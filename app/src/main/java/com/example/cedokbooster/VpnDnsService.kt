package com.example.cedokbooster

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.Context
import android.content.Intent
import android.net.VpnService
import android.os.*
import androidx.core.app.NotificationCompat
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import kotlinx.coroutines.withTimeout
import kotlinx.coroutines.delay
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.TimeUnit

class VpnDnsService : VpnService() {
    
    companion object {
        private const val TAG = "VpnDnsService"
        private const val NOTIFICATION_ID = 999
        private const val CHANNEL_ID = "vpn_dns_channel"
        private val PORT_STRATEGY = listOf(5353, 5354, 5355, 9999, 53535, 53536, 53537, 53538)
        private const val VPN_ADDRESS = "100.64.0.2"
        private const val VPN_PREFIX_LENGTH = 24
        
        // Actions
        private const val ACTION_START_VPN = "com.example.cedokbooster.START_VPN"
        private const val ACTION_STOP_VPN = "com.example.cedokbooster.STOP_VPN"
        private const val ACTION_SOFT_RESTART = "com.example.cedokbooster.SOFT_RESTART_VPN"
        const val FORCE_CLOSE_VPN = "com.example.cedokbooster.FORCE_CLOSE_VPN"
        const val EXTRA_DNS_TYPE = "dns_type"

        // Restart limits
        private const val MAX_RESTARTS_PER_MINUTE = 3
        
        private var isRunning = AtomicBoolean(false)
        private var currentDns = "1.0.0.1"
        
        fun startVpn(context: Context, dnsType: String = "A") {
            val intent = Intent(context, VpnDnsService::class.java).apply {
                action = ACTION_START_VPN
                putExtra(EXTRA_DNS_TYPE, dnsType)
            }
            context.startService(intent)
        }
        
        fun startVpn(context: Context) {
            startVpn(context, "A")
        }
        
        fun stopVpn(context: Context) {
            val intent = Intent(context, VpnDnsService::class.java).apply {
                action = ACTION_STOP_VPN
            }
            context.startService(intent)
        }
        
        fun softRestartVpn(context: Context) {
            val intent = Intent(context, VpnDnsService::class.java).apply {
                action = ACTION_SOFT_RESTART
            }
            context.startService(intent)
        }
        
        fun isVpnRunning(): Boolean = isRunning.get()
        fun getCurrentDns(): String = currentDns
    }
    
    // State
    private var vpnInterface: ParcelFileDescriptor? = null
    private var dnsProxyThread: Thread? = null
    private var dnsProxySocket: DatagramSocket? = null
    private val executor: ExecutorService = Executors.newFixedThreadPool(4)
    private val coroutineScope = CoroutineScope(Dispatchers.IO)
    private var currentDnsType = "A"
    private var startIntent: Intent? = null // 👈 SIMPAN INTENT REFERENCE
    
    // Restart stability
    private val isRestarting = AtomicBoolean(false)
    private val restartCount = AtomicInteger(0)
    private val handler = Handler(Looper.getMainLooper())
    
    /**
     * Dapatkan DNS type optimal secara auto
     */
    private fun getOptimalDnsType(): String {
        return try {
            // Check DNS mana paling bagus untuk Panda
            val bestDns = DnsQualityChecker.selectBestDnsForPanda()
            
            // Map ke DNS type berdasarkan server terpilih
            when {
                bestDns.startsWith("1.1.1.1") || bestDns.startsWith("1.0.0.1") -> {
                    LogUtil.d(TAG, "✅ Selected Cloudflare DNS ($bestDns)")
                    "A" // Cloudflare group
                }
                bestDns.startsWith("8.8.") -> {
                    LogUtil.d(TAG, "✅ Selected Google DNS ($bestDns)")
                    "B" // Google group
                }
                else -> {
                    LogUtil.d(TAG, "✅ Selected Other DNS ($bestDns)")
                    "C" // Other group
                }
            }
        } catch (e: Exception) {
            LogUtil.e(TAG, "DNS selection error, using default: ${e.message}")
            "A" // Fallback ke Cloudflare
        }
    }
    
    /**
     * GET DNS SERVERS dengan auto-selection
     * MODIFY FUNCTION YANG SUDAH ADA:
     */
    private fun getDnsServers(type: String): List<String> {
        // Jika type = "auto", pilih optimal
        val effectiveType = if (type == "auto") getOptimalDnsType() else type
        
        return when (effectiveType.uppercase()) {
            "A" -> listOf("1.1.1.1", "1.0.0.1", "2606:4700:4700::1111", "2606:4700:4700::1001")
            "B" -> listOf("8.8.8.8", "8.8.4.4", "2001:4860:4860::8888", "2001:4860:4860::8844")
            else -> listOf("9.9.9.9", "149.112.112.112", "2620:fe::fe", "2620:fe::9")
        }.also {
            currentDns = it.first()
            LogUtil.d(TAG, "Using DNS servers: $it (Type: $effectiveType)")
        }
    }
    
    /**
     * SETUP DNS-ONLY VPN
     */
    private fun setupDnsOnlyVpn(dnsType: String): Boolean {
        return try {
            currentDnsType = if (dnsType == "auto") getOptimalDnsType() else dnsType
           
            val dnsServers = getDnsServers(currentDnsType)
            
            val builder = Builder()
                .setSession("CedokDNS-$dnsType")
                .addAddress(VPN_ADDRESS, VPN_PREFIX_LENGTH)
                .setMtu(1280)
                .setBlocking(true)
            
            // System apps boleh bypass DNS kita
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                try {
                    builder.addDisallowedApplication("com.android.systemui")
                    builder.addDisallowedApplication("com.android.settings")
                    builder.addDisallowedApplication("com.android.dialer")
                    LogUtil.d(TAG, "✅ System apps disallowed")
                } catch (e: Exception) {
                    LogUtil.w(TAG, "⚠️ Cannot disallow system apps: ${e.message}")
                }
            }
            
            // Set DNS servers
            dnsServers.take(2).forEach { dns ->
                builder.addDnsServer(dns)
            }
            
            // Route ke DNS servers
            dnsServers.take(2).forEach { dns ->
                if (dns.contains('.')) {
                    builder.addRoute(dns, 32)
                }
            }
            
            // Route ke Telco DNS
            builder.addRoute("203.82.91.14", 32)
            builder.addRoute("203.82.91.30", 32)
            
            // Route ke popular services
            builder.addRoute("142.250.0.0", 16)
            builder.addRoute("13.0.0.0", 8)
            builder.addRoute("34.0.0.0", 8)
            
            // Establish VPN
            val fd = builder.establish()
            if (fd != null) {
                vpnInterface = fd
                LogUtil.d(TAG, "✅ VPN established dengan DNS: ${dnsServers.first()}")
                
                // Start DNS proxy
                coroutineScope.launch {
                    startDnsProxy(dnsServers)
                }
                
                return true
            }
            
            LogUtil.e(TAG, "❌ VPN establishment failed")
            false
            
        } catch (e: Exception) {
            LogUtil.e(TAG, "💥 VPN setup error: ${e.message}")
            false
        }
    }
    
    /**
     * DNS PROXY dengan STABILITY IMPROVEMENTS
     */
    private fun startDnsProxy(dnsServers: List<String>) {
        // Check jika sedang restart
        if (isRestarting.get()) {
            LogUtil.w(TAG, "⚠️ Skipping DNS start - restart in progress")
            return
        }
        
        LogUtil.d(TAG, "Starting DNS proxy dengan servers: $dnsServers")
        
        try {
            // Graceful cleanup sebelum start baru
            dnsProxyThread?.let { thread ->
                if (thread.isAlive) {
                    thread.interrupt()
                    try {
                        thread.join(500)
                    } catch (e: Exception) {
                        LogUtil.w(TAG, "Thread join interrupted")
                    }
                }
            }
            
            dnsProxySocket?.close()
            
            Thread.sleep(100) // Small delay untuk cleanup
            
            var socket: DatagramSocket? = null
            var selectedPort = -1
            
            // Cuba setiap port dalam strategy
            for (port in PORT_STRATEGY) {
                try {
                    // Try release port
                    try {
                        Runtime.getRuntime().exec(arrayOf(
                            "sh", "-c", 
                            "fuser -k $port/udp 2>/dev/null || true; " +
                            "killall mdnsd 2>/dev/null || true"
                        ))
                        Thread.sleep(50)
                    } catch (e: Exception) {
                        // Ignore untuk non-root
                    }
                    
                    // Cuba bind ke port
                    socket = DatagramSocket(null).apply {
                        reuseAddress = true
                        soTimeout = 0  // 🔥 NO TIMEOUT - BLOCK FOREVER
                        bind(java.net.InetSocketAddress(port))
                    }
                    
                    selectedPort = port
                    LogUtil.d(TAG, "✅ Acquired port $port")
                    break
                    
                } catch (e: java.net.SocketException) {
                    if (e.message?.contains("EADDRINUSE") == true || 
                        e.message?.contains("Address already in use") == true) {
                        LogUtil.w(TAG, "🚨 Port $port occupied, trying next...")
                        socket?.close()
                        continue
                    } else {
                        throw e
                    }
                }
            }
            
            if (selectedPort == -1) {
                LogUtil.e(TAG, "💥 All ports blocked!")
                return
            }
            
            dnsProxySocket = socket
            
            // Start proxy thread dengan STABILITY FIXES
            dnsProxyThread = Thread {
                LogUtil.d(TAG, "🔁 DNS Proxy thread STARTED on port $selectedPort")
                
                try {
                    while (!Thread.currentThread().isInterrupted && isRunning.get()) {
                        try {
                            // Receive DNS query - BLOCK FOREVER (soTimeout = 0)
                            val buffer = ByteArray(512)
                            val packet = DatagramPacket(buffer, buffer.size)
                            dnsProxySocket!!.receive(packet)
                            
                            // Process query
                            executor.submit {
                                handleDnsQuery(packet, dnsServers)
                            }
                            
                        } catch (e: java.net.SocketTimeoutException) {
                            // Tidak akan terjadi kerana soTimeout = 0
                            continue
                        } catch (e: Exception) {
                            if (isRunning.get() && !Thread.currentThread().isInterrupted) {
                                LogUtil.w(TAG, "DNS Proxy error: ${e.message}")
                                // Continue loop - jangan crash
                            }
                        }
                    }
                } finally {
                    LogUtil.d(TAG, "🔴 DNS Proxy thread EXITING. " +
                                  "Interrupted: ${Thread.currentThread().isInterrupted}, " +
                                  "isRunning: ${isRunning.get()}")
                }
            }
            
            dnsProxyThread!!.priority = Thread.MAX_PRIORITY
            dnsProxyThread!!.name = "DNS-Proxy-$selectedPort"
            dnsProxyThread!!.start()
            
            LogUtil.d(TAG, "✅ DNS Proxy started successfully")
            
        } catch (e: Exception) {
            LogUtil.e(TAG, "💥 Failed to start DNS proxy: ${e.message}")
            
            // Retry dengan exponential backoff
            coroutineScope.launch {
                delay(3000) // 👈 FIXED: guna delay() bukan kotlinx.coroutines.delay()
                if (isRunning.get() && !isRestarting.get()) {
                    LogUtil.d(TAG, "🔄 Retrying DNS proxy...")
                    startDnsProxy(dnsServers)
                }
            }
        }
    }
    
    /**
     * HANDLE DNS QUERY
     */
    private fun handleDnsQuery(queryPacket: DatagramPacket, dnsServers: List<String>) {
        var socket: DatagramSocket? = null
        
        try {
            val clientIp = queryPacket.address.hostAddress
            val clientPort = queryPacket.port
            val queryData = queryPacket.data.copyOf(queryPacket.length)
            
            // Decode DNS ID
            val queryId = if (queryData.size >= 2) {
                ((queryData[0].toInt() and 0xFF) shl 8) or (queryData[1].toInt() and 0xFF)
            } else 0
            
            LogUtil.d(TAG, "📡 DNS Query #$queryId from $clientIp:$clientPort")
            
            // Gunakan protect() untuk elak loop
            val dnsSocket = DatagramSocket()
            protect(dnsSocket)
            
            // Cuba semua DNS servers
            var success = false
            val filteredServers = dnsServers.filter { it.contains('.') }
            
            for (dnsServer in filteredServers) {
                try {
                    val forwardPacket = DatagramPacket(
                        queryData,
                        queryData.size,
                        InetAddress.getByName(dnsServer),
                        53
                    )
                    
                    dnsSocket.soTimeout = 3000
                    dnsSocket.send(forwardPacket)
                    
                    val responseBuffer = ByteArray(512)
                    val responsePacket = DatagramPacket(responseBuffer, responseBuffer.size)
                    dnsSocket.receive(responsePacket)
                    
                    val replyPacket = DatagramPacket(
                        responsePacket.data,
                        responsePacket.length,
                        queryPacket.address,
                        queryPacket.port
                    )
                    
                    dnsProxySocket!!.send(replyPacket)
                    
                    success = true
                    LogUtil.d(TAG, "✅ DNS resolved via $dnsServer for #$queryId")
                    break
                    
                } catch (e: java.net.SocketTimeoutException) {
                    LogUtil.w(TAG, "⚠️ $dnsServer timeout")
                    continue
                } catch (e: Exception) {
                    LogUtil.w(TAG, "❌ $dnsServer failed: ${e.message}")
                    continue
                }
            }
            
            if (!success) {
                tryFallbackDns(queryPacket, dnsSocket)
            }
            
            dnsSocket.close()
            
        } catch (e: Exception) {
            LogUtil.e(TAG, "💥 DNS handling error: ${e.message}")
        } finally {
            socket?.close()
        }
    }
    
    /**
     * FALLBACK DNS
     */
    private fun tryFallbackDns(queryPacket: DatagramPacket, dnsSocket: DatagramSocket) {
        val fallbackServers = listOf("1.1.1.1", "8.8.8.8", "9.9.9.9")
        val queryData = queryPacket.data.copyOf(queryPacket.length)
        
        for (dns in fallbackServers) {
            try {
                val forwardPacket = DatagramPacket(
                    queryData,
                    queryData.size,
                    InetAddress.getByName(dns),
                    53
                )
                
                dnsSocket.soTimeout = 3000
                dnsSocket.send(forwardPacket)
                
                val responseBuffer = ByteArray(512)
                val responsePacket = DatagramPacket(responseBuffer, responseBuffer.size)
                dnsSocket.receive(responsePacket)
                
                val replyPacket = DatagramPacket(
                    responsePacket.data,
                    responsePacket.length,
                    queryPacket.address,
                    queryPacket.port
                )
                
                dnsProxySocket!!.send(replyPacket)
                LogUtil.d(TAG, "✅ Fallback DNS via $dns succeeded")
                return
                
            } catch (e: Exception) {
                continue
            }
        }
        
        LogUtil.e(TAG, "💥 All DNS servers failed")
    }
    
    /**
     * SOFT RESTART - Untuk DAJ sequence
     */
    private fun performSoftRestart() {
        if (isRestarting.get()) {
            LogUtil.d(TAG, "⚠️ Restart already in progress, skipping...")
            return
        }
        
        val currentCount = restartCount.getAndIncrement()
        if (currentCount >= MAX_RESTARTS_PER_MINUTE) {
            LogUtil.w(TAG, "🚨 Max restarts per minute reached ($MAX_RESTARTS_PER_MINUTE)")
            restartCount.decrementAndGet()
            return
        }
        
        isRestarting.set(true)
        
        LogUtil.d(TAG, "🔄 Performing SOFT RESTART #${currentCount + 1}")
        
        coroutineScope.launch {
            try {
                // PHASE 1: Check jika VPN masih running
                if (!isRunning.get() || vpnInterface == null) {
                    LogUtil.w(TAG, "⚠️ VPN not running, attempting recovery...")
                    
                    // AUTO-RECOVERY: Start VPN semula
                    delay(1000)
                    startVpnService()
                    return@launch
                }
                
                // PHASE 2: Graceful shutdown DNS proxy
                dnsProxyThread?.let { thread ->
                    if (thread.isAlive) {
                        thread.interrupt()
                        withTimeout(2000) {
                            try {
                                thread.join()
                            } catch (e: Exception) {
                                LogUtil.w(TAG, "Thread join timeout")
                            }
                        }
                    }
                }
                
                // PHASE 3: Close socket
                dnsProxySocket?.close()
                dnsProxySocket = null
                dnsProxyThread = null
                
                // PHASE 4: Small delay
                delay(500)
                
                // PHASE 5: Restart DNS proxy
                val dnsServers = getDnsServers(currentDnsType)
                startDnsProxy(dnsServers)
                updateNotification("Soft-restarted")
                LogUtil.d(TAG, "✅ DNS Proxy soft-restarted successfully")
                
            } catch (e: Exception) {
                LogUtil.e(TAG, "💥 Soft restart failed: ${e.message}")
                
                // Emergency recovery
                if (isRunning.get()) {
                    delay(2000)
                    try {
                        val dnsServers = getDnsServers(currentDnsType)
                        startDnsProxy(dnsServers)
                    } catch (e2: Exception) {
                        LogUtil.e(TAG, "💥 Emergency recovery failed")
                    }
                }
                
            } finally {
                isRestarting.set(false)
                
                // Reset restart counter after 1 minute
                handler.postDelayed({
                    restartCount.set(0)
                    LogUtil.d(TAG, "🔄 Restart counter reset")
                }, 60000)
            }
        }
    }
    
    /**
     * UPDATE NOTIFICATION
     */
    private fun updateNotification(status: String) {
        val notificationManager = getSystemService(Context.NOTIFICATION_SERVICE) 
            as NotificationManager
        
        val notification = NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle("🛡️ CedokDNS ($status)")
            .setContentText("DNS: $currentDns | Restarts: ${restartCount.get()}")
            .setSmallIcon(android.R.drawable.ic_lock_lock)
            .setOngoing(true)
            .setOnlyAlertOnce(true)
            .setPriority(NotificationCompat.PRIORITY_LOW)
            .build()
        
        notificationManager.notify(NOTIFICATION_ID, notification)
    }
    
    /**
     * SHOW NOTIFICATION
     */
    private fun showNotification() {
        val notificationManager = getSystemService(Context.NOTIFICATION_SERVICE) 
            as NotificationManager
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val channel = NotificationChannel(
                CHANNEL_ID,
                "DNS Protection",
                NotificationManager.IMPORTANCE_LOW
            ).apply {
                description = "DNS protection is active"
                setShowBadge(false)
            }
            notificationManager.createNotificationChannel(channel)
        }
        
        val intent = Intent(this, MainActivity::class.java).apply {
            flags = Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_CLEAR_TASK
        }
        
        val pendingIntent = PendingIntent.getActivity(
            this, 0, intent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )
        
        val stopIntent = Intent(this, VpnDnsService::class.java).apply {
            action = ACTION_STOP_VPN
        }
        val stopPendingIntent = PendingIntent.getService(
            this, 1, stopIntent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )
        
        val notification = NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle("🛡️ CedokDNS Active")
            .setContentText("DNS: $currentDns | Type: $currentDnsType")
            .setSmallIcon(android.R.drawable.ic_lock_lock)
            .setContentIntent(pendingIntent)
            .setPriority(NotificationCompat.PRIORITY_LOW)
            .setOngoing(true)
            .setOnlyAlertOnce(true)
            .setCategory(NotificationCompat.CATEGORY_SERVICE)
            .addAction(
                android.R.drawable.ic_menu_close_clear_cancel,
                "Stop",
                stopPendingIntent
            )
            .setAutoCancel(false)
            .build()
        
        startForeground(NOTIFICATION_ID, notification)
        LogUtil.d(TAG, "✅ Notification shown")
    }
    
    /**
     * START VPN SERVICE
     */
    private fun startVpnService() {
        if (isRunning.get()) {
            LogUtil.d(TAG, "VPN already running")
            return
        }
        
        LogUtil.d(TAG, "Starting VPN service...")
        
        val prepareIntent = VpnService.prepare(this)
        if (prepareIntent != null) {
            LogUtil.e(TAG, "VPN permission not granted")
            stopSelf()
            return
        }
        
        // 👈 FIXED: Guna startIntent yang disimpan
        val dnsType = startIntent?.getStringExtra(EXTRA_DNS_TYPE) ?: "A"
        
        val success = setupDnsOnlyVpn(dnsType)
        if (success) {
            isRunning.set(true)
            showNotification()
            
            sendBroadcast(Intent("DNS_VPN_STATUS").apply {
                putExtra("status", "ACTIVE")
                putExtra("dns_type", dnsType)
                putExtra("current_dns", currentDns)
            })
            
            LogUtil.d(TAG, "✅ VPN started dengan DNS type: $dnsType")
        } else {
            LogUtil.e(TAG, "❌ Failed to start VPN")
            stopSelf()
        }
    }
    
    private fun stopVpnService() {
        if (!isRunning.get()) {
            LogUtil.d(TAG, "VPN already stopped")
            stopSelf() // 🟢 TAMBAH: Pasti stop service
            return
        }
        
        LogUtil.d(TAG, "Stopping VPN service...")
        
        isRunning.set(false)
        isRestarting.set(false)
        
        // 1. Interrupt thread dan TUNGGU sampai mati
        dnsProxyThread?.let { thread ->
            if (thread.isAlive) {
                thread.interrupt()
                var waited = 0
                while (thread.isAlive && waited < 2000) { // Tunggu sampai 2s
                    try {
                        Thread.sleep(100)
                        waited += 100
                    } catch (e: InterruptedException) { break }
                }
                if (thread.isAlive) {
                    LogUtil.w(TAG, "Thread still alive, forcing...")
                }
            }
        }
        
        // 2. Close socket dengan confirm
        dnsProxySocket?.close()
        dnsProxySocket = null
        
        // 3. Shutdown executor dan TUNGGU
        executor.shutdown()
        try {
            if (!executor.awaitTermination(2, TimeUnit.SECONDS)) {
                executor.shutdownNow()
            }
        } catch (e: InterruptedException) {
            executor.shutdownNow()
        }
        
        // 4. Close VPN interface
        vpnInterface?.close()
        vpnInterface = null
        
        // 5. Stop foreground
        stopForeground(true)
        
        // 6. Broadcast
        sendBroadcast(Intent("DNS_VPN_STATUS").apply {
            putExtra("status", "STOPPED")
            putExtra("dns_type", currentDnsType)
        })
        
        LogUtil.d(TAG, "✅ VPN stopped COMPLETELY")
        
        // 7. 🟢 PASTI stop service
        stopSelf()
    }
    
    /**
     * SERVICE LIFECYCLE
     */
    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        // 👈 SIMPAN INTENT untuk digunakan kemudian
        startIntent = intent
        
        when (intent?.action) {
            ACTION_START_VPN -> startVpnService()
            ACTION_STOP_VPN -> stopVpnService()
            ACTION_SOFT_RESTART -> performSoftRestart()
            else -> stopSelf()
        }
        return START_STICKY
    }
    
    override fun onDestroy() {
        LogUtil.d(TAG, "Service destroying")
        stopVpnService()
        super.onDestroy()
    }
    
    override fun onBind(intent: Intent?): IBinder? = null
    
    override fun onRevoke() {
        LogUtil.d(TAG, "VPN revoked by system")
        stopVpnService()
    }
    
    /**
     * LOGGING UTILITY
     */
    private object LogUtil {
        fun d(tag: String, message: String) = android.util.Log.d(tag, message)
        fun e(tag: String, message: String) = android.util.Log.e(tag, message)
        fun w(tag: String, message: String) = android.util.Log.w(tag, message)
    }
}
