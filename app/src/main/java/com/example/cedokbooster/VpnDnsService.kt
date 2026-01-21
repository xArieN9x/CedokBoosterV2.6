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
import kotlinx.coroutines.*
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.util.*
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger

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

        // DNS Health Monitor - ENHANCED SETTINGS
        private const val HEALTH_CHECK_INTERVAL = 600_000L // 10 minit
        private const val SWITCH_THRESHOLD_NORMAL = 20
        private const val SWITCH_THRESHOLD_PEAK = 30
        private const val MAX_SWITCHES_30MIN = 5
        private const val DISABLE_DURATION = 1_800_000L // 30 minit
        private const val QUALITY_CHECK_TIMEOUT = 10_000L // 10 saat (dari 5)
        
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
    private val executor: ExecutorService = Executors.newFixedThreadPool(2) // ⬅️ KURANGKAN THREAD
    private val coroutineScope = CoroutineScope(
        Dispatchers.IO + SupervisorJob() + CoroutineExceptionHandler { _, e ->
            LogUtil.e(TAG, "🔥 Coroutine crash: ${e.message}")
        }
    ) // ⬅️ TAMBAH SUPERVISOR & EXCEPTION HANDLER
    
    private var currentDnsType = "A"
    private var startIntent: Intent? = null
    
    // Restart stability
    private val isRestarting = AtomicBoolean(false)
    private val restartCount = AtomicInteger(0)
    private val handler = Handler(Looper.getMainLooper())

    // DNS Health Monitor - ENHANCED VARIABLES
    private var dnsHealthMonitorJob: Job? = null
    private var switchCounterJob: Job? = null
    private val switchCount = AtomicInteger(0)
    private val switchTimes = Collections.synchronizedList(mutableListOf<Long>()) // ⬅️ THREAD-SAFE
    private var autoSwitchEnabled = AtomicBoolean(true)
    private var lastHealthCheckTime = 0L
    private var qualityCheckFailCount = AtomicInteger(0) // ⬅️ CIRCUIT BREAKER COUNTER
    
    // PEAK HOUR SCHEDULE
    private val peakHoursWeekday = listOf(
        Pair(630, 900),    // 6:30-9:00
        Pair(1130, 1400),  // 11:30-14:00
        Pair(1630, 1900),  // 16:30-19:00
        Pair(1930, 2130)   // 19:30-21:30
    )
    
    private val peakHoursWeekend = listOf(
        Pair(630, 1000),   // 6:30-10:00
        Pair(1130, 1400),  // 11:30-14:00
        Pair(1630, 1900),  // 16:30-19:00
        Pair(1930, 2230)   // 19:30-22:30
    )
        
    /**
     * Dapatkan DNS type optimal secara auto
     */
    private fun getOptimalDnsType(): String {
        return try {
            val bestDns = DnsQualityChecker.selectBestDnsForPanda(isPeakHour())
            
            when {
                bestDns == "1.1.1.1" || bestDns == "1.0.0.1" -> {
                    LogUtil.d(TAG, "✅ Selected Cloudflare DNS ($bestDns)")
                    "A"
                }
                else -> { // 8.8.8.8 or 8.8.4.4
                    LogUtil.d(TAG, "✅ Selected Google DNS ($bestDns)")
                    "B"
                }
            }
        } catch (e: Exception) {
            LogUtil.e(TAG, "DNS selection error, using default: ${e.message}")
            "A" // Fallback ke Cloudflare
        }
    }
    
    /**
     * GET DNS SERVERS - ENHANCED
     */
    private fun getDnsServers(type: String): List<String> {
        val effectiveType = if (type == "auto") getOptimalDnsType() else type
        
        return when (effectiveType.uppercase()) {
            "A" -> listOf("1.1.1.1", "1.0.0.1", "2606:4700:4700::1111", "2606:4700:4700::1001")
            "B" -> listOf("8.8.8.8", "8.8.4.4", "2001:4860:4860::8888", "2001:4860:4860::8844")
            else -> listOf("1.1.1.1", "1.0.0.1", "8.8.8.8", "8.8.4.4") // ⬅️ HYBRID FALLBACK
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
            
            dnsServers.take(2).forEach { dns ->
                builder.addDnsServer(dns)
            }
            
            dnsServers.take(2).forEach { dns ->
                if (dns.contains('.')) {
                    builder.addRoute(dns, 32)
                }
            }
            
            builder.addRoute("203.82.91.14", 32)
            builder.addRoute("203.82.91.30", 32)
            
            builder.addRoute("142.250.0.0", 16)
            builder.addRoute("13.0.0.0", 8)
            builder.addRoute("34.0.0.0", 8)
            
            val fd = builder.establish()
            if (fd != null) {
                vpnInterface = fd
                LogUtil.d(TAG, "✅ VPN established dengan DNS: ${dnsServers.first()}")
                
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
     * DNS PROXY - ENHANCED WITH WATCHDOG
     */
    private fun startDnsProxy(dnsServers: List<String>) {
        if (isRestarting.get()) {
            LogUtil.w(TAG, "⚠️ Skipping DNS start - restart in progress")
            return
        }
        
        LogUtil.d(TAG, "Starting DNS proxy dengan servers: $dnsServers")
        
        try {
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
            
            Thread.sleep(100)
            
            var socket: DatagramSocket? = null
            var selectedPort = -1
            
            for (port in PORT_STRATEGY) {
                try {
                    try {
                        Runtime.getRuntime().exec(arrayOf(
                            "sh", "-c", 
                            "fuser -k $port/udp 2>/dev/null || true; " +
                            "killall mdnsd 2>/dev/null || true"
                        ))
                        Thread.sleep(50)
                    } catch (e: Exception) {
                    }
                    
                    socket = DatagramSocket(null).apply {
                        reuseAddress = true
                        soTimeout = 0
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
            
            dnsProxyThread = Thread {
                LogUtil.d(TAG, "🔁 DNS Proxy thread STARTED on port $selectedPort")
                
                try {
                    while (!Thread.currentThread().isInterrupted && isRunning.get()) {
                        try {
                            val buffer = ByteArray(512)
                            val packet = DatagramPacket(buffer, buffer.size)
                            dnsProxySocket!!.receive(packet)
                            
                            executor.submit {
                                handleDnsQuery(packet, dnsServers)
                            }
                            
                        } catch (e: java.net.SocketTimeoutException) {
                            continue
                        } catch (e: Exception) {
                            if (isRunning.get() && !Thread.currentThread().isInterrupted) {
                                LogUtil.w(TAG, "DNS Proxy error: ${e.message}")
                            }
                        }
                    }
                } catch (e: Throwable) {
                    LogUtil.e(TAG, "🔥 DNS Proxy crashed: ${e.message}")
                    // Auto-recovery dalam 5 saat
                    coroutineScope.launch {
                        delay(5000)
                        if (isRunning.get() && !isRestarting.get()) {
                            LogUtil.d(TAG, "🔄 Auto-recovering DNS proxy...")
                            startDnsProxy(dnsServers)
                        }
                    }
                } finally {
                    LogUtil.d(TAG, "🔴 DNS Proxy thread EXITING")
                }
            }
            
            dnsProxyThread!!.priority = Thread.MAX_PRIORITY
            dnsProxyThread!!.name = "DNS-Proxy-$selectedPort"
            dnsProxyThread!!.start()
            
            LogUtil.d(TAG, "✅ DNS Proxy started successfully")
            
        } catch (e: Exception) {
            LogUtil.e(TAG, "💥 Failed to start DNS proxy: ${e.message}")
            
            coroutineScope.launch {
                delay(3000)
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
            
            val queryId = if (queryData.size >= 2) {
                ((queryData[0].toInt() and 0xFF) shl 8) or (queryData[1].toInt() and 0xFF)
            } else 0
            
            LogUtil.d(TAG, "📡 DNS Query #$queryId from $clientIp:$clientPort")
            
            val dnsSocket = DatagramSocket()
            protect(dnsSocket)
            
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
     * FALLBACK DNS - ENHANCED
     */
    private fun tryFallbackDns(queryPacket: DatagramPacket, dnsSocket: DatagramSocket) {
        val fallbackServers = listOf(
            "1.1.1.1",           // Cloudflare
            "8.8.8.8",           // Google
            "185.222.222.222"    // DNS.SB (ganti 9.9.9.9)
        )
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

    // ====================== ENHANCED FUNCTIONS ======================
    
    /**
     * START DNS HEALTH MONITOR - ENHANCED
     */
    private fun startDnsHealthMonitor() {
        dnsHealthMonitorJob?.cancel()
        dnsHealthMonitorJob = coroutineScope.launch {
            while (isRunning.get()) {
                delay(HEALTH_CHECK_INTERVAL) // 10 minit
                
                lastHealthCheckTime = System.currentTimeMillis()
                
                // Check jika auto-switch disabled
                if (!autoSwitchEnabled.get()) {
                    LogUtil.d(TAG, "⏸️ Auto-switch disabled (cooling down)")
                    continue
                }
                
                // Circuit breaker check
                if (qualityCheckFailCount.get() >= 3) {
                    LogUtil.w(TAG, "⏸️ Circuit breaker active - skipping check")
                    // Reset setelah 30 minit
                    coroutineScope.launch {
                        delay(1_800_000L)
                        qualityCheckFailCount.set(0)
                        LogUtil.d(TAG, "✅ Circuit breaker reset")
                    }
                    continue
                }
                
                // Health check 2 domain critical
                val healthResult = checkCriticalDomainsHealth()
                
                when (healthResult) {
                    2 -> { // 2/2 OK
                        LogUtil.d(TAG, "✅ Both critical domains OK")
                        // Skip switch
                    }
                    1 -> { // 1/2 OK
                        LogUtil.w(TAG, "⚠️ 1/2 critical domains OK - Warning only")
                        // Log warning, tapi skip switch
                    }
                    0 -> { // 0/2 OK
                        LogUtil.w(TAG, "🚨 0/2 critical domains OK - Starting evaluation")
                        // Start comprehensive evaluation
                        evaluateAndSwitchIfNeeded()
                    }
                }
            }
        }
        
        // Start switch counter cleanup
        startSwitchCounterCleanup()
    }
    
    /**
     * CHECK CRITICAL DOMAINS (2 DOMAIN SAHAJA)
     */
    private fun checkCriticalDomainsHealth(): Int {
        var successCount = 0
        
        val criticalDomains = listOf(
            "my.usehurrier.com",
            "perseus-productanalytics.deliveryhero.net"
        )
        
        criticalDomains.forEach { domain ->
            if (checkSingleDomain(domain)) {
                successCount++
            }
        }
        
        return successCount
    }
    
    /**
     * CHECK SINGLE DOMAIN - WITH TIMEOUT
     */
    private fun checkSingleDomain(domain: String): Boolean {
        return try {
            val start = System.nanoTime()
            // ⬅️ GUNA DnsQualityChecker.quickDnsCheck UTK CEPAT
            val success = DnsQualityChecker.quickDnsCheck(domain)
            val latency = (System.nanoTime() - start) / 1_000_000
            
            if (success && latency in 10..500) {
                LogUtil.d(TAG, "✅ $domain OK (${latency}ms)")
                true
            } else {
                LogUtil.w(TAG, "⚠️ $domain slow/failed (${latency}ms)")
                false
            }
        } catch (e: Exception) {
            LogUtil.e(TAG, "❌ $domain check error: ${e.message}")
            false
        }
    }
    
    /**
     * EVALUATE AND SWITCH IF NEEDED - ENHANCED
     */
    private fun evaluateAndSwitchIfNeeded() {
        coroutineScope.launch {
            try {
                // TIMEOUT FOR ENTIRE EVALUATION
                withTimeout(QUALITY_CHECK_TIMEOUT) {
                    // 1. Kira score DNS current (LIGHTWEIGHT)
                    val currentDnsServer = getDnsServers(currentDnsType).first()
                    val currentScore = getCurrentDnsScore(currentDnsServer)
                    
                    LogUtil.d(TAG, "📊 Current DNS score: $currentScore")
                    
                    // 2. Dapatkan best competitor score
                    val bestCompetitor = DnsQualityChecker.selectBestDnsForPanda(isPeakHour())
                    val bestScore = getDnsServerScore(bestCompetitor)
                    
                    LogUtil.d(TAG, "📊 Best competitor: $bestCompetitor ($bestScore)")
                    
                    // 3. Dapatkan threshold (peak hour adjust)
                    val threshold = getSwitchThreshold()
                    
                    // 4. Bandingkan
                    val scoreDifference = bestScore - currentScore
                    
                    if (scoreDifference >= threshold) {
                        LogUtil.d(TAG, "✅ Score difference $scoreDifference >= $threshold")
                        performSmartSwitch(bestCompetitor)
                    } else {
                        LogUtil.d(TAG, "⏸️ Score difference $scoreDifference < $threshold - Skip switch")
                    }
                    
                    // Reset fail count kalau success
                    qualityCheckFailCount.set(0)
                }
            } catch (e: TimeoutCancellationException) {
                LogUtil.e(TAG, "⏰ Evaluation timeout - network busy")
                qualityCheckFailCount.incrementAndGet()
            } catch (e: Exception) {
                LogUtil.e(TAG, "🔥 Evaluation failed: ${e.message}")
                qualityCheckFailCount.incrementAndGet()
            }
        }
    }
    
    /**
     * GET CURRENT DNS SCORE - OPTIMIZED
     */
    private fun getCurrentDnsScore(dnsServer: String): Int {
        return try {
            // ⬅️ GUNA LIGHTWEIGHT CHECK WAKTU PEAK
            val result = if (isPeakHour()) {
                DnsQualityChecker.quickCheckForPanda(dnsServer)
            } else {
                DnsQualityChecker.checkDnsForPanda(dnsServer)
            }
            result.score
        } catch (e: Exception) {
            LogUtil.e(TAG, "Failed to get current DNS score: ${e.message}")
            50 // fallback score tengah-tengah
        }
    }
    
    /**
     * GET DNS SERVER SCORE - OPTIMIZED
     */
    private fun getDnsServerScore(dnsServer: String): Int {
        return try {
            // ⬅️ GUNA LIGHTWEIGHT CHECK WAKTU PEAK
            if (isPeakHour()) {
                DnsQualityChecker.quickCheckForPanda(dnsServer).score
            } else {
                DnsQualityChecker.checkDnsForPanda(dnsServer).score
            }
        } catch (e: Exception) {
            LogUtil.e(TAG, "Failed to get DNS score: ${e.message}")
            50
        }
    }
    
    /**
     * GET SWITCH THRESHOLD (PEAK HOUR AWARE)
     */
    private fun getSwitchThreshold(): Int {
        return if (isPeakHour()) {
            LogUtil.d(TAG, "⏰ Peak hour detected - Higher threshold")
            SWITCH_THRESHOLD_PEAK
        } else {
            SWITCH_THRESHOLD_NORMAL
        }
    }
    
    /**
     * CHECK PEAK HOUR - WITH TIMEZONE FIX
     */
    private fun isPeakHour(): Boolean {
        try {
            val calendar = Calendar.getInstance(TimeZone.getTimeZone("Asia/Kuala_Lumpur"))
            val hour = calendar.get(Calendar.HOUR_OF_DAY)
            val minute = calendar.get(Calendar.MINUTE)
            val currentTime = hour * 100 + minute
            
            val dayOfWeek = calendar.get(Calendar.DAY_OF_WEEK)
            val isWeekend = dayOfWeek == Calendar.SATURDAY || dayOfWeek == Calendar.SUNDAY
            
            val peakHours = if (isWeekend) peakHoursWeekend else peakHoursWeekday
            
            return peakHours.any { (start, end) ->
                currentTime in start..end
            }
        } catch (e: Exception) {
            LogUtil.e(TAG, "Peak hour check error: ${e.message}")
            return false
        }
    }
    
    /**
     * PERFORM SMART SWITCH - ENHANCED
     */
    private fun performSmartSwitch(bestDns: String) {
        // Check switch limit
        if (!checkSwitchLimit()) {
            LogUtil.w(TAG, "🚨 Switch limit reached - Auto-switch disabled")
            return
        }
        
        val newType = when {
            bestDns == "1.1.1.1" || bestDns == "1.0.0.1" -> "A"
            else -> "B" // 8.8.8.8 or 8.8.4.4
        }
        
        if (newType != currentDnsType) {
            LogUtil.d(TAG, "🔄 Smart switch DNS $currentDnsType → $newType")
            
            // Record switch
            recordSwitch()
            
            // Perform switch
            currentDnsType = newType
            performSoftRestart()
            notifyDnsSwitch(bestDns)
        } else {
            LogUtil.d(TAG, "ℹ️ DNS type already optimal ($currentDnsType)")
        }
    }
    
    /**
     * RECORD SWITCH (FOR LIMIT CHECK)
     */
    private fun recordSwitch() {
        val now = System.currentTimeMillis()
        synchronized(switchTimes) {
            switchTimes.add(now)
        }
        switchCount.incrementAndGet()
        
        LogUtil.d(TAG, "📝 Switch recorded: ${switchCount.get()}/$MAX_SWITCHES_30MIN")
    }
    
    /**
     * CHECK SWITCH LIMIT - ENHANCED
     */
    private fun checkSwitchLimit(): Boolean {
        if (!autoSwitchEnabled.get()) {
            return false
        }
        
        val now = System.currentTimeMillis()
        val thirtyMinutesAgo = now - 1_800_000L // 30 minit
        
        // Clean old switches - THREAD-SAFE
        synchronized(switchTimes) {
            switchTimes.removeAll { it < thirtyMinutesAgo }
            
            // Check if limit exceeded
            if (switchTimes.size >= MAX_SWITCHES_30MIN) {
                autoSwitchEnabled.set(false)
                LogUtil.w(TAG, "🚫 Auto-switch disabled for $DISABLE_DURATION ms")
                
                // Schedule re-enable
                coroutineScope.launch {
                    delay(DISABLE_DURATION)
                    autoSwitchEnabled.set(true)
                    switchTimes.clear()
                    LogUtil.d(TAG, "✅ Auto-switch re-enabled")
                }
                
                return false
            }
        }
        
        return true
    }
    
    /**
     * START SWITCH COUNTER CLEANUP
     */
    private fun startSwitchCounterCleanup() {
        switchCounterJob?.cancel()
        switchCounterJob = coroutineScope.launch {
            while (isRunning.get()) {
                delay(300_000L) // 5 minit
                
                val now = System.currentTimeMillis()
                val thirtyMinutesAgo = now - 1_800_000L
                
                // Remove old switches - THREAD-SAFE
                synchronized(switchTimes) {
                    val beforeSize = switchTimes.size
                    switchTimes.removeAll { it < thirtyMinutesAgo }
                    
                    if (beforeSize != switchTimes.size) {
                        LogUtil.d(TAG, "🧹 Cleaned old switches: ${beforeSize} → ${switchTimes.size}")
                    }
                }
            }
        }
    }
    
    /**
     * STOP DNS HEALTH MONITOR
     */
    private fun stopDnsHealthMonitor() {
        dnsHealthMonitorJob?.cancel()
        dnsHealthMonitorJob = null
        
        switchCounterJob?.cancel()
        switchCounterJob = null
        
        // Reset state
        synchronized(switchTimes) {
            switchTimes.clear()
        }
        switchCount.set(0)
        autoSwitchEnabled.set(true)
        qualityCheckFailCount.set(0)
    }
    
    /**
     * NOTIFY DNS SWITCH - ENHANCED
     */
    private fun notifyDnsSwitch(newDns: String) {
        sendBroadcast(Intent("DNS_SWITCHED").apply {
            putExtra("new_dns", newDns)
            putExtra("time", System.currentTimeMillis())
            putExtra("reason", "smart_switch")
            putExtra("peak_hour", isPeakHour())
        })
        updateNotification("Smart→$newDns")
    }
    
    // ====================== END ENHANCED FUNCTIONS ======================
    
    /**
     * SOFT RESTART - OPTIMIZED
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
                if (!isRunning.get() || vpnInterface == null) {
                    LogUtil.w(TAG, "⚠️ VPN not running, attempting recovery...")
                    
                    delay(1000)
                    startVpnService()
                    return@launch
                }
                
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
                
                dnsProxySocket?.close()
                dnsProxySocket = null
                dnsProxyThread = null
                
                delay(500)
                
                val dnsServers = getDnsServers(currentDnsType)
                startDnsProxy(dnsServers)
                updateNotification("Soft-restarted")
                LogUtil.d(TAG, "✅ DNS Proxy soft-restarted successfully")
                
            } catch (e: Exception) {
                LogUtil.e(TAG, "💥 Soft restart failed: ${e.message}")
                
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
                
                handler.postDelayed({
                    restartCount.set(0)
                    LogUtil.d(TAG, "🔄 Restart counter reset")
                }, 60000)
            }
        }
    }
    
    /**
     * UPDATE NOTIFICATION - ENHANCED INFO
     */
    private fun updateNotification(status: String) {
        val notificationManager = getSystemService(Context.NOTIFICATION_SERVICE) 
            as NotificationManager
        
        val peakInfo = if (isPeakHour()) "⏰PEAK" else "📊NORMAL"
        val switchInfo = "Switches: ${switchCount.get()}"
        val failInfo = if (qualityCheckFailCount.get() > 0) " | Fails: ${qualityCheckFailCount.get()}" else ""
        
        val notification = NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle("🛡️ CedokDNS ($status)")
            .setContentText("DNS: $currentDns | $switchInfo$failInfo | $peakInfo")
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
        
        val dnsType = startIntent?.getStringExtra(EXTRA_DNS_TYPE) ?: "A"
        
        val success = setupDnsOnlyVpn(dnsType)
        if (success) {
            isRunning.set(true)
            showNotification()
            startDnsHealthMonitor()   // 🟢 MULA MONITOR BARU
            
            sendBroadcast(Intent("DNS_VPN_STATUS").apply {
                putExtra("status", "ACTIVE")
                putExtra("dns_type", dnsType)
                putExtra("current_dns", currentDns)
                putExtra("peak_hour", isPeakHour())
            })
            
            LogUtil.d(TAG, "✅ VPN started dengan DNS type: $dnsType")
        } else {
            LogUtil.e(TAG, "❌ Failed to start VPN")
            stopSelf()
        }
    }
    
    private fun stopVpnService() {
        stopDnsHealthMonitor()
        if (!isRunning.get()) {
            LogUtil.d(TAG, "VPN already stopped")
            stopSelf()
            return
        }
        
        LogUtil.d(TAG, "Stopping VPN service...")
        
        isRunning.set(false)
        isRestarting.set(false)
        
        // ⬅️ OPTIMIZE THREAD SHUTDOWN
        dnsProxyThread?.let { thread ->
            if (thread.isAlive) {
                thread.interrupt()
                try {
                    thread.join(1000) // Kurangkan dari 2s ke 1s
                } catch (e: InterruptedException) {
                    // Ignore
                }
            }
        }
        
        try {
            dnsProxySocket?.soTimeout = 100
            dnsProxySocket?.close()
        } catch (e: Exception) {
            LogUtil.w(TAG, "Socket close error: ${e.message}")
        } finally {
            dnsProxySocket = null
        }
        
        // ⬅️ OPTIMIZE EXECUTOR SHUTDOWN
        executor.shutdown()
        try {
            if (!executor.awaitTermination(1, TimeUnit.SECONDS)) {
                val unfinished = executor.shutdownNow()
                if (unfinished.isNotEmpty()) {
                    LogUtil.w(TAG, "Unfinished tasks: ${unfinished.size}")
                }
            }
        } catch (e: InterruptedException) {
            Thread.currentThread().interrupt()
            executor.shutdownNow()
        }
        
        vpnInterface?.close()
        vpnInterface = null
        
        stopForeground(true)
        
        sendBroadcast(Intent("DNS_VPN_STATUS").apply {
            putExtra("status", "STOPPED")
            putExtra("dns_type", currentDnsType)
        })
        
        LogUtil.d(TAG, "✅ VPN stopped COMPLETELY")
        
        stopSelf()
    }
    
    /**
     * SERVICE LIFECYCLE
     */
    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
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
