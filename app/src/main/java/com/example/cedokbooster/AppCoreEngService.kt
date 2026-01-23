package com.example.cedokbooster

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.Service
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.location.Location
import android.location.LocationListener
import android.location.LocationManager
import android.location.LocationProvider
import android.os.Build
import android.os.Bundle
import android.os.IBinder
import android.os.PowerManager
import android.os.Handler
import android.os.Looper
import android.util.Log
import androidx.core.app.NotificationCompat
import androidx.localbroadcastmanager.content.LocalBroadcastManager
import kotlinx.coroutines.*

import java.net.HttpURLConnection
import java.net.URL
import android.net.ConnectivityManager
import android.net.Network
import android.net.NetworkCapabilities
import android.net.NetworkRequest
import androidx.annotation.RequiresApi

import java.net.DatagramSocket
import java.net.DatagramPacket
import java.net.InetAddress

import android.Manifest
import android.content.pm.PackageManager
import androidx.core.content.ContextCompat

class AppCoreEngService : Service() {

    private var wakeLock: PowerManager.WakeLock? = null
    private var locationManager: LocationManager? = null
    private var gpsHealthJob: Job? = null
    private var keepAliveJob: Job? = null
    private var dnsType: String = "none"
    private var gpsStatus: String = "idle"
    private var isEngineRunning = false
    private val handler = Handler(Looper.getMainLooper())

    companion object {
        private const val TAG = "AppCoreEngService"
        const val ACTION_START_ENGINE = "com.example.cedokbooster.START_ENGINE"
        const val ACTION_STOP_ENGINE = "com.example.cedokbooster.STOP_ENGINE"
        const val ACTION_QUERY_STATUS = "com.example.cedokbooster.QUERY_STATUS"
        const val CORE_ENGINE_STATUS_UPDATE = "com.example.cedokbooster.CORE_ENGINE_STATUS_UPDATE"
        const val GPS_LOCK_ACHIEVED = "com.example.cedokbooster.GPS_LOCK_ACHIEVED"
        
        private const val NOTIFICATION_ID = 1001
        private const val CHANNEL_ID = "core_engine_channel"
    }

    private val statusQueryReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context?, intent: Intent?) {
            if (intent?.action == ACTION_QUERY_STATUS) {
                Log.d(TAG, "Status query received, broadcasting current status")
                broadcastStatus()
            }
        }
    }

    // ==================== UPDATE LOCATION LISTENERS ====================
    private val locationListener = object : LocationListener {
        override fun onLocationChanged(location: Location) {
            val accuracy = location.accuracy
            Log.d(TAG, "🛰️ GPS Update: Accuracy = $accuracy meters")
        
            if (accuracy < 25f && gpsStatus != "locked") {
                gpsStatus = "locked"
                Log.d(TAG, "GPS LOCKED! Accuracy: $accuracy meters")
                broadcastStatus()
                
                Handler(Looper.getMainLooper()).postDelayed({
                    val intent = Intent(GPS_LOCK_ACHIEVED)
                    LocalBroadcastManager.getInstance(this@AppCoreEngService).sendBroadcast(intent)
                    Log.d(TAG, "GPS_LOCK_ACHIEVED broadcast sent (delayed)")
                }, 2000)
            } else if (accuracy >= 25f && gpsStatus == "locked") {
                gpsStatus = "stabilizing"
                broadcastStatus()
            }
        }
        override fun onStatusChanged(provider: String?, status: Int, extras: Bundle?) {}
        override fun onProviderEnabled(provider: String) {}
        override fun onProviderDisabled(provider: String) {}
    }
    
    // 2. TAMBAH Network Location Listener (untuk indoor)
    private val networkLocationListener = object : LocationListener {
        override fun onLocationChanged(location: Location) {
            val accuracy = location.accuracy
            Log.d(TAG, "📶 Network Location: Accuracy = $accuracy meters")
            
            // Kalau GPS takde signal, guna network location
            if (accuracy < 100 && (gpsStatus == "stabilizing" || gpsStatus == "disabled")) {
                gpsStatus = "network_lock"
                broadcastStatus()
                Log.d(TAG, "Network location active (indoor/backup)")
            }
        }
        override fun onStatusChanged(provider: String?, status: Int, extras: Bundle?) {}
        override fun onProviderEnabled(provider: String) {}
        override fun onProviderDisabled(provider: String) {}
    }

    override fun onCreate() {
        super.onCreate()
        Log.d(TAG, "Service onCreate()")
        createNotificationChannel()
        
        // Register receiver for status queries
        val filter = IntentFilter(ACTION_QUERY_STATUS)
        registerReceiver(statusQueryReceiver, filter)

        val restartFilter = IntentFilter("RESTART_CORE_ENGINE")
        LocalBroadcastManager.getInstance(this).registerReceiver(restartReceiver, restartFilter)
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        when (intent?.action) {
            ACTION_START_ENGINE -> {
                dnsType = intent.getStringExtra("dnsType") ?: "A"
                startCoreEngine()
            }
            ACTION_STOP_ENGINE -> {
                stopCoreEngine()
            }
        }
        return START_STICKY
    }

    private val restartReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context, intent: Intent) {
            if (intent.action == "RESTART_CORE_ENGINE") {
                Log.d(TAG, "RESTART_CORE_ENGINE received - SMART RESTART")
                
                // SMART RESTART: Jangan stop CoreEngine, cuma trigger soft restart VPN
                handler.postDelayed({
                    // Soft restart VPN sahaja
                    try {
                        VpnDnsService.softRestartVpn(this@AppCoreEngService)
                        Log.d(TAG, "✅ VPN soft restart triggered")
                        
                        // Refresh network conditioning
                        stopNetworkConditioning()
                        handler.postDelayed({
                            startNetworkConditioning()
                            Log.d(TAG, "Network conditioning restarted")
                        }, 500)
                        
                        // Update notification
                        broadcastStatus()
                        
                    } catch (e: Exception) {
                        Log.e(TAG, "Failed to soft restart VPN: ${e.message}")
                    }
                }, 500)
            }
        }
    }

    private fun startCoreEngine() {
        if (isEngineRunning) {
            Log.d(TAG, "CoreEngine already running, restarting...")
            stopCoreEngine()
        }

        Log.d(TAG, "Starting CoreEngine with DNS: $dnsType")
        isEngineRunning = true

        // APPLY DNS
        applyDNS()

        // Start foreground
        startForeground(NOTIFICATION_ID, createNotification())

        // Acquire wakelock
        acquireWakeLock()

        // Start GPS
        startGPSStabilization()

        // Start network conditioning
        startNetworkConditioning()

        // Start anchor service
        startService(Intent(this, AnchorService::class.java))

        // Start floating widget
        startService(Intent(this, FloatingWidgetService::class.java).apply {
            action = FloatingWidgetService.ACTION_START_WIDGET
            putExtra("isActive", true)
        })

        broadcastStatus()
    }

    private fun stopCoreEngine() {
        Log.d(TAG, "Stopping CoreEngine")
        isEngineRunning = false
        gpsStatus = "idle"
    
        // 1. Stop VPN
        try {
            VpnDnsService.stopVpn(this@AppCoreEngService)
            Log.d(TAG, "VPN stopped from CoreEngine")
        } catch (e: Exception) {
            Log.e(TAG, "VPN stop error: ${e.message}")
        }
    
        // 2. Stop GPS
        stopGPSStabilization()
    
        // 3. Release wakelock
        releaseWakeLock()
    
        // 4. Stop network conditioning
        stopNetworkConditioning()
    
        // 5. Update floating widget (tetap aktif, cuma status update)
        startService(Intent(this, FloatingWidgetService::class.java).apply {
            action = FloatingWidgetService.ACTION_START_WIDGET
            putExtra("isActive", false)
        })
    
        // 6. Broadcast status terakhir
        broadcastStatus()
        
        // 7. Stop service ini sahaja, widget KEKAL
        stopForeground(true)
        stopSelf()
    }

    private fun acquireWakeLock() {
        val powerManager = getSystemService(Context.POWER_SERVICE) as PowerManager
        wakeLock = powerManager.newWakeLock(
            PowerManager.PARTIAL_WAKE_LOCK,
            "CedokBooster::CoreEngineWakeLock"
        ).apply {
            acquire(60 * 60 * 1000L) // 1 hour
        }
        Log.d(TAG, "WakeLock acquired")
    }

    private fun releaseWakeLock() {
        wakeLock?.let {
            if (it.isHeld) {
                it.release()
                Log.d(TAG, "WakeLock released")
            }
        }
        wakeLock = null
    }

    private fun startGPSStabilization() {
        // Check runtime permission
        if (ContextCompat.checkSelfPermission(
                this,
                Manifest.permission.ACCESS_FINE_LOCATION
            ) != PackageManager.PERMISSION_GRANTED
        ) {
            Log.e(TAG, "ACCESS_FINE_LOCATION permission not granted")
            return
        }
    
        // Check background location for Android 10+ (API 29+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            if (ContextCompat.checkSelfPermission(
                    this,
                    Manifest.permission.ACCESS_BACKGROUND_LOCATION
                ) != PackageManager.PERMISSION_GRANTED
            ) {
                Log.w(TAG, "BACKGROUND_LOCATION not granted - may restrict in background")
            }
        }
    
        gpsStatus = "stabilizing"
        locationManager = getSystemService(Context.LOCATION_SERVICE) as LocationManager
        
        // Check providers enabled
        val isGpsEnabled = locationManager?.isProviderEnabled(LocationManager.GPS_PROVIDER) == true
        val isNetworkEnabled = locationManager?.isProviderEnabled(LocationManager.NETWORK_PROVIDER) == true
        
        if (!isGpsEnabled && !isNetworkEnabled) {
            Log.e(TAG, "No location providers available")
            gpsStatus = "disabled"
            broadcastStatus()
            return
        }
        
        try {
            // ALWAYS START NETWORK PROVIDER (indoor backup)
            if (isNetworkEnabled) {
                locationManager?.requestLocationUpdates(
                    LocationManager.NETWORK_PROVIDER,
                    2000L, // 2 seconds untuk battery saving
                    10f,   // 10 meter minimum distance change
                    networkLocationListener
                )
                Log.d(TAG, "Network Provider started (indoor backup)")
            }
            
            // START GPS jika enabled (high accuracy)
            if (isGpsEnabled) {
                locationManager?.requestLocationUpdates(
                    LocationManager.GPS_PROVIDER,
                    1000L, // 1 second untuk outdoor accuracy
                    0f,    // No minimum distance
                    LocationListener  // Use renamed listener
                )
                Log.d(TAG, "GPS Provider started: 1000ms interval")
            } else {
                Log.w(TAG, "GPS not enabled, relying on network location")
                gpsStatus = "network_only"
            }
            
            broadcastStatus()
        } catch (e: SecurityException) {
            Log.e(TAG, "Location permission not granted", e)
        } catch (e: Exception) {
            Log.e(TAG, "Failed to start location updates: ${e.message}")
        }
    }
    
    // 4. UPDATE stopGPSStabilization():
    private fun stopGPSStabilization() {
        try {
            // Remove both listeners
            locationManager?.removeUpdates(LocationListener)
            locationManager?.removeUpdates(networkLocationListener)
            Log.d(TAG, "GPS + Network location stopped")
            gpsStatus = "stopped"
            broadcastStatus()
        } catch (e: Exception) {
            Log.e(TAG, "Failed to stop location: ${e.message}")
        }
    }

    // Dalam class AppCoreEngService (tambah function baru):
    private fun triggerGpsRecovery() {
        Log.d(TAG, "🔄 Triggering GPS recovery...")
        
        // 1. Stop existing updates
        try {
            locationManager?.removeUpdates(LocationListener)
            locationManager?.removeUpdates(networkLocationListener)
        } catch (e: Exception) { /* ignore */ }
        
        // 2. Small delay
        handler.postDelayed({
            // 3. Restart dengan fresh state
            startGPSStabilization()
            Log.d(TAG, "✅ GPS recovery completed")
        }, 1000)
    }

    private fun startGpsHealthMonitor() {
        gpsHealthJob = CoroutineScope(Dispatchers.IO).launch {
            var lastGoodLocationTime = System.currentTimeMillis()
            
            while (isActive && isEngineRunning) {
                delay(30000) // Check setiap 30 saat
                
                val currentTime = System.currentTimeMillis()
                val timeSinceLastUpdate = currentTime - lastGoodLocationTime
                
                // Jika lebih 2 minit takde location update
                if (timeSinceLastUpdate > 120000 && gpsStatus != "stopped") {
                    Log.w(TAG, "⚠️ GPS stale for ${timeSinceLastUpdate/1000}s, triggering recovery")
                    triggerGpsRecovery()
                    lastGoodLocationTime = currentTime
                }
            }
        }
    }

    // NEW UPDATE for VpnDnsService.kt
    private fun applyDNS() {
        Log.d(TAG, "Applying DNS: $dnsType")
        
        try {
            // Guna VpnDnsService untuk apply DNS sebenar
            VpnDnsService.startVpn(this, dnsType)
            Log.d(TAG, "DNS VPN service started dengan type: $dnsType")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to start DNS VPN: ${e.message}")
            // Fallback ke dummy log (existing behavior)
            val dns = when (dnsType) {
                //"A" -> "156.154.70.1"
                "A" -> "1.1.1.1"
                else -> "8.8.8.8"
            }
            Log.d(TAG, "Fallback: DNS would be: $dns")
        }
    }

    // NEW UPDATE for VpnDnsService.kt
    private fun restoreDNS() {
        Log.d(TAG, "Restoring default DNS")
        
        try {
            VpnDnsService.stopVpn(this)
            Log.d(TAG, "DNS VPN service stopped")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to stop DNS VPN: ${e.message}")
            // Fallback ke existing behavior
            Log.d(TAG, "Fallback: DNS restored to default")
        }
    }

    private fun startNetworkConditioning() {
        keepAliveJob = CoroutineScope(Dispatchers.IO).launch {
            val udpSocket = DatagramSocket()
            var consecutiveFailures = 0
            val maxFailures = 3
    
            HttpURLConnection.setFollowRedirects(true)
    
            prewarmCDNConnections()
    
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                setupNetworkPriority()
            }
    
            var cycle = 0
    
            while (isActive) {
                try {
                    cycle++
    
                    // =============================
                    // Target rotation (human-like)
                    // =============================
                    val targets = listOf(
                        // Critical Panda Hosts
                        "https://perseus-productanalytics.deliveryhero.net",
                        "https://my.usehurrier.com",
                        "https://service2.us.incognia.com",
                        "https://api.mapbox.com",
                        
                        // CDN / Traffic
                        "https://www.google.com",
                        "https://youtube.com",
                        "https://i.ytimg.com",
                        "https://yt3.ggpht.com",
                        "https://dns.google",
                        "https://one.one.one.one",
                        "https://www.gstatic.com",
                        "https://rr1---sn-5hne6nsk.googlevideo.com"
                    )
    
                    val target = targets[cycle % targets.size]
    
                    // =====================================
                    // UDP Keep-alive (multi-DNS + human interval)
                    // =====================================
                    if (cycle % 3 == 0) {
                        try {
                            val dnsServers = listOf("1.1.1.1", "8.8.8.8", "8.8.4.4")
                            val targetIP = dnsServers[cycle % dnsServers.size]
                            val timestamp = System.currentTimeMillis()
                            val pingData = "PING/$timestamp".toByteArray()
                            val pingPacket = DatagramPacket(pingData, pingData.size, InetAddress.getByName(targetIP), 53)
                            udpSocket.send(pingPacket)
                            Log.d(TAG, "UDP keep-alive -> $targetIP:53")
                        } catch (e: Exception) {
                            Log.w(TAG, "UDP keep-alive skipped: ${e.message}")
                        }
                    }
    
                    // =====================================
                    // HTTP request loop with retry & adaptive
                    // =====================================
                    var connection: HttpURLConnection? = null
                    var success = false
                    var attempts = 0
                    val maxAttempts = 2
    
                    while (!success && attempts < maxAttempts) {
                        try {
                            attempts++
                            connection = URL(target).openConnection() as HttpURLConnection
                            connection.connectTimeout = 4000
                            connection.readTimeout = 6000
    
                            // Realistic headers
                            connection.setRequestProperty("User-Agent",
                                "Mozilla/5.0 (Linux; Android 10; RMX2020) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36")
                            connection.setRequestProperty("Accept",
                                "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8")
                            connection.setRequestProperty("Accept-Language", "en-US,en;q=0.9")
                            connection.setRequestProperty("Connection", "keep-alive")
    
                            // Adaptive method rotation
                            val methods = listOf("HEAD", "GET", "OPTIONS")
                            val method = when {
                                target.contains("googlevideo.com") -> "HEAD"
                                cycle % 5 == 0 -> "GET"
                                else -> methods[cycle % methods.size]
                            }
                            connection.requestMethod = method
    
                            // Adaptive payload simulation
                            val simulatePayload = cycle % 5 == 0
                            if (simulatePayload && method == "GET") connection.doInput = true
    
                            connection.connect()
                            val responseCode = connection.responseCode
    
                            // Adaptive payload read (human-like, small random size)
                            if (simulatePayload && responseCode == 200 && method == "GET") {
                                try {
                                    val inputStream = connection.inputStream
                                    val buffer = ByteArray(1024)
                                    var totalRead = 0
                                    var bytesRead: Int
                                    while (totalRead < (2048 + (0..1024).random())) {
                                        bytesRead = inputStream.read(buffer)
                                        if (bytesRead == -1) break
                                        totalRead += bytesRead
                                    }
                                    if (totalRead > 0) Log.d(TAG, "Payload read: $totalRead bytes")
                                } catch (e: Exception) {
                                    Log.w(TAG, "Payload read skipped: ${e.message}")
                                }
                            }
    
                            // Traffic classification enhanced
                            val trafficType = when {
                                target.contains("deliveryhero.net") -> "PANDA-ANALYTICS"
                                target.contains("usehurrier.com") -> "PANDA-DISPATCH"
                                target.contains("incognia.com") -> "PANDA-FRAUD"
                                target.contains("mapbox.com") && target.contains("api") -> "PANDA-MAPS"
                                target.contains("ytimg.com") -> "YT-CDN"
                                target.contains("yt3.ggpht.com") -> "YT-AVATAR"
                                target.contains("googlevideo.com") -> "YT-VIDEO"
                                target.contains("youtube.com") -> "YT-MAIN"
                                target.contains("one.one.one.one") -> "CF-DNS"
                                target.contains("dns.google") -> "GG-DNS"
                                target.contains("gstatic.com") -> "G-STATIC"
                                target.contains("google.com") && !target.contains("dns") -> "GOOGLE"
                                else -> "WEB"
                            }
    
                            Log.d(TAG, "[$trafficType] $target -> $responseCode ($method) [Attempt: $attempts]")
    
                            success = true
                            consecutiveFailures = 0
                        } catch (e: Exception) {
                            Log.w(TAG, "Request failed (attempt $attempts): ${e.message}")
                            if (attempts >= maxAttempts) consecutiveFailures++
                        } finally {
                            connection?.disconnect()
                        }
                    }
    
                    // =====================================
                    // Adaptive human-like delay (power gila)
                    // =====================================
                    val delay = when {
                        consecutiveFailures >= maxFailures -> 60000L
                        target.contains("deliveryhero") || target.contains("usehurrier") ||
                                target.contains("incognia") || target.contains("mapbox") ->
                            if (!success) 12000L else (8000L..15000L).random()
                        !success -> 15000L
                        else -> listOf(10000L, 15000L, 20000L, 25000L, 30000L, 35000L).random()
                    }
    
                    delay(delay)
    
                } catch (e: Exception) {
                    Log.e(TAG, "Network conditioning cycle failed: ${e.message}")
                    consecutiveFailures++
                    delay(if (consecutiveFailures >= maxFailures) 60000L else 10000L)
                }
            }
    
            udpSocket.close()
        }
    
        Log.d(TAG, "ENHANCED Network conditioning started (POWER GILA VERSION)")
    }
    
    // =============================================
    // CDN Pre-warming (robust, human stagger + retry)
    // =============================================
    private fun prewarmCDNConnections() {
        CoroutineScope(Dispatchers.IO).launch {
            val cdns = listOf(
                "https://www.google.com",
                "https://yt3.ggpht.com",
                "https://i.ytimg.com",
                "https://fonts.gstatic.com",
                "https://www.gstatic.com",
                "https://play.googleapis.com",
                "https://dns.google",
                "https://one.one.one.one"
            )
    
            cdns.forEachIndexed { index, cdn ->
                delay(index * (600L..1200L).random()) // human-like stagger
    
                var attempts = 0
                var success = false
                while (!success && attempts < 2) {
                    attempts++
                    try {
                        val connection = URL(cdn).openConnection() as HttpURLConnection
                        connection.connectTimeout = 4000
                        connection.readTimeout = 4000
                        connection.requestMethod = "HEAD"
                        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; Android 10) AppleWebKit/537.36")
                        connection.connect()
                        val code = connection.responseCode
                        Log.d(TAG, "CDN pre-warmed: $cdn ($code) [Attempt: $attempts]")
                        connection.disconnect()
                        success = true
                    } catch (e: Exception) {
                        Log.w(TAG, "CDN pre-warm retry $cdn (attempt $attempts)")
                        if (attempts < 2) delay((800L..1500L).random())
                    }
                }
            }
        }
    }
    
    // =============================================
    // Network priority (robust + proper cleanup)
    // =============================================
    @RequiresApi(Build.VERSION_CODES.M)
    private fun setupNetworkPriority() {
        try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            val request = NetworkRequest.Builder()
                .addCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET)
                .addCapability(NetworkCapabilities.NET_CAPABILITY_VALIDATED)
                .addCapability(NetworkCapabilities.NET_CAPABILITY_NOT_RESTRICTED)
                .addTransportType(NetworkCapabilities.TRANSPORT_CELLULAR)
                .addTransportType(NetworkCapabilities.TRANSPORT_WIFI)
                .build()
    
            val callback = object : ConnectivityManager.NetworkCallback() {
                override fun onAvailable(network: Network) {
                    Log.d(TAG, "Priority network available: $network")
                    try { cm.bindProcessToNetwork(network) } catch (e: Exception) { Log.e(TAG, "Bind failed: ${e.message}") }
                }
    
                override fun onLost(network: Network) {
                    Log.d(TAG, "Priority network lost: $network")
                    try { cm.bindProcessToNetwork(null) } catch (e: Exception) { Log.w(TAG, "Unbind failed: ${e.message}") }
                }
    
                override fun onUnavailable() { Log.w(TAG, "Priority network unavailable") }
            }
    
            cm.requestNetwork(request, callback)
        } catch (e: Exception) { Log.e(TAG, "Network priority setup failed: ${e.message}") }
    }

    private fun stopNetworkConditioning() {
        keepAliveJob?.cancel()
        Log.d(TAG, "Network conditioning stopped")
    }

    private fun broadcastStatus() {
        val intent = Intent(CORE_ENGINE_STATUS_UPDATE).apply {
            putExtra("isRunning", isEngineRunning)
            putExtra("dns", dnsType)
            putExtra("gpsStatus", gpsStatus)
        }
        LocalBroadcastManager.getInstance(this).sendBroadcast(intent)
        
        // Update notification
        if (isEngineRunning) {
            val notification = createNotification()
            val manager = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            manager.notify(NOTIFICATION_ID, notification)
        }
    }

    private fun createNotification(): Notification {
        val statusText = if (isEngineRunning) {
            "CoreEngine Active (DNS: $dnsType) | GPS: $gpsStatus"
        } else {
            "CoreEngine Stopped"
        }

        return NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle("CedokBooster")
            .setContentText(statusText)
            .setSmallIcon(android.R.drawable.ic_dialog_info)
            .setPriority(NotificationCompat.PRIORITY_LOW)
            .setOngoing(true)
            .build()
    }

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val channel = NotificationChannel(
                CHANNEL_ID,
                "Core Engine Service",
                NotificationManager.IMPORTANCE_LOW
            ).apply {
                description = "Keeps CoreEngine running"
            }
            val manager = getSystemService(NotificationManager::class.java)
            manager.createNotificationChannel(channel)
        }
    }

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onDestroy() {
        super.onDestroy()
        stopNetworkConditioning()
        stopGPSStabilization()
        try {
            unregisterReceiver(statusQueryReceiver)
            // ✅ TAMBAH BARIS INI:
            LocalBroadcastManager.getInstance(this).unregisterReceiver(restartReceiver)
        } catch (e: Exception) {
            Log.e(TAG, "Error unregistering receiver", e)
        }
    }
}
