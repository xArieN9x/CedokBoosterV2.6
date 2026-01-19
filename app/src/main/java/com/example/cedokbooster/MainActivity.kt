package com.example.cedokbooster

import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.net.Uri
import android.net.TrafficStats
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.provider.Settings
import android.util.Log
import android.view.View
import android.widget.Button
import android.widget.TextView
import android.widget.Toast
import androidx.appcompat.app.AppCompatActivity
import androidx.localbroadcastmanager.content.LocalBroadcastManager
import kotlinx.coroutines.*
import android.net.VpnService

import android.app.AlertDialog
import android.app.ActivityManager
import android.content.pm.PackageManager
import kotlin.system.exitProcess

import com.example.cedokbooster.AccessibilityAutomationService.Companion.DO_ALL_JOB_TRIGGER
import com.example.cedokbooster.VpnDnsService
import java.io.BufferedReader
import java.io.FileReader

class MainActivity : AppCompatActivity() {

    private lateinit var tvPublicIp: TextView
    private lateinit var tvCoreEngineStatus: TextView
    private lateinit var viewIndicator: View
    private lateinit var btnDoAllJob: Button
    private lateinit var btnOnA: Button
    private lateinit var btnOnAcs: Button
    private lateinit var btnOnB: Button
    private lateinit var btnOff: Button

    private lateinit var forceStopManager: ForceStopManager
    private val handler = Handler(Looper.getMainLooper())

    private var currentDns: String = "none"
    private val scope = CoroutineScope(Dispatchers.Main + SupervisorJob())
    //private var pendingDNS = "A" // default

    companion object {
        private const val TAG = "MainActivity"
    }

    private val statusReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context?, intent: Intent?) {
            when (intent?.action) {
                AppCoreEngService.CORE_ENGINE_STATUS_UPDATE -> {
                    val isRunning = intent.getBooleanExtra("isRunning", false)
                    val dns = intent.getStringExtra("dns") ?: "none"
                    val gpsStatus = intent.getStringExtra("gpsStatus") ?: "idle"
                    
                    updateUIStatus(isRunning, dns, gpsStatus)
                }
            }
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        initViews()
        setupButtons()
        fetchPublicIp()
        requestOverlayPermission()
        forceStopManager = ForceStopManager(this)

        val filter = IntentFilter(AppCoreEngService.CORE_ENGINE_STATUS_UPDATE)
        LocalBroadcastManager.getInstance(this).registerReceiver(statusReceiver, filter)
    }

    private fun initViews() {
        tvPublicIp = findViewById(R.id.tvPublicIp)
        tvCoreEngineStatus = findViewById(R.id.tvCoreEngineStatus)
        viewIndicator = findViewById(R.id.viewIndicator)
        btnDoAllJob = findViewById(R.id.btnDoAllJob)
        btnOnA = findViewById(R.id.btnOnA)
        btnOnAcs = findViewById(R.id.btnOnAcs)
        btnOnB = findViewById(R.id.btnOnB)
        btnOff = findViewById(R.id.btnOff)
    }

    private fun setupButtons() {
        btnOnAcs.setOnClickListener {
            Log.d(TAG, "ON ACS BUTTON CLICKED")
            openAccessibilitySettings()
        }

        /*btnOnA.setOnClickListener {
            Log.d(TAG, "BUTTON START CLICKED")
            
            if (!isAccessibilityEnabled()) {
                Toast.makeText(this, "Sila enable Accessibility Service dulu!", Toast.LENGTH_LONG).show()
                openAccessibilitySettings()
                return@setOnClickListener
            }
            
            val forceCloseIntent = Intent("com.example.cedokbooster.FORCE_CLOSE_PANDA")
            LocalBroadcastManager.getInstance(this).sendBroadcast(forceCloseIntent)
            Log.d(TAG, "Broadcast sent: FORCE_CLOSE_PANDA")
            
            Toast.makeText(this, "Force closing Panda app...", Toast.LENGTH_SHORT).show()
            
            Handler(Looper.getMainLooper()).postDelayed({
                startCEWithVpnCheck("A")
                Log.d(TAG, "Service started after force close (7s delay)")
            }, 7000) // 7 saat delay - SAFE TIMING
        }*/

        // UBAH BUTTON START:
        btnOnA.setOnClickListener {
            Log.d(TAG, "BUTTON START CLICKED - AUTO DNS SELECTION")
            
            if (!isAccessibilityEnabled()) {
                Toast.makeText(this, "Sila enable Accessibility Service dulu!", Toast.LENGTH_LONG).show()
                openAccessibilitySettings()
                return@setOnClickListener
            }
            
            val forceCloseIntent = Intent("com.example.cedokbooster.FORCE_CLOSE_PANDA")
            LocalBroadcastManager.getInstance(this).sendBroadcast(forceCloseIntent)
            Log.d(TAG, "Broadcast sent: FORCE_CLOSE_PANDA")
            
            Toast.makeText(this, "Force closing Panda app...", Toast.LENGTH_SHORT).show()
            
            Handler(Looper.getMainLooper()).postDelayed({
                // 🟢 GANTI: startCEWithVpnCheck("A") dengan auto selection
                startCEWithVpnCheck() 
                Log.d(TAG, "Service started with AUTO DNS selection (7s delay)")
            }, 7000)
        }

        btnOnB.setOnClickListener {
            Log.d(TAG, "BUTTON STOP CLICKED")
            
            if (!isAccessibilityEnabled()) {
                Toast.makeText(this, "Sila enable Accessibility Service dulu!", Toast.LENGTH_LONG).show()
                openAccessibilitySettings()
                return@setOnClickListener
            }
            
            // 1. Stop CoreEngine dulu
            stopCoreEngine()
            
            // 2. Stop VPN
            handler.postDelayed({
            VpnDnsService.stopVpn(this)
           
            Toast.makeText(this@MainActivity, "Phone in Normal Mode", Toast.LENGTH_SHORT).show()
            
            Log.d(TAG, "VPN stopped and toast shown")
            }, 3000)
        }

        btnDoAllJob.setOnClickListener {
            Log.d(TAG, "DO ALL JOB BUTTON CLICKED")
            if (!isAccessibilityEnabled()) {
                Toast.makeText(this, "Accessibility Service tak enabled!", Toast.LENGTH_LONG).show()
                return@setOnClickListener
            }
            
            if (currentDns == "none") {
                Toast.makeText(this, "CoreEngine tidak aktif! klik START dulu!", Toast.LENGTH_LONG).show()
                return@setOnClickListener
            }

            triggerDoAllJob()
        }

        btnOff.setOnClickListener {
            Log.d(TAG, "EXIT BUTTON CLICKED")
            
            AlertDialog.Builder(this)
                .setTitle("Keluar App")
                .setMessage("Hentikan semua service dan tutup app?")
                .setPositiveButton("YA") { dialog, _ ->
                    dialog.dismiss()
                    executeFullExit()
                }
                .setNegativeButton("TIDAK", null)
                .show()
        }
    }

    private fun executeFullExit() {
        Log.d(TAG, "🛑 FULL EXIT STARTED")
        
        // 1. Stop CoreEngine dulu, TUNGGU sampai dia callback selesai
        stopCoreEngineWithCallback { coreEngineStopped ->
            if (coreEngineStopped) {
                Log.d(TAG, "✅ CoreEngine stopped, now stopping VPN...")
                
                // 2. Stop VPN setelah CoreEngine selesai
                VpnDnsService.stopVpn(this@MainActivity)
                
                // Beri masa 3 saat untuk VPN cleanup
                Handler(Looper.getMainLooper()).postDelayed({
                    Log.d(TAG, "✅ VPN should be stopped, now stopping widget...")
                    
                    // 3. Stop widget
                    stopFloatingWidget()
                    
                    // 4. Final kill setelah semua selesai
                    Handler(Looper.getMainLooper()).postDelayed({
                        Log.d(TAG, "✅ All services stopped, final kill...")
                        forceStopManager.stopEverythingNuclear()
                        finishAffinity()
                    }, 2000) // Tunggu 2s untuk widget stop
                    
                }, 3000) // Tunggu 3s untuk VPN stop
            }
        }
    }
    
    private fun stopCoreEngineWithCallback(callback: (Boolean) -> Unit) {
        Log.d(TAG, "Stopping CoreEngine with callback...")
        
        // Simpan original state
        val wasRunning = currentDns != "none"
        
        // Trigger stop
        stopCoreEngine()
        
        // Check status setiap 500ms
        val handler = Handler(Looper.getMainLooper())
        val checkRunnable = object : Runnable {
            var attempts = 0
            override fun run() {
                attempts++
                
                // Check jika CoreEngine dah stop (currentDns == "none")
                if (currentDns == "none" || attempts > 10) { // Max 5 saat
                    Log.d(TAG, "CoreEngine stop confirmed: ${currentDns == "none"}")
                    callback(currentDns == "none")
                } else {
                    // Check lagi
                    handler.postDelayed(this, 500)
                }
            }
        }
        handler.postDelayed(checkRunnable, 1000)
    }

    private fun stopFloatingWidget() {
        try {
            val serviceIntent = Intent(this, FloatingWidgetService::class.java)
            serviceIntent.action = FloatingWidgetService.ACTION_STOP_WIDGET
            startService(serviceIntent)
            Log.d(TAG, "Widget stop command sent")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to stop widget: ${e.message}")
        }
    }

    private fun openAccessibilitySettings() {
        val intent = Intent(Settings.ACTION_ACCESSIBILITY_SETTINGS)
        startActivity(intent)
        Toast.makeText(this, "Cari 'CedokBooster' dan enable", Toast.LENGTH_LONG).show()
    }

    private fun isAccessibilityEnabled(): Boolean {
        val expectedServiceName = "$packageName/${AccessibilityAutomationService::class.java.name}"
        val enabledServices = Settings.Secure.getString(
            contentResolver,
            Settings.Secure.ENABLED_ACCESSIBILITY_SERVICES
        )
        return enabledServices?.contains(expectedServiceName) == true
    }

    private fun startCoreEngine(dnsType: String) {
        currentDns = dnsType
        val intent = Intent(this, AppCoreEngService::class.java).apply {
            action = AppCoreEngService.ACTION_START_ENGINE
            putExtra("dnsType", dnsType)
        }
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            startForegroundService(intent)
        } else {
            startService(intent)
        }

        Toast.makeText(this, "CoreEngine starting dengan DNS $dnsType...", Toast.LENGTH_SHORT).show()
    }

    private fun stopCoreEngine() {
        val intent = Intent(this, AppCoreEngService::class.java).apply {
            action = AppCoreEngService.ACTION_STOP_ENGINE
        }
        startService(intent)
        
        currentDns = "none"
        updateUIStatus(false, "none", "idle")
        
        Toast.makeText(this, "CoreEngine stopped", Toast.LENGTH_SHORT).show()
    }

    private fun stopEverything() {
        Log.d(TAG, "Stopping EVERYTHING: CoreEngine + VPN")
        
        // 1. Stop VPN first (network layer)
        try {
            VpnDnsService.stopVpn(this)
            Log.d(TAG, "✅ VPN & CoreEngine stopped")
        } catch (e: Exception) {
            Log.e(TAG, "VPN stop error: ${e.message}")
        }
        
        // 2. Stop CoreEngine service
        val intent = Intent(this, AppCoreEngService::class.java).apply {
            action = AppCoreEngService.ACTION_STOP_ENGINE
        }
        startService(intent)
        
        // 3. Update UI
        currentDns = "none"
        updateUIStatus(false, "none", "idle")
        
        Toast.makeText(this, "All services stopped", Toast.LENGTH_SHORT).show()
    }

    private fun triggerDoAllJob() {
        val intent = Intent(AccessibilityAutomationService.DO_ALL_JOB_TRIGGER)
        LocalBroadcastManager.getInstance(this).sendBroadcast(intent)
        Toast.makeText(this, "DO ALL JOB triggered!", Toast.LENGTH_SHORT).show()
        Log.d(TAG, "DO_ALL_JOB_TRIGGER sent")
    }

    private fun updateUIStatus(isRunning: Boolean, dns: String, gpsStatus: String) {
        runOnUiThread {
            tvCoreEngineStatus.text = if (isRunning) {
                "CoreEngine: Active (DNS: $dns) | GPS: $gpsStatus"
            } else {
                "CoreEngine: Disabled"
            }

            when {
                !isRunning -> {
                    viewIndicator.setBackgroundResource(R.drawable.red_circle)
                }
                gpsStatus == "stabilizing" -> {
                    viewIndicator.setBackgroundResource(R.drawable.yellow_circle)
                }
                gpsStatus == "locked" -> {
                    viewIndicator.setBackgroundResource(R.drawable.green_circle)
                }
                else -> {
                    viewIndicator.setBackgroundResource(R.drawable.yellow_circle)
                }
            }
        }
    }

    private fun fetchPublicIp() {
        CoroutineScope(Dispatchers.IO).launch {
            var ip: String? = null
            try {
                val url = java.net.URL("https://1.1.1.1/cdn-cgi/trace")
                val text = url.readText().trim()
                // Format: ip=123.123.123.123
                val ipLine = text.lines().find { it.startsWith("ip=") }
                ip = ipLine?.substringAfter("=")?.trim()
            } catch (e1: Exception) {
                // Fallback to ipify jika 1.1.1.1 gagal
                try {
                    ip = java.net.URL("https://api.ipify.org").readText().trim()
                } catch (e2: Exception) {
                    ip = null
                }
            }
            withContext(Dispatchers.Main) {
                tvPublicIp.text = if (ip.isNullOrEmpty()) "Public IP: —" else "Public IP: $ip"
            }
        }
    }

    private fun requestOverlayPermission() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            if (!Settings.canDrawOverlays(this)) {
                val intent = Intent(
                    Settings.ACTION_MANAGE_OVERLAY_PERMISSION,
                    Uri.parse("package:$packageName")
                )
                startActivity(intent)
                Toast.makeText(this, "Sila enable overlay permission untuk floating widget", Toast.LENGTH_LONG).show()
            }
        }
    }

    /*private fun startCEWithVpnCheck(dnsType: String) {
        // 1. Check jika VPN dah approve
        val vpnIntent = VpnService.prepare(this)
        
        if (vpnIntent != null) {
            // BELUM APPROVE: Show popup dulu
            startActivityForResult(vpnIntent, 100)
            // Simpan dnsType untuk guna lepas approve
            pendingDNS = dnsType
        } else {
            // DAH APPROVE: Start CE seperti biasa
            startCoreEngine(dnsType)
        }
    }*/

    // UBAH FUNCTION startCEWithVpnCheck:
    private fun startCEWithVpnCheck(dnsType: String = "auto") { // 🟢 DEFAULT "auto"
        // 1. Check jika VPN dah approve
        val vpnIntent = VpnService.prepare(this)
        
        if (vpnIntent != null) {
            // BELUM APPROVE: Show popup dulu
            startActivityForResult(vpnIntent, 100)
            // 🟢 Simpan sebagai "auto"
            // pendingDNS = dnsType // 🗑️ BUANG
        } else {
            // DAH APPROVE: Start CE dengan DNS type
            startCoreEngine(dnsType) // 🟢 Pass "auto"
        }
    }

    /*override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        if (requestCode == 100 && resultCode == RESULT_OK) {
            // SEKARANG VPN DAH APPROVE
            startCoreEngine(pendingDNS)
        }
    }*/

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        if (requestCode == 100 && resultCode == RESULT_OK) {
            // SEKARANG VPN DAH APPROVE
            startCoreEngine("auto") // 🟢 Start dengan auto selection
        }
    }

    override fun onResume() {
        super.onResume()
        // Query service status bila app resume
        queryServiceStatus()
    }

    private fun queryServiceStatus() {
        // Check if service running
        val am = getSystemService(Context.ACTIVITY_SERVICE) as android.app.ActivityManager
        var isServiceRunning = false
        
        try {
            val services = am.getRunningServices(Int.MAX_VALUE)
            for (service in services) {
                if (service.service.className == AppCoreEngService::class.java.name) {
                    isServiceRunning = true
                    break
                }
            }
        } catch (e: Exception) {
            Log.e(TAG, "Error checking service status", e)
        }

        // Send query broadcast to service
        if (isServiceRunning) {
            val intent = Intent(AppCoreEngService.ACTION_QUERY_STATUS)
            sendBroadcast(intent)
            Log.d(TAG, "Querying service status...")
        } else {
            // Service not running, update UI
            updateUIStatus(false, "none", "idle")
            Log.d(TAG, "Service not running, UI updated")
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        scope.cancel()
        //stopMonitor() // TAMBAH: Stop monitor
        LocalBroadcastManager.getInstance(this).unregisterReceiver(statusReceiver)
    }
}
