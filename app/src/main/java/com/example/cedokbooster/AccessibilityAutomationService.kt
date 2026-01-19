package com.example.cedokbooster

import android.accessibilityservice.AccessibilityService
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.os.Handler
import android.os.Looper
import android.provider.Settings
import android.util.Log
import android.view.accessibility.AccessibilityEvent
import android.view.accessibility.AccessibilityNodeInfo
import androidx.localbroadcastmanager.content.LocalBroadcastManager
import java.util.ArrayDeque

class AccessibilityAutomationService : AccessibilityService() {

    companion object {
        private const val TAG = "AccessibilityAutomation"
        const val FORCE_CLOSE_PANDA = "com.example.cedokbooster.FORCE_CLOSE_PANDA"
        const val DO_ALL_JOB_TRIGGER = "DO_ALL_JOB_TRIGGER"
    }
        
    private val storageKeys = arrayOf("Storage usage", "Storage usage ", "Storage", "Storage & cache", "App storage")
    private val forceStopKeys = arrayOf("Force stop", "Force stop ", "Force Stop", "Paksa berhenti", "Paksa Hentikan")
    private val confirmOkKeys = arrayOf("OK", "Yes", "Confirm", "Ya", "Force stop ", "Force stop")
    private val clearCacheKeys = arrayOf("Clear cache", "Clear cache ", "Clear Cache", "Kosongkan cache")

    private val handler = Handler(Looper.getMainLooper())
    private var isAutomationRunning = false
    //private var currentStep = 0

    // ==================== FUNGSI UTAMA DARI PROJEK LAMA ====================
    fun findAndClick(vararg keys: String, maxRetries: Int = 3, delayMs: Long = 700L): Boolean {
        repeat(maxRetries) {
            val root = rootInActiveWindow
            if (root != null) {
                for (k in keys) {
                    // Exact text matches
                    val nodes = root.findAccessibilityNodeInfosByText(k)
                    if (!nodes.isNullOrEmpty()) {
                        for (n in nodes) {
                            if (n.isClickable) { 
                                n.performAction(AccessibilityNodeInfo.ACTION_CLICK); 
                                return true 
                            }
                            var p = n.parent
                            while (p != null) {
                                if (p.isClickable) { 
                                    p.performAction(AccessibilityNodeInfo.ACTION_CLICK); 
                                    return true 
                                }
                                p = p.parent
                            }
                        }
                    }
                    // Content-desc scan
                    val desc = findNodeByDescription(root, k)
                    if (desc != null) { 
                        desc.performAction(AccessibilityNodeInfo.ACTION_CLICK); 
                        return true 
                    }
                    // ViewId fallback
                    val idNode = findNodeByViewId(root, k)
                    if (idNode != null) {
                        if (idNode.isClickable) { 
                            idNode.performAction(AccessibilityNodeInfo.ACTION_CLICK); 
                            return true 
                        }
                        var p = idNode.parent
                        while (p != null) {
                            if (p.isClickable) { 
                                p.performAction(AccessibilityNodeInfo.ACTION_CLICK); 
                                return true 
                            }
                            p = p.parent
                        }
                    }
                }
                // Try scroll to reveal
                root.performAction(AccessibilityNodeInfo.ACTION_SCROLL_FORWARD)
            }
            Thread.sleep(delayMs)
        }
        return false
    }

    private fun findNodeByDescription(root: AccessibilityNodeInfo, text: String): AccessibilityNodeInfo? {
        val stack = ArrayDeque<AccessibilityNodeInfo>()
        stack.add(root)
        while (stack.isNotEmpty()) {
            val n = stack.removeFirst()
            try {
                val cd = n.contentDescription
                if (cd != null && cd.toString().contains(text, true)) return n
            } catch (_: Exception) {}
            for (i in 0 until n.childCount) n.getChild(i)?.let { stack.add(it) }
        }
        return null
    }

    private fun findNodeByViewId(root: AccessibilityNodeInfo, idPart: String): AccessibilityNodeInfo? {
        val stack = ArrayDeque<AccessibilityNodeInfo>()
        stack.add(root)
        while (stack.isNotEmpty()) {
            val n = stack.removeFirst()
            try {
                val vid = n.viewIdResourceName
                if (vid != null && vid.contains(idPart, true)) return n
            } catch (_: Exception) {}
            for (i in 0 until n.childCount) n.getChild(i)?.let { stack.add(it) }
        }
        return null
    }
    // ==================== AKHIR FUNGSI DARI PROJEK LAMA ====================

    private val broadcastReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context, intent: Intent) {
            when (intent.action) {
                "DO_ALL_JOB_TRIGGER" -> {
                    Log.d(TAG, "════════════════════════════════")
                    Log.d(TAG, "DO_ALL_JOB_TRIGGER received")
                    if (!isAutomationRunning) {
                        startAutomationSequence()
                    }
                }
                FORCE_CLOSE_PANDA -> {
                    Log.d(TAG, "FORCE_CLOSE_PANDA received")
                    performForceCloseAndClearCache()
                }
                "com.example.cedokbooster.GPS_LOCK_ACHIEVED" -> {
                    Log.d(TAG, "GPS_LOCK_ACHIEVED received - Launching Panda")
                    handler.postDelayed({
                        launchPandaApp()
                    }, 1000)
                }
            }
        }
    }

    override fun onCreate() {
        super.onCreate()
        Log.d(TAG, "Service onCreate")
        
        val filter = IntentFilter().apply {
            addAction("DO_ALL_JOB_TRIGGER")
            addAction(Companion.FORCE_CLOSE_PANDA)
            addAction("com.example.cedokbooster.GPS_LOCK_ACHIEVED")
        }
        LocalBroadcastManager.getInstance(this).registerReceiver(broadcastReceiver, filter)
    }

    override fun onServiceConnected() {
        super.onServiceConnected()
        Log.i(TAG, "Accessibility Service Connected")
        
        val config = serviceInfo.apply {
            eventTypes = AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED or
                        AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED
            feedbackType = android.accessibilityservice.AccessibilityServiceInfo.FEEDBACK_GENERIC
            flags = android.accessibilityservice.AccessibilityServiceInfo.FLAG_INCLUDE_NOT_IMPORTANT_VIEWS
            notificationTimeout = 100
        }
        this.serviceInfo = config
    }

    private fun startAutomationSequence() {
        if (isAutomationRunning) return
        
        Log.i(TAG, "=== STARTING AUTOMATION SEQUENCE ===")
        isAutomationRunning = true
        
        Log.d(TAG, "Step 1: Force Stop + Clear Cache")
        performForceCloseAndClearCache()
        
        // ⏱️ TIMING IMPROVEMENT: Tambah delay
        handler.postDelayed({
            Log.d(TAG, "Step 2: Airplane Mode ON→OFF")
            toggleAirplaneMode(true)
        }, 8000) // 7000 → 8000
        
        // ⏱️ TIMING IMPROVEMENT: Lebih lama untuk VPN stabil
        handler.postDelayed({
            Log.d(TAG, "Step 3: Restarting CoreEngine")
            restartCoreEngine()
        }, 16000) // 14000 → 16000
        
        // ⏱️ TIMING IMPROVEMENT
        handler.postDelayed({
            Log.d(TAG, "Step 4: Launching Panda app")
            launchPandaApp()
            isAutomationRunning = false
            Log.i(TAG, "=== AUTOMATION SEQUENCE COMPLETE ===")
        }, 20000) // 18000 → 20000
    }

    // ==================== FLOW BARU: GABUNG FORCE STOP & CLEAR CACHE ====================
    private fun performForceCloseAndClearCache() {
        handler.post {
            try {
                // 1. Buka App Info Panda
                val intent = Intent(Settings.ACTION_APPLICATION_DETAILS_SETTINGS).apply {
                    data = android.net.Uri.parse("package:com.logistics.rider.foodpanda")
                    addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                }
                startActivity(intent)
                Log.d(TAG, "Opened Panda app info")
                
                // 2. Tunggu ⏱️ 1000ms (dari 1200ms) untuk App Info load
                handler.postDelayed({
                    // 3. Force Stop
                    val forceStopClicked = findAndClick(*forceStopKeys)
                    
                    if (forceStopClicked) {
                        Log.d(TAG, "Force Stop clicked")
                        // 4. Confirm ⏱️ 500ms (dari 700ms)
                        handler.postDelayed({
                            val confirmClicked = findAndClick(*confirmOkKeys)
                            
                            if (confirmClicked) {
                                Log.d(TAG, "Force Stop confirmed")
                                // 5. Tunggu ⏱️ 1200ms (dari 1800ms) untuk process selesai
                                handler.postDelayed({
                                    // 6. Clear Cache Flow
                                    val storageClicked = findAndClick(*storageKeys)
                                    
                                    if (storageClicked) {
                                        Log.d(TAG, "Storage clicked")
                                        // 7. Tunggu ⏱️ 1000ms (dari 1500ms) untuk Storage page load
                                        handler.postDelayed({
                                            val cacheClicked = findAndClick(*clearCacheKeys)
                                            
                                            if (cacheClicked) {
                                                Log.d(TAG, "Clear Cache clicked")
                                                // 8. Kembali ke Main & Home
                                                handler.postDelayed({
                                                    performGlobalAction(GLOBAL_ACTION_BACK)
                                                    handler.postDelayed({
                                                        performGlobalAction(GLOBAL_ACTION_HOME)
                                                        Log.d(TAG, "Force Stop + Clear Cache COMPLETE")
                                                    }, 400)
                                                }, 800)
                                            } else {
                                                Log.d(TAG, "Clear Cache FAILED")
                                                performGlobalAction(GLOBAL_ACTION_HOME)
                                            }
                                        }, 1000) // ⬅️ UBAH: 1500 → 1000
                                    } else {
                                        Log.d(TAG, "Storage button FAILED")
                                        performGlobalAction(GLOBAL_ACTION_HOME)
                                    }
                                }, 1200) // ⬅️ UBAH: 1800 → 1200
                            } else {
                                Log.d(TAG, "Confirmation FAILED")
                                performGlobalAction(GLOBAL_ACTION_HOME)
                            }
                        }, 500) // ⬅️ UBAH: 700 → 500
                    } else {
                        Log.d(TAG, "Force Stop FAILED")
                        performGlobalAction(GLOBAL_ACTION_HOME)
                    }
                }, 1000) // ⬅️ UBAH: 1200 → 1000
                
            } catch (e: Exception) {
                Log.e(TAG, "Error in performForceCloseAndClearCache: ${e.message}")
                performGlobalAction(GLOBAL_ACTION_HOME)
            }
        }
    }

    private fun toggleAirplaneMode(turnOn: Boolean) {
        handler.post {
            // 1. Buka Quick Settings SEKALI SAHAJA
            performGlobalAction(AccessibilityService.GLOBAL_ACTION_QUICK_SETTINGS)
            Log.d(TAG, "Quick Settings opened")
            
            // 2. Tunggu 700ms untuk panel load
            handler.postDelayed({
                val airplaneKeys = arrayOf(
                    "Airplane mode", "Airplane mode ", "Airplane", 
                    "Mod Pesawat", "Mod Penerbangan", "Aeroplane mode"
                )
                
                // 3. Click Airplane ON
                val clicked = findAndClick(*airplaneKeys, maxRetries = 3)
                if (!clicked) {
                    findAndClick("Airplane", maxRetries = 3)
                }
                Log.d(TAG, "Airplane Mode ${if (turnOn) "ON" else "OFF"} clicked")
                
                // 4. TUNGGU DALAM SAME SESSION
                if (turnOn) {
                    // Jika ON: tunggu 4s dalam ON state
                    handler.postDelayed({
                        // 5. Click lagi sekali untuk OFF (masih dalam Quick Settings yang sama)
                        val clicked2 = findAndClick(*airplaneKeys, maxRetries = 3)
                        if (!clicked2) {
                            findAndClick("Airplane", maxRetries = 3)
                        }
                        Log.d(TAG, "Airplane Mode OFF clicked (after waiting)")
                        
                        // 6. Tutup Quick Settings & Home (SEKALI SAHAJA)
                        handler.postDelayed({
                            performGlobalAction(AccessibilityService.GLOBAL_ACTION_BACK)
                            handler.postDelayed({
                                performGlobalAction(AccessibilityService.GLOBAL_ACTION_HOME)
                                Log.d(TAG, "Airplane ON→OFF sequence COMPLETE")
                            }, 300)
                        }, 1000)
                    }, 3000) // Tunggu 4s dalam ON state
                    
                } else {
                    // Jika OFF: terus tutup
                    handler.postDelayed({
                        performGlobalAction(AccessibilityService.GLOBAL_ACTION_BACK)
                        handler.postDelayed({
                            performGlobalAction(AccessibilityService.GLOBAL_ACTION_HOME)
                            Log.d(TAG, "Airplane Mode OFF complete")
                        }, 300)
                    }, 1000)
                }
            }, 700)
        }
    }

    private fun restartCoreEngine() {
        val intent = Intent("RESTART_CORE_ENGINE")
        LocalBroadcastManager.getInstance(this).sendBroadcast(intent)
        Log.d(TAG, "Sent RESTART_CORE_ENGINE broadcast")
    }

    private fun launchPandaApp() {
        handler.post {
            try {
                val intent = packageManager.getLaunchIntentForPackage("com.logistics.rider.foodpanda")
                if (intent != null) {
                    intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_CLEAR_TOP)
                    startActivity(intent)
                    Log.d(TAG, "Panda app launched")
                } else {
                    Log.e(TAG, "No launch intent for Panda app")
                }
            } catch (e: Exception) {
                Log.e(TAG, "Error launching Panda app: ${e.message}")
            }
        }
    }

    // Function lama (untuk compatibility)
    private fun findButtonByDescription(rootNode: AccessibilityNodeInfo, description: String) {
        val node = findNodeByDescription(rootNode, description)
        if (node != null) {
            node.performAction(AccessibilityNodeInfo.ACTION_CLICK)
        }
    }

    override fun onAccessibilityEvent(event: AccessibilityEvent?) {
        event?.let {
            if (it.packageName == "com.logistics.rider.foodpanda") {
                Log.d(TAG, "Panda window event: ${it.className}")
            }
        }
    }

    override fun onInterrupt() {
        Log.i(TAG, "Service interrupted")
    }

    override fun onDestroy() {
        Log.d(TAG, "Service onDestroy")
        handler.removeCallbacksAndMessages(null)
        try {
            LocalBroadcastManager.getInstance(this).unregisterReceiver(broadcastReceiver)
        } catch (e: Exception) {
            Log.e(TAG, "Error unregistering receiver: ${e.message}")
        }
        super.onDestroy()
    }
}
