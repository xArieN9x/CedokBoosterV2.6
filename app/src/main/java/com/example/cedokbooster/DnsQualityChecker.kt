package com.example.cedokbooster

import android.util.Log
import java.net.*
import java.util.concurrent.*
import kotlin.math.*
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.ConcurrentHashMap

class DnsQualityChecker {

    companion object {
        private const val TAG = "DnsQualityChecker"

        // ⬅️ OPTIMIZED DOMAINS FOR DIFFERENT MODES
        private val PANDA_CRITICAL_DOMAINS = listOf(
            "perseus-productanalytics.deliveryhero.net",
            "my.usehurrier.com"
        )

        private val PANDA_EXTENDED_DOMAINS = listOf(
            "perseus-productanalytics.deliveryhero.net",
            "my.usehurrier.com", 
            "service2.us.incognia.com",
            "api.mapbox.com",
            "deliveryhero.net"
        )

        private val STANDARD_DOMAINS = listOf(
            "google.com",
            "cloudflare.com"
        )

        // ⬅️ ENHANCED DNS CANDIDATES
        private val DNS_CANDIDATES = listOf(
            "1.1.1.1",          // Cloudflare Primary
            "1.0.0.1",          // Cloudflare Secondary
            "8.8.8.8",          // Google Primary
            "8.8.4.4"           // Google Secondary
        )

        // ⬅️ SIMPLIFIED CANDIDATES FOR PEAK HOUR
        private val PEAK_HOUR_CANDIDATES = listOf(
            "1.1.1.1",          // Cloudflare
            "8.8.8.8"           // Google
        )

        // ===== MEMORY: simpan sejarah =====
        private val dnsHistory = ConcurrentHashMap<String, MutableList<Long>>()
        private val dnsFailHistory = ConcurrentHashMap<String, AtomicInteger>()
        private const val MAX_HISTORY = 30

        /**
         * ⬅️ ENHANCED: CHECK DNS FOR PANDA WITH MODES
         */
        fun checkDnsForPanda(dnsServer: String, peakHour: Boolean = false): DnsQualityResult {
            return try {
                // PEAK HOUR: GUNA LIGHTWEIGHT CHECK
                if (peakHour) {
                    return quickCheckForPanda(dnsServer)
                }

                val pandaDomains = PANDA_EXTENDED_DOMAINS
                val standardDomains = STANDARD_DOMAINS

                val pandaResults = mutableListOf<Long>()
                val pandaSuccess = AtomicInteger(0)
                val standardResults = mutableListOf<Long>()
                val standardSuccess = AtomicInteger(0)

                // ⬅️ OPTIMIZED THREAD POOL
                val executor = Executors.newFixedThreadPool(2) // Kurang dari 3 ke 2
                val latch = CountDownLatch(pandaDomains.size + standardDomains.size)

                pandaDomains.forEach { domain ->
                    executor.submit {
                        try {
                            val startTime = System.nanoTime()
                            val addresses = InetAddress.getAllByName(domain)
                            val latency = (System.nanoTime() - startTime) / 1_000_000
                            
                            if (addresses.isNotEmpty() && latency in 10..1000) {
                                pandaResults.add(latency)
                                pandaSuccess.incrementAndGet()
                            }
                        } catch (_: Exception) {
                            // Silent fail
                        } finally {
                            latch.countDown()
                        }
                    }
                }

                standardDomains.forEach { domain ->
                    executor.submit {
                        try {
                            val startTime = System.nanoTime()
                            val addresses = InetAddress.getAllByName(domain)
                            val latency = (System.nanoTime() - startTime) / 1_000_000
                            
                            if (addresses.isNotEmpty() && latency in 10..1000) {
                                standardResults.add(latency)
                                standardSuccess.incrementAndGet()
                            }
                        } catch (_: Exception) {
                            // Silent fail
                        } finally {
                            latch.countDown()
                        }
                    }
                }

                executor.shutdown()
                latch.await(4, TimeUnit.SECONDS) // ⬅️ INCREASE TIMEOUT

                val result = calculatePandaScore(
                    dnsServer,
                    pandaResults,
                    pandaSuccess.get(),
                    standardResults,
                    standardSuccess.get()
                )

                updateHistory(dnsServer, result.avgLatencyMs, result.isUsable)
                result

            } catch (e: Exception) {
                Log.e(TAG, "DNS check error: ${e.message}")
                updateHistory(dnsServer, 999, false)
                DnsQualityResult(dnsServer, 0, 999, 0, 0, false, "FAILED")
            }
        }

        /**
         * ⬅️ NEW: QUICK CHECK FOR PANDA (PEAK HOUR OPTIMIZED)
         */
        fun quickCheckForPanda(dnsServer: String): DnsQualityResult {
            return try {
                val domains = PANDA_CRITICAL_DOMAINS // ⬅️ 2 DOMAIN SAHAJA
                val results = mutableListOf<Long>()
                val successCount = AtomicInteger(0)

                val executor = Executors.newFixedThreadPool(2)
                val latch = CountDownLatch(domains.size)

                domains.forEach { domain ->
                    executor.submit {
                        try {
                            val startTime = System.nanoTime()
                            val addresses = InetAddress.getAllByName(domain)
                            val latency = (System.nanoTime() - startTime) / 1_000_000
                            
                            if (addresses.isNotEmpty() && latency in 10..800) {
                                results.add(latency)
                                successCount.incrementAndGet()
                            }
                        } catch (_: Exception) {
                            // Silent fail
                        } finally {
                            latch.countDown()
                        }
                    }
                }

                executor.shutdown()
                latch.await(3, TimeUnit.SECONDS) // ⬅️ SHORTER TIMEOUT

                val successRate = if (domains.isNotEmpty()) {
                    (successCount.get() * 100) / domains.size
                } else 0

                val avgLatency = if (results.isNotEmpty()) results.average().toLong() else 999

                // ⬅️ SIMPLIFIED SCORING FOR QUICK CHECK
                val score = when {
                    successRate == 100 && avgLatency < 200 -> 90
                    successRate == 100 && avgLatency < 400 -> 75
                    successRate >= 50 && avgLatency < 600 -> 60
                    successRate >= 50 -> 40
                    else -> 20
                }

                val status = when {
                    score >= 85 -> "PANDA_ELITE"
                    score >= 70 -> "PANDA_STRONG"
                    score >= 50 -> "PANDA_OK"
                    else -> "UNSTABLE"
                }

                val result = DnsQualityResult(
                    server = dnsServer,
                    score = score,
                    avgLatencyMs = avgLatency,
                    pandaScore = successRate,
                    successRate = successRate, // Same for quick check
                    isUsable = score >= 40,
                    status = status
                )

                updateHistory(dnsServer, avgLatency, score >= 40)
                result

            } catch (e: Exception) {
                Log.e(TAG, "Quick DNS check error: ${e.message}")
                DnsQualityResult(dnsServer, 0, 999, 0, 0, false, "FAILED")
            }
        }

        private fun updateHistory(dns: String, latency: Long, ok: Boolean) {
            try {
                val list = dnsHistory.getOrPut(dns) { mutableListOf() }
                list.add(latency)
                if (list.size > MAX_HISTORY) list.removeAt(0)

                if (!ok) {
                    dnsFailHistory.getOrPut(dns) { AtomicInteger(0) }.incrementAndGet()
                } else {
                    // Reset fail count jika OK
                    dnsFailHistory[dns]?.set(0)
                }
            } catch (e: Exception) {
                Log.e(TAG, "Update history error: ${e.message}")
            }
        }

        private fun getTrendScore(dns: String): Int {
            return try {
                val list = dnsHistory[dns] ?: return 50
                if (list.isEmpty()) return 50

                val avg = list.average()
                val variance = list.map { (it - avg).pow(2) }.average()
                val jitter = sqrt(variance)

                when {
                    avg < 150 && jitter < 50 -> 100
                    avg < 300 && jitter < 100 -> 80
                    avg < 500 -> 60
                    else -> 30
                }
            } catch (e: Exception) {
                50 // Fallback
            }
        }

        private fun calculatePandaScore(
            dnsServer: String,
            pandaLatencies: List<Long>,
            pandaSuccess: Int,
            standardLatencies: List<Long>,
            standardSuccess: Int
        ): DnsQualityResult {

            val pandaDomainsSize = PANDA_EXTENDED_DOMAINS.size
            val standardDomainsSize = STANDARD_DOMAINS.size

            val pandaSuccessRate = if (pandaDomainsSize > 0) {
                (pandaSuccess * 100) / pandaDomainsSize
            } else 0

            val pandaAvgLatency = if (pandaLatencies.isNotEmpty()) {
                pandaLatencies.average().toLong()
            } else 999

            val standardSuccessRate = if (standardDomainsSize > 0) {
                (standardSuccess * 100) / standardDomainsSize
            } else 0

            // ⬅️ ENHANCED SCORING ALGORITHM
            val instantScore = when {
                pandaSuccessRate >= 80 && pandaAvgLatency < 200 -> 85
                pandaSuccessRate >= 70 && pandaAvgLatency < 300 -> 75
                pandaSuccessRate >= 50 && pandaAvgLatency < 500 -> 60
                pandaSuccessRate >= 30 -> 40
                else -> 10
            }

            val trendScore = getTrendScore(dnsServer)
            val failPenalty = dnsFailHistory[dnsServer]?.get() ?: 0

            var totalScore = (instantScore * 0.7 + trendScore * 0.3).toInt()
            totalScore -= min(failPenalty * 3, 20) // ⬅️ REDUCED PENALTY

            val status = when {
                totalScore >= 85 -> "PANDA_ELITE"
                totalScore >= 70 -> "PANDA_STRONG"
                totalScore >= 50 -> "PANDA_OK"
                totalScore >= 30 -> "PANDA_WEAK"
                else -> "UNSTABLE"
            }

            val usable = totalScore >= 40 || standardSuccessRate >= 70

            return DnsQualityResult(
                server = dnsServer,
                score = totalScore.coerceIn(0, 100),
                avgLatencyMs = pandaAvgLatency,
                pandaScore = pandaSuccessRate,
                successRate = standardSuccessRate,
                isUsable = usable,
                status = status
            )
        }

        /**
         * ⬅️ ENHANCED: SELECT BEST DNS WITH PEAK HOUR OPTIMIZATION
         */
        fun selectBestDnsForPanda(peakHour: Boolean = false): String {
            Log.d(TAG, "🔍 Selecting best DNS for Panda... (Peak: $peakHour)")

            val candidates = if (peakHour) {
                Log.d(TAG, "⏰ Peak hour mode - Lightweight check")
                PEAK_HOUR_CANDIDATES
            } else {
                DNS_CANDIDATES
            }

            val results = mutableListOf<DnsQualityResult>()
            val executor = Executors.newCachedThreadPool()

            // ⬅️ TIMEOUT FOR ENTIRE SELECTION
            val timeoutMs = if (peakHour) 8000L else 12000L // 8s/12s

            candidates.forEach { dns ->
                executor.submit {
                    try {
                        val result = if (peakHour) {
                            quickCheckForPanda(dns)
                        } else {
                            checkDnsForPanda(dns, peakHour)
                        }
                        
                        synchronized(results) {
                            results.add(result)
                        }
                        Log.d(TAG, "DNS $dns → ${result.score} (${result.status}) [${result.avgLatencyMs}ms]")
                    } catch (e: Exception) {
                        Log.e(TAG, "DNS $dns check failed: ${e.message}")
                    }
                }
            }

            executor.shutdown()
            
            return try {
                if (!executor.awaitTermination(timeoutMs, TimeUnit.MILLISECONDS)) {
                    Log.w(TAG, "⚠️ DNS selection timeout")
                    executor.shutdownNow()
                }

                // ⬅️ ENHANCED SELECTION LOGIC
                val bestResult = results
                    .filter { it.isUsable }
                    .maxByOrNull { result ->
                        // Priority: Score > Latency > Stability
                        val scoreWeight = result.score * 0.6
                        val latencyWeight = (1000 - result.avgLatencyMs).coerceAtLeast(0) * 0.3
                        val stabilityWeight = getTrendScore(result.server) * 0.1
                        (scoreWeight + latencyWeight + stabilityWeight).toInt()
                    }

                bestResult?.server ?: "1.1.1.1"

            } catch (e: Exception) {
                Log.e(TAG, "Selection error: ${e.message}")
                "1.1.1.1"
            }
        }

        /**
         * ⬅️ QUICK DNS CHECK (SINGLE DOMAIN)
         */
        fun quickDnsCheck(dnsServer: String, domain: String = "google.com"): Boolean {
            return try {
                val start = System.nanoTime()
                val addresses = InetAddress.getAllByName(domain)
                val latency = (System.nanoTime() - start) / 1_000_000
                
                addresses.isNotEmpty() && latency < 500
            } catch (e: Exception) {
                false
            }
        }

        /**
         * ⬅️ NEW: QUICK DNS CHECK FOR PANDA DOMAIN
         */
        fun quickDnsCheck(domain: String): Boolean {
            return try {
                val start = System.nanoTime()
                val addresses = InetAddress.getAllByName(domain)
                val latency = (System.nanoTime() - start) / 1_000_000
                
                addresses.isNotEmpty() && latency < 800
            } catch (e: Exception) {
                false
            }
        }

        /**
         * ⬅️ NEW: GET DNS SERVER HEALTH STATUS
         */
        fun getDnsHealthStatus(dnsServer: String): String {
            return try {
                val result = quickCheckForPanda(dnsServer)
                when {
                    result.score >= 70 -> "HEALTHY"
                    result.score >= 40 -> "DEGRADED"
                    else -> "UNHEALTHY"
                }
            } catch (e: Exception) {
                "UNKNOWN"
            }
        }
    }

    data class DnsQualityResult(
        val server: String,
        val score: Int,
        val avgLatencyMs: Long,
        val pandaScore: Int,
        val successRate: Int,
        val isUsable: Boolean,
        val status: String
    )
}
