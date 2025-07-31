package co.uk.doverguitarteacher.voiceguitartuner

import android.Manifest
import android.content.Context
import android.content.pm.PackageManager
import android.media.AudioAttributes
import android.media.SoundPool
import android.os.Bundle
import android.util.Log
import android.view.LayoutInflater
import android.view.WindowManager
import android.widget.Button
import android.widget.ImageView
import android.widget.TextView
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.slideInVertically
import androidx.compose.foundation.BorderStroke
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.KeyboardArrowLeft
import androidx.compose.material.icons.automirrored.filled.KeyboardArrowRight
import androidx.compose.material.icons.automirrored.filled.VolumeOff
import androidx.compose.material.icons.automirrored.filled.VolumeUp
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.draw.shadow
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.*
import androidx.compose.ui.graphics.drawscope.DrawScope
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.graphics.lerp
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import androidx.core.content.edit
import androidx.lifecycle.lifecycleScope
import be.tarsos.dsp.AudioDispatcher
import be.tarsos.dsp.AudioEvent
import be.tarsos.dsp.AudioProcessor
import be.tarsos.dsp.filters.HighPass
import be.tarsos.dsp.filters.LowPassFS
import be.tarsos.dsp.io.android.AudioDispatcherFactory
import be.tarsos.dsp.pitch.PitchDetectionHandler
import be.tarsos.dsp.pitch.PitchProcessor
import be.tarsos.dsp.util.fft.FFT
import com.android.billingclient.api.AcknowledgePurchaseParams
import com.android.billingclient.api.BillingClient
import com.android.billingclient.api.BillingClientStateListener
import com.android.billingclient.api.BillingFlowParams
import com.android.billingclient.api.BillingResult
import com.android.billingclient.api.PendingPurchasesParams
import com.android.billingclient.api.ProductDetails
import com.android.billingclient.api.ProductDetailsResponseListener
import com.android.billingclient.api.Purchase
import com.android.billingclient.api.PurchasesUpdatedListener
import com.android.billingclient.api.QueryProductDetailsParams
import com.android.billingclient.api.QueryProductDetailsResult
import com.android.billingclient.api.QueryPurchasesParams
import com.google.android.gms.ads.*
import com.google.android.gms.ads.nativead.NativeAd
import com.google.android.gms.ads.nativead.NativeAdOptions
import com.google.android.gms.ads.nativead.NativeAdView
import kotlinx.coroutines.*
import java.util.Locale
import kotlin.math.abs
import kotlin.math.log2

enum class VisualizerMode {
    NONE, BARS, WAVEFORM
}

class MainActivity : ComponentActivity() {

    companion object {
        private const val TAG = "MainActivity"
        private const val REQUEST_RECORD_AUDIO_PERMISSION = 200
        private const val SAMPLE_RATE = 22050
        private const val AUDIO_BUFFER_SIZE = 2048
        private const val BUFFER_OVERLAP = 0
        private const val CONFIDENCE_THRESHOLD = 0.9f
        private const val PITCH_BUFFER_SIZE = 5
        private const val IN_TUNE_DELAY_MS = 2500L
        private const val IN_TUNE_CENTS_THRESHOLD = 3.0f
        private const val PREFS_NAME = "TunerPrefs"
        private const val PREF_PEDAL_SKIN = "pedal_skin"
        private const val PREF_VDU_SKIN = "vdu_skin"
        private const val SCROLLING_WAVEFORM_MAX_SIZE = 16384
        private const val PRODUCT_ID = "1" // Replace with your real one-time product id from Play Console
        private const val PREF_AD_FREE = "pref_ad_free"
    }

    private var nativeAd by mutableStateOf<NativeAd?>(null)
    private var isAdVisible by mutableStateOf(false)
    private var isRecording by mutableStateOf(false)
    private var detectedNote by mutableStateOf("--")
    private var frequencyText by mutableStateOf("0.00 Hz")
    private var statusText by mutableStateOf("Press Start to Tune")
    private var statusColor by mutableStateOf(Color.White)
    private var rotationAngle by mutableFloatStateOf(0f)
    private var smoothedAngle by mutableFloatStateOf(0f)
    private var voiceModeEnabled by mutableStateOf(false)
    private var cents by mutableFloatStateOf(0.0f)
    private val activeLedIndex by derivedStateOf { (cents / 10f).coerceIn(-5f, 5f).toInt() }
    private var isMetronomeRunning by mutableStateOf(false)
    private var tempo by mutableIntStateOf(120)
    private var timeSignatureIndex by mutableIntStateOf(0)
    private var metronomeJob: Job? = null
    private var visualizerMode by mutableStateOf(VisualizerMode.WAVEFORM)
    private var magnitudes by mutableStateOf(floatArrayOf())
    private var scrollingWaveformData by mutableStateOf<List<Float>>(emptyList())
    private var soundsLoaded by mutableStateOf(false)
    private var selectedPedal by mutableIntStateOf(R.drawable.red)
    private var selectedVDU by mutableIntStateOf(R.drawable.dial)
    private var dispatcher: AudioDispatcher? = null
    private var audioThread: Thread? = null
    private lateinit var soundPool: SoundPool
    private var soundUp = 0; private var soundDown = 0; private var soundIntune = 0; private var soundTick = 0
    private var lastFeedbackTime = 0L
    private val pitchBuffer = mutableListOf<Float>()
    private var inTuneStartTime = 0L
    private var inTuneSoundPlayed = false
    private lateinit var pedalImages: List<Int>
    private lateinit var vduImages: List<Int>
    private lateinit var timeSignatures: List<String>
    private lateinit var noteFrequencies: List<Pair<Float, String>>
    private var isAdFree by mutableStateOf(false)

    private lateinit var billingClient: BillingClient
    private var adRemovalProductDetails: ProductDetails? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        val prefs = getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        isAdFree = prefs.getBoolean(PREF_AD_FREE, false)

        setupBillingClient()

        MobileAds.initialize(this) {}
        if (!isAdFree) {
            loadAd()
        }

        // --- BUG FIX 1: BULLETPROOF SKIN LOADING ---
        try {
            val loadedPedalId = prefs.getInt(PREF_PEDAL_SKIN, R.drawable.dovercastle1)
            val loadedVduId = prefs.getInt(PREF_VDU_SKIN, R.drawable.dial)
            resources.getResourceName(loadedPedalId)
            resources.getResourceName(loadedVduId)
            selectedPedal = loadedPedalId
            selectedVDU = loadedVduId
        } catch (e: Exception) {
            Log.e(TAG, "Failed to load skins, likely due to invalid preference data. Resetting to default.", e)
            selectedPedal = R.drawable.dovercastle1
            selectedVDU = R.drawable.dial
            prefs.edit { clear() }
        }
        // --- END BUG FIX 1 ---

        pedalImages = listOf(
            R.drawable.vintage_drive_pedal, R.drawable.blue_delay_pedal, R.drawable.wood, R.drawable.wood2, R.drawable.punk, R.drawable.taj,
            R.drawable.dovercastle1, R.drawable.gothic, R.drawable.alien, R.drawable.cyber, R.drawable.graffiti, R.drawable.steampunk,
            R.drawable.usa, R.drawable.spacerock, R.drawable.acrylic, R.drawable.horse, R.drawable.surf,
            R.drawable.red, R.drawable.yellow, R.drawable.black, R.drawable.doom , R.drawable.green, R.drawable.cats, R.drawable.wolf, R.drawable.sunflowers
        )
        vduImages = listOf(R.drawable.dial2, R.drawable.dial3, R.drawable.dial4, R.drawable.dial)
        timeSignatures = listOf("4/4", "3/4", "6/8", "2/4", "5/4")
        noteFrequencies = listOf(82.41f to "E2", 110.00f to "A2", 146.83f to "D3", 196.00f to "G3", 246.94f to "B3", 329.63f to "E4")

        setupSoundPool()

        setContent {
            val window = this@MainActivity.window
            LaunchedEffect(isRecording, isMetronomeRunning) {
                val keepScreenOn = isRecording || isMetronomeRunning
                if (keepScreenOn) window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
                else window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
            }

            // --- BUG FIX 2: STABLE NEEDLE ANIMATION ---
            LaunchedEffect(Unit) {
                while (true) {
                    delay(16)
                    val smoothing = 0.1f
                    if (abs(smoothedAngle - rotationAngle) > 0.01f) {
                        smoothedAngle += (rotationAngle - smoothedAngle) * smoothing
                    } else if (smoothedAngle != rotationAngle) {
                        smoothedAngle = rotationAngle
                    }
                }
            }
            // --- END BUG FIX 2 ---

            MaterialTheme {
                Surface(modifier = Modifier.fillMaxSize()) {
                    Box(modifier = Modifier.fillMaxSize()) {
                        Image(
                            painter = painterResource(id = selectedPedal),
                            contentDescription = null,
                            modifier = Modifier.fillMaxSize()
                        )

                        // ===== Top-center controls with a small black " remove ads " button =====
                        Column(
                            modifier = Modifier
                                .align(Alignment.TopCenter)
                                .padding(top = 16.dp),
                            horizontalAlignment = Alignment.CenterHorizontally
                        ) {
                            // Keep your existing controls if you like; "remove ads" is centered and small.
                            if (!isAdFree) {
                                Button(
                                    onClick = { launchPurchaseFlow() },
                                    enabled = adRemovalProductDetails != null,
                                    colors = ButtonDefaults.buttonColors(
                                        containerColor = Color.Black,
                                        contentColor = Color.White
                                    ),
                                    contentPadding = PaddingValues(horizontal = 12.dp, vertical = 6.dp),
                                    shape = RoundedCornerShape(6.dp)
                                ) {
                                    Text(" remove ads ", fontSize = 12.sp)
                                }
                                Spacer(Modifier.height(8.dp))
                            }

                            // Your original top row:
                            MetronomeControls(enabled = soundsLoaded)
                            Spacer(modifier = Modifier.height(16.dp))
                            Row(
                                horizontalArrangement = Arrangement.spacedBy(8.dp),
                                verticalAlignment = Alignment.CenterVertically
                            ) {
                                Button(
                                    onClick = { if (isRecording) stopTuner() else requestPermissionAndStartTuner() },
                                    colors = ButtonDefaults.buttonColors(
                                        containerColor = Color.Black,
                                        contentColor = Color.White
                                    )
                                ) { Text(if (isRecording) "Stop" else "Start") }

                                Button(
                                    onClick = { randomizeSkins() },
                                    colors = ButtonDefaults.buttonColors(
                                        containerColor = Color.Black,
                                        contentColor = Color.White
                                    )
                                ) { Text("Skin") }

                                VisualizerToggleButton()
                            }
                        }

                        Column(
                            horizontalAlignment = Alignment.CenterHorizontally,
                            modifier = Modifier.align(Alignment.Center).offset(y = (-15).dp)
                        ) {
                            LedTuningStrip(activeLedIndex = activeLedIndex)
                            Image(
                                painter = painterResource(id = selectedVDU),
                                contentDescription = null,
                                modifier = Modifier.size(240.dp)
                            )
                        }

                        Image(
                            painter = painterResource(id = R.drawable.needle),
                            contentDescription = null,
                            modifier = Modifier
                                .size(140.dp)
                                .align(Alignment.Center)
                                .offset(y = (-15).dp)
                                .graphicsLayer {
                                    rotationZ = smoothedAngle
                                    transformOrigin = TransformOrigin(0.5f, 0.84f)
                                }
                        )

                        Icon(
                            imageVector = if (voiceModeEnabled) Icons.AutoMirrored.Filled.VolumeUp else Icons.AutoMirrored.Filled.VolumeOff,
                            contentDescription = "Toggle Voice Feedback",
                            tint = if (voiceModeEnabled) Color.Green else Color.Red,
                            modifier = Modifier
                                .padding(12.dp)
                                .size(28.dp)
                                .align(Alignment.TopStart)
                                .clickable { if (soundsLoaded) voiceModeEnabled = !voiceModeEnabled }
                        )

                        Box(modifier = Modifier.align(Alignment.BottomCenter)) {
                            BottomControls()
                        }
                    }
                }
            }
        }
    }

    private fun loadAd() {
        if (isAdFree) return
        val adUnitId = getString(R.string.native_ad_unit_id)
        val adLoader = AdLoader.Builder(this, adUnitId)
            .forNativeAd { ad: NativeAd ->
                nativeAd = ad
                isAdVisible = true
                Log.d(TAG, "Native ad loaded. Will be shown immediately.")
            }
            .withAdListener(object : AdListener() {
                override fun onAdFailedToLoad(adError: LoadAdError) {
                    Log.e(TAG, "Ad failed to load: ${adError.message}")
                    nativeAd = null
                }
            })
            .withNativeAdOptions(NativeAdOptions.Builder().build())
            .build()
        adLoader.loadAd(AdRequest.Builder().build())
    }

    private fun setupBillingClient() {
        val purchasesUpdatedListener =
            PurchasesUpdatedListener { billingResult, purchases ->
                if (billingResult.responseCode == BillingClient.BillingResponseCode.OK && purchases != null) {
                    for (purchase in purchases) {
                        handlePurchase(purchase)
                    }
                } else if (billingResult.responseCode == BillingClient.BillingResponseCode.USER_CANCELED) {
                    Log.d(TAG, "User canceled the purchase.")
                } else {
                    Log.e(TAG, "Billing error: ${billingResult.debugMessage}")
                }
            }

        // IMPORTANT for PBL 8: enablePendingPurchases(PendingPurchasesParams(...))
        billingClient = BillingClient.newBuilder(this)
            .enablePendingPurchases(
                PendingPurchasesParams.newBuilder()
                    .enableOneTimeProducts()
                    .build()
            )
            .enableAutoServiceReconnection() // optional but reduces manual reconnect code in PBL 8
            .setListener(purchasesUpdatedListener)
            .build()

        billingClient.startConnection(object : BillingClientStateListener {
            override fun onBillingSetupFinished(billingResult: BillingResult) {
                if (billingResult.responseCode == BillingClient.BillingResponseCode.OK) {
                    Log.d(TAG, "Billing Client Connected")
                    queryProductDetails()
                    queryPurchases()
                } else {
                    Log.e(TAG, "Billing Client connection failure: ${billingResult.debugMessage}")
                }
            }
            override fun onBillingServiceDisconnected() {
                Log.d(TAG, "Billing Client Disconnected")
            }
        })
    }

    private fun queryProductDetails() {
        val productList = listOf(
            QueryProductDetailsParams.Product.newBuilder()
                .setProductId(PRODUCT_ID)
                .setProductType(BillingClient.ProductType.INAPP)
                .build()
        )

        val params = QueryProductDetailsParams.newBuilder()
            .setProductList(productList)
            .build()

        // PBL 8: ProductDetailsResponseListener returns QueryProductDetailsResult
        billingClient.queryProductDetailsAsync(
            params,
            ProductDetailsResponseListener { billingResult: BillingResult, result: QueryProductDetailsResult ->
                if (billingResult.responseCode == BillingClient.BillingResponseCode.OK) {
                    val list = result.productDetailsList
                    if (!list.isNullOrEmpty()) {
                        adRemovalProductDetails = list.firstOrNull()
                        Log.d(TAG, "Product details queried: ${adRemovalProductDetails?.name}")
                    } else {
                        val unfetched = result.unfetchedProductList
                        Log.e(TAG, "No ProductDetails returned. Unfetched: $unfetched")
                    }
                } else {
                    Log.e(TAG, "Failed to query product details: ${billingResult.debugMessage}")
                }
            }
        )
    }

    private fun launchPurchaseFlow() {
        adRemovalProductDetails?.let { productDetails ->
            val productDetailsParamsList = listOf(
                BillingFlowParams.ProductDetailsParams.newBuilder()
                    .setProductDetails(productDetails)
                    .build()
            )
            val billingFlowParams = BillingFlowParams.newBuilder()
                .setProductDetailsParamsList(productDetailsParamsList)
                .build()
            billingClient.launchBillingFlow(this, billingFlowParams)
        } ?: run {
            Toast.makeText(this, "Unable to start purchase. Please try again later.", Toast.LENGTH_SHORT).show()
            Log.e(TAG, "Ad removal product details not found.")
        }
    }

    private fun handlePurchase(purchase: Purchase) {
        when (purchase.purchaseState) {
            Purchase.PurchaseState.PURCHASED -> {
                if (!purchase.isAcknowledged) {
                    val acknowledgePurchaseParams = AcknowledgePurchaseParams.newBuilder()
                        .setPurchaseToken(purchase.purchaseToken)
                        .build()
                    billingClient.acknowledgePurchase(acknowledgePurchaseParams) { billingResult ->
                        if (billingResult.responseCode == BillingClient.BillingResponseCode.OK) {
                            grantAdFreeAccess()
                        } else {
                            Log.e(TAG, "Error acknowledging purchase: ${billingResult.debugMessage}")
                        }
                    }
                } else {
                    grantAdFreeAccess()
                }
            }
            Purchase.PurchaseState.PENDING -> {
                // Do not grant entitlement yet
                Toast.makeText(this, "Purchase pending... we'll unlock ad-free when it completes.", Toast.LENGTH_LONG).show()
                Log.d(TAG, "Purchase is pending.")
            }
            Purchase.PurchaseState.UNSPECIFIED_STATE -> {
                Log.w(TAG, "Purchase state UNSPECIFIED_STATE")
            }
        }
    }

    private fun queryPurchases() {
        val params = QueryPurchasesParams.newBuilder()
            .setProductType(BillingClient.ProductType.INAPP)

        billingClient.queryPurchasesAsync(params.build()) { billingResult, purchases ->
            if (billingResult.responseCode == BillingClient.BillingResponseCode.OK && purchases.isNotEmpty()) {
                for (purchase in purchases) {
                    if (purchase.products.contains(PRODUCT_ID) && purchase.purchaseState == Purchase.PurchaseState.PURCHASED) {
                        grantAdFreeAccess()
                        break
                    }
                }
            }
        }
    }

    private fun grantAdFreeAccess() {
        lifecycleScope.launch {
            isAdFree = true
            getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE).edit {
                putBoolean(PREF_AD_FREE, true)
            }
            nativeAd?.destroy()
            nativeAd = null
            isAdVisible = false
            Toast.makeText(applicationContext, "Ads removed!", Toast.LENGTH_SHORT).show()
        }
    }

    private fun setupSoundPool() {
        val audioAttributes = AudioAttributes.Builder()
            .setUsage(AudioAttributes.USAGE_ASSISTANCE_SONIFICATION)
            .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
            .build()
        soundPool = SoundPool.Builder()
            .setMaxStreams(4)
            .setAudioAttributes(audioAttributes)
            .build()
        var loadedCount = 0
        val totalSounds = 4
        soundPool.setOnLoadCompleteListener { _, _, status ->
            if (status == 0) {
                loadedCount++
                if (loadedCount == totalSounds) {
                    lifecycleScope.launch {
                        soundsLoaded = true
                        Log.d(TAG, "All sounds loaded successfully.")
                    }
                }
            } else {
                Log.e(TAG, "Error loading sound, status: $status")
            }
        }
        soundUp = soundPool.load(this, R.raw.up, 1)
        soundDown = soundPool.load(this, R.raw.down, 1)
        soundIntune = soundPool.load(this, R.raw.intune, 1)
        soundTick = soundPool.load(this, R.raw.metronome_tick, 1)
    }

    override fun onStop() { super.onStop(); stopMetronome() }

    override fun onDestroy() {
        super.onDestroy()
        nativeAd?.destroy()
        soundPool.release()
        dispatcher?.stop()
    }

    private fun requestPermissionAndStartTuner() {
        when {
            ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED -> {
                lifecycleScope.launch { startTuner() }
            }
            else -> {
                ActivityCompat.requestPermissions(this, arrayOf(Manifest.permission.RECORD_AUDIO), REQUEST_RECORD_AUDIO_PERMISSION)
            }
        }
    }

    @Suppress("DEPRECATION")
    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQUEST_RECORD_AUDIO_PERMISSION) {
            if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                lifecycleScope.launch { startTuner() }
            } else {
                statusText = "Permission Denied"
                statusColor = Color.Red
                Toast.makeText(this, "Microphone permission is required for the tuner to work.", Toast.LENGTH_LONG).show()
            }
        }
    }

    private suspend fun startTuner() {
        if (isRecording) return
        try {
            dispatcher = withContext(Dispatchers.IO) {
                AudioDispatcherFactory.fromDefaultMicrophone(SAMPLE_RATE, AUDIO_BUFFER_SIZE, BUFFER_OVERLAP)
            }
            val pitchDetectionHandler = PitchDetectionHandler { result, _ ->
                if(result.isPitched && result.probability > CONFIDENCE_THRESHOLD) {
                    lifecycleScope.launch { updatePitch(result.pitch) }
                }
            }
            val pitchProcessor = PitchProcessor(PitchProcessor.PitchEstimationAlgorithm.YIN, SAMPLE_RATE.toFloat(), AUDIO_BUFFER_SIZE, pitchDetectionHandler)

            val processingProcessor = object: AudioProcessor {
                val fft = FFT(AUDIO_BUFFER_SIZE)
                override fun process(audioEvent: AudioEvent): Boolean {
                    val audioBuffer = audioEvent.floatBuffer.clone()
                    lifecycleScope.launch {
                        val transformBuffer = audioBuffer.clone()
                        val magnitudesDest = FloatArray(transformBuffer.size / 2)
                        fft.forwardTransform(transformBuffer)
                        fft.modulus(transformBuffer, magnitudesDest)
                        magnitudes = magnitudesDest
                        val newList = scrollingWaveformData.toMutableList()
                        newList.addAll(audioBuffer.toList())
                        while (newList.size > SCROLLING_WAVEFORM_MAX_SIZE) {
                            newList.removeAt(0)
                        }
                        scrollingWaveformData = newList
                    }
                    return true
                }
                override fun processingFinished() {}
            }
            dispatcher?.addAudioProcessor(HighPass(60f, SAMPLE_RATE.toFloat()))
            dispatcher?.addAudioProcessor(LowPassFS(1500f, SAMPLE_RATE.toFloat()))
            dispatcher?.addAudioProcessor(pitchProcessor)
            dispatcher?.addAudioProcessor(processingProcessor)

            audioThread = Thread(dispatcher, "AudioDispatcherThread").apply { isDaemon = true; start() }
            isRecording = true
            statusText = "Listening..."
            statusColor = Color.White
        } catch (e: Exception) {
            Log.e(TAG, "Error starting tuner", e)
            isRecording = false
            statusText = "Tuner Error"
            statusColor = Color.Red
            if (e is IllegalStateException) {
                Toast.makeText(this, "Microphone might be in use by another app.", Toast.LENGTH_LONG).show()
            }
        }
    }

    private fun stopTuner() {
        dispatcher?.stop()
        audioThread?.interrupt()
        isRecording = false
        cents = 0f
        rotationAngle = 0f
        pitchBuffer.clear()
        detectedNote = "--"
        frequencyText = "0.00 Hz"
        statusText = "Press Start to Tune"
        statusColor = Color.White
        magnitudes = floatArrayOf()
        scrollingWaveformData = emptyList()
    }

    private fun updatePitch(pitch: Float) {
        if (!isRecording) return
        pitchBuffer.add(pitch)
        if (pitchBuffer.size < PITCH_BUFFER_SIZE) return
        val stablePitch = pitchBuffer.sorted()[PITCH_BUFFER_SIZE / 2]
        pitchBuffer.removeAt(0)
        val nearestNote = getNearestNoteFrequency(stablePitch)
        if (nearestNote != null) {
            val (noteFreq, noteName) = nearestNote
            cents = 1200f * log2(stablePitch / noteFreq)
            rotationAngle = (cents.coerceIn(-50f, 50f) / 50f) * 90f
            detectedNote = noteName
            frequencyText = String.format(Locale.US, "%.2f Hz", stablePitch)
            val isInTune = abs(cents) <= IN_TUNE_CENTS_THRESHOLD
            if(isInTune) {
                statusText = "$noteName (In Tune)"
                statusColor = Color.Green
                if(inTuneStartTime == 0L) inTuneStartTime = System.currentTimeMillis()
                if(System.currentTimeMillis() - inTuneStartTime >= IN_TUNE_DELAY_MS && !inTuneSoundPlayed) {
                    playFeedbackSound(soundIntune)
                    inTuneSoundPlayed = true
                }
            } else {
                inTuneStartTime = 0L
                inTuneSoundPlayed = false
                if(cents < 0) {
                    statusText = "$noteName (Tune Up)"
                    playFeedbackSound(soundUp)
                } else {
                    statusText = "$noteName (Tune Down)"
                    playFeedbackSound(soundDown)
                }
                statusColor = Color(0xFFFFA000)
            }
        }
    }

    private fun playFeedbackSound(soundId: Int) {
        if (!soundsLoaded) return
        val now = System.currentTimeMillis()
        val cooldown = if(soundId == soundIntune) 0 else 1500
        if (voiceModeEnabled && isRecording && now - lastFeedbackTime > cooldown) {
            if (soundId != 0) {
                soundPool.play(soundId, 1f, 1f, 1, 0, 1f)
                lastFeedbackTime = now
            }
        }
    }

    private fun startMetronome() {
        if(isMetronomeRunning || !soundsLoaded) return
        isMetronomeRunning = true
        metronomeJob = lifecycleScope.launch(Dispatchers.Default) {
            while(isActive) {
                withContext(Dispatchers.Main) {
                    soundPool.play(soundTick, 1f, 1f, 0, 0, 1f)
                }
                val delayMillis = 60_000L / tempo
                delay(delayMillis)
            }
        }
    }

    private fun stopMetronome() {
        metronomeJob?.cancel()
        isMetronomeRunning = false
    }

    private fun getNearestNoteFrequency(pitch: Float): Pair<Float, String>? =
        noteFrequencies.minByOrNull { abs(pitch - it.first) }

    // --- Crash-proof skin change ---
    private fun randomizeSkins() {
        val wasRecording = isRecording
        if (wasRecording) {
            stopTuner()
        }

        val newPedal = pedalImages.random()
        val newVdu = vduImages.random()
        selectedPedal = newPedal
        selectedVDU = newVdu

        getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE).edit {
            putInt(PREF_PEDAL_SKIN, newPedal)
            putInt(PREF_VDU_SKIN, newVdu)
        }

        if (wasRecording) {
            lifecycleScope.launch {
                delay(100)
                startTuner()
            }
        }
    }

    @Composable
    fun BottomControls() {
        Column(
            modifier = Modifier
                .fillMaxWidth()
                .padding(16.dp),
            horizontalAlignment = Alignment.CenterHorizontally
        ) {
            VisualizerDisplay()
            Spacer(modifier = Modifier.height(16.dp))
            Row(
                modifier = Modifier.fillMaxWidth(),
                horizontalArrangement = Arrangement.SpaceEvenly,
                verticalAlignment = Alignment.CenterVertically
            ) {
                Text(
                    text = "Note: $detectedNote",
                    color = Color.White,
                    fontSize = 18.sp,
                    fontWeight = FontWeight.Bold,
                    style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 8f)),
                    maxLines = 1,
                    overflow = TextOverflow.Ellipsis
                )
                Text(
                    text = frequencyText,
                    fontSize = 14.sp,
                    color = Color.LightGray,
                    style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 6f)),
                    maxLines = 1,
                    overflow = TextOverflow.Ellipsis
                )
                Text(
                    text = statusText,
                    fontSize = 16.sp,
                    color = statusColor,
                    style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 8f)),
                    maxLines = 1,
                    overflow = TextOverflow.Ellipsis
                )
            }
            Spacer(modifier = Modifier.height(16.dp))
            nativeAd?.let { ad ->
                AnimatedVisibility(
                    visible = isAdVisible && !isAdFree,
                    enter = slideInVertically(initialOffsetY = { it / 2 }, animationSpec = tween(durationMillis = 500)) + fadeIn(animationSpec = tween(durationMillis = 500))
                ) {
                    NativeAdView(ad = ad)
                }
            }
        }
    }

    @Composable
    fun MetronomeControls(enabled: Boolean) {
        Surface(
            shape = RoundedCornerShape(12.dp),
            color = Color.Black.copy(alpha = 0.7f),
            border = BorderStroke(1.dp, Color.Gray.copy(alpha = 0.5f))
        ) {
            Row(
                modifier = Modifier.height(48.dp).padding(horizontal = 8.dp),
                horizontalArrangement = Arrangement.Center,
                verticalAlignment = Alignment.CenterVertically
            ) {
                IconButton(onClick = { if (tempo > 40) tempo-- }, enabled = enabled) {
                    Icon(Icons.AutoMirrored.Filled.KeyboardArrowLeft, "", tint = Color.White)
                }
                Text(
                    "$tempo BPM",
                    color = Color.White,
                    fontWeight = FontWeight.SemiBold,
                    fontSize = 14.sp,
                    modifier = Modifier.width(80.dp),
                    textAlign = TextAlign.Center
                )
                IconButton(onClick = { if (tempo < 240) tempo++ }, enabled = enabled) {
                    Icon(Icons.AutoMirrored.Filled.KeyboardArrowRight, "", tint = Color.White)
                }
                Spacer(Modifier.width(4.dp))
                HorizontalDivider(modifier = Modifier.height(24.dp).width(1.dp), color = Color.Gray)
                Spacer(Modifier.width(4.dp))
                IconButton(onClick = { timeSignatureIndex = (timeSignatureIndex - 1 + timeSignatures.size) % timeSignatures.size }, enabled = enabled) {
                    Icon(Icons.AutoMirrored.Filled.KeyboardArrowLeft, "", tint = Color.White)
                }
                Text(
                    timeSignatures[timeSignatureIndex],
                    color = Color.White,
                    fontWeight = FontWeight.SemiBold,
                    fontSize = 14.sp,
                    modifier = Modifier.width(40.dp),
                    textAlign = TextAlign.Center
                )
                IconButton(onClick = { timeSignatureIndex = (timeSignatureIndex + 1) % timeSignatures.size }, enabled = enabled) {
                    Icon(Icons.AutoMirrored.Filled.KeyboardArrowRight, "", tint = Color.White)
                }
                Spacer(modifier = Modifier.width(8.dp))
                Button(
                    onClick = { if (isMetronomeRunning) stopMetronome() else startMetronome() },
                    enabled = enabled,
                    modifier = Modifier.fillMaxHeight(0.75f),
                    contentPadding = PaddingValues(horizontal = 10.dp),
                    colors = ButtonDefaults.buttonColors(
                        containerColor = if (isMetronomeRunning) Color(0xFFE53935) else Color(0xFF43A047)
                    )
                ) {}
            }
        }
    }

    @Composable
    fun VisualizerToggleButton() {
        Button(
            onClick = {
                val allModes = VisualizerMode.entries.toTypedArray()
                visualizerMode = allModes[(allModes.indexOf(visualizerMode) + 1) % allModes.size]
            },
            colors = ButtonDefaults.buttonColors(containerColor = Color.Black, contentColor = Color.White)
        ) {
            val vizName = when(visualizerMode) {
                VisualizerMode.WAVEFORM -> "Wave"
                VisualizerMode.BARS -> "Bars"
                VisualizerMode.NONE -> "Off"
            }
            Text("Visualizer: $vizName")
        }
    }

    @Composable
    fun VisualizerDisplay() {
        Box(
            modifier = Modifier
                .fillMaxWidth(0.9f)
                .height(80.dp)
                .background(Color.Black.copy(alpha = 0.6f), RoundedCornerShape(8.dp))
                .clip(RoundedCornerShape(8.dp))
                .padding(8.dp),
            contentAlignment = Alignment.Center
        ){
            when(visualizerMode){
                VisualizerMode.BARS->BarsVisualizer(Modifier.fillMaxSize(), magnitudes)
                VisualizerMode.WAVEFORM->WaveformVisualizer(Modifier.fillMaxSize(), scrollingWaveformData)
                VisualizerMode.NONE->{ Text("No Visualizer", color=Color.Gray, fontSize=12.sp) }
            }
        }
    }

    @Composable
    fun BarsVisualizer(modifier: Modifier = Modifier, magnitudes: FloatArray) {
        Canvas(modifier = modifier) {
            if (magnitudes.isNotEmpty()) {
                val barCount = 64
                if (barCount == 0) return@Canvas
                val barWidth = size.width / barCount
                val barSpacing = 1.dp.toPx()
                val relevantMagnitudes = magnitudes.take(barCount)
                val maxMagnitude = (relevantMagnitudes.maxOrNull() ?: 1f).coerceAtLeast(1.0f)
                relevantMagnitudes.forEachIndexed { index, mag ->
                    val normalizedHeight = (mag / maxMagnitude).coerceIn(0f, 1f)
                    val barHeight = normalizedHeight * size.height
                    val color = lerp(Color.Green, Color.Red, normalizedHeight)
                    drawRect(
                        color = color,
                        topLeft = Offset(x = index * barWidth, y = size.height - barHeight),
                        size = Size(width = (barWidth - barSpacing).coerceAtLeast(0f), height = barHeight)
                    )
                }
            }
        }
    }

    @Composable
    fun WaveformVisualizer(modifier: Modifier = Modifier, fullData: List<Float>) {
        Canvas(modifier = modifier) {
            val samplesToDisplay = 4096
            if (fullData.isEmpty()) return@Canvas
            val waveformSlice = fullData.takeLast(samplesToDisplay)
            val displayData = if (waveformSlice.size < samplesToDisplay) {
                List(samplesToDisplay - waveformSlice.size) { 0f } + waveformSlice
            } else { waveformSlice }
            val stepX = size.width / displayData.size
            val centerY = size.height / 2f
            val waveColor = Color(0xFF4CAF50)
            val centerLineColor = Color.Black.copy(alpha = 0.3f)
            val topPath = Path().apply {
                moveTo(0f, centerY)
                displayData.forEachIndexed { index, value ->
                    lineTo(index * stepX, centerY - (value.coerceAtLeast(0f) * centerY))
                }
                lineTo(size.width, centerY); close()
            }
            val bottomPath = Path().apply {
                moveTo(0f, centerY)
                displayData.forEachIndexed { index, value ->
                    lineTo(index * stepX, centerY - (value.coerceAtMost(0f) * centerY))
                }
                lineTo(size.width, centerY); close()
            }
            drawPath(path = topPath, color = waveColor)
            drawPath(path = bottomPath, color = waveColor)
            drawLine(
                color = centerLineColor,
                start = Offset(0f, centerY),
                end = Offset(size.width, centerY),
                strokeWidth = 1.dp.toPx()
            )
        }
    }

    @Composable
    fun LedTuningStrip(activeLedIndex:Int) {
        Row(
            modifier = Modifier.shadow(elevation=8.dp, shape=RoundedCornerShape(6.dp), spotColor=Color.Green),
            horizontalArrangement=Arrangement.Center,
            verticalAlignment=Alignment.CenterVertically
        ){
            (-5..5).forEach{ index ->
                val isActive = when {
                    activeLedIndex < 0 -> index in activeLedIndex until 0
                    activeLedIndex > 0 -> index in 1..activeLedIndex
                    else -> index == 0
                }
                val color = when {
                    index == 0 -> Color(0xFF00C853)
                    abs(index) in 1..2 -> Color(0xFFFFFF00)
                    else -> Color(0xFFD50000)
                }
                LedIndicator(isActive = isActive, activeColor = color)
                if (index < 5) { Spacer(modifier = Modifier.width(2.dp)) }
            }
        }
    }

    @Composable
    fun LedIndicator(isActive:Boolean, activeColor:Color) {
        val color = if(isActive) activeColor else Color.DarkGray.copy(alpha=0.5f)
        Box(
            modifier = Modifier
                .size(width=20.dp, height=24.dp)
                .background(color, shape=RoundedCornerShape(4.dp))
                .border(width=1.dp, color=Color.Black.copy(alpha=0.3f), shape=RoundedCornerShape(4.dp))
        )
    }
}

@Composable
fun NativeAdView(ad: NativeAd) {
    AndroidView(
        modifier = Modifier.fillMaxWidth().padding(vertical = 8.dp),
        factory = { context ->
            val adView = LayoutInflater.from(context).inflate(R.layout.ad_unified, null) as NativeAdView
            adView
        },
        update = { adView ->
            adView.headlineView = adView.findViewById(R.id.ad_headline)
            adView.bodyView = adView.findViewById(R.id.ad_body)
            adView.callToActionView = adView.findViewById(R.id.ad_call_to_action)
            adView.iconView = adView.findViewById(R.id.ad_app_icon)
            (adView.headlineView as? TextView)?.text = ad.headline
            (adView.bodyView as? TextView)?.text = ad.body
            (adView.callToActionView as? Button)?.text = ad.callToAction
            (adView.iconView as? ImageView)?.setImageDrawable(ad.icon?.drawable)
            adView.setNativeAd(ad)
        }
    )
}
