plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
    id("org.jetbrains.kotlin.plugin.compose")
}

android {
    namespace = "co.uk.doverguitarteacher.voiceguitartuner" // Your package name
    compileSdk = 36 // Or your project's compileSdk

    defaultConfig {
        applicationId = "co.uk.doverguitarteacher.voiceguitartuner" // Your package name
        minSdk = 24 // Or your project's minSdk
        targetSdk = 36 // Or your project's targetSdk
        versionCode = 18
        versionName = "1"

        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        vectorDrawables {
            useSupportLibrary = true
        }
    }

    buildTypes {
        release {
            isMinifyEnabled = true

            // Enables resource shrinking.
            isShrinkResources = true
            proguardFiles(
                getDefaultProguardFile("proguard-android-optimize.txt"),
                "proguard-rules.pro"
            )
            // CORRECTED: Use double quotes for the String in Kotlin DSL
            ndk.debugSymbolLevel = "FULL"
        }
    }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_1_8
        targetCompatibility = JavaVersion.VERSION_1_8
    }
    kotlinOptions {
        jvmTarget = "1.8"
    }
    buildFeatures {
        compose = true // Enable Jetpack Compose
    }
    composeOptions {
        kotlinCompilerExtensionVersion = "1.5.3" // Check for the version compatible with your Kotlin and Compose versions
    }
    packaging { // For TarsosDSP to avoid packaging issues
        resources {
            excludes += "/META-INF/{AL2.0,LGPL2.1}"
            excludes += "META-INF/LICENSE.txt" // Common TarsosDSP exclusion
            excludes += "META-INF/NOTICE.txt"  // Common TarsosDSP exclusion
        }
    }
}

dependencies {
    implementation("com.google.android.play:review-ktx:2.0.1")
    implementation("com.android.billingclient:billing-ktx:8.0.0")
    implementation("com.google.android.gms:play-services-ads:24.5.0")
    implementation("androidx.core:core-ktx:1.16.0")
    implementation("androidx.lifecycle:lifecycle-runtime-ktx:2.9.2")

    // Jetpack Compose BOM (Bill of Materials) - Let this manage versions
    implementation(platform("androidx.compose:compose-bom:2025.07.00")) // Use platform() for BOM
    implementation("androidx.compose.ui:ui")
    implementation("androidx.compose.ui:ui-graphics")
    implementation("androidx.compose.ui:ui-tooling-preview")
    implementation("androidx.compose.material3:material3-window-size-class")
    implementation("androidx.compose.material3:material3")
    implementation("androidx.compose.material:material-icons-extended")
    implementation("androidx.activity:activity-compose") // No version needed

    // Your other dependencies
    implementation(files("libs/TarsosDSP.jar"))
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-android:1.10.2")



    // Test dependencies
    testImplementation("junit:junit:4.13.2")
    androidTestImplementation("androidx.test.ext:junit:1.2.1")
    androidTestImplementation("androidx.test.espresso:espresso-core:3.6.1") // Aligned version
    androidTestImplementation(platform("androidx.compose:compose-bom:2025.07.00")) // BOM for tests
    androidTestImplementation("androidx.compose.ui:ui-test-junit4")

    // Debug dependencies
    debugImplementation("androidx.compose.ui:ui-tooling")
    debugImplementation("androidx.compose.ui:ui-test-manifest")
}
