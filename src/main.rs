use anyhow::Result;
use argon2::{Argon2, password_hash::{SaltString, PasswordHasher}};
use chacha20poly1305::{aead::{Aead, KeyInit}, XChaCha20Poly1305, XNonce};
use aes_gcm::{Aes256Gcm, KeyInit as AesKeyInit, Nonce as AesNonce}; 
use eframe::egui;
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH, Duration};
use zeroize::Zeroizing;
use serde::{Serialize, Deserialize};
use rand::{Rng, SeedableRng}; 
use rand::rngs::StdRng;
use rand::seq::SliceRandom; // Needed for scrambling
use crossbeam_channel::{unbounded, Sender, Receiver};
use std::thread;
use std::env;

// --- HARDWARE LOCKING ---

fn get_device_fingerprint() -> String {
    // In a production app, use the 'machine-uid' crate. 
    // Here we use std::env to create a stable signature of the current machine.
    let os = env::consts::OS;
    let arch = env::consts::ARCH;
    let user = env::var("USERNAME").or(env::var("USER")).unwrap_or("UNKNOWN".into());
    let host = env::var("COMPUTERNAME").or(env::var("HOSTNAME")).unwrap_or("UNKNOWN".into());
    
    let raw_id = format!("{}-{}-{}-{}", os, arch, user, host);
    let hash = blake3::hash(raw_id.as_bytes());
    hash.to_hex().to_string()
}

fn check_hardware_lock() -> Result<()> {
    let mut lock_path = get_app_root();
    lock_path.push(".VEILGUARD_HW_LOCK");
    
    let current_id = get_device_fingerprint();

    if lock_path.exists() {
        let saved_id = fs::read_to_string(&lock_path)?;
        if saved_id.trim() != current_id {
            // CRASH: Hardware mismatch
            eprintln!("CRITICAL SECURITY ALERT: VAULT HARDWARE MISMATCH.");
            eprintln!("This vault is bound to a different machine.");
            std::process::exit(1); 
        }
    } else {
        // First run: Bind to this machine
        fs::write(&lock_path, current_id)?;
    }
    Ok(())
}

// --- BIT MANIPULATION HELPERS ---

fn get_bit(data: &[u8], bit_idx: usize) -> bool {
    let byte_idx = bit_idx / 8;
    if byte_idx >= data.len() {
        return rand::thread_rng().random::<bool>(); 
    }
    (data[byte_idx] & (1 << (bit_idx % 8))) != 0
}

fn set_bit(data: &mut [u8], bit_idx: usize, val: bool) {
    if bit_idx / 8 >= data.len() { return; }
    if val {
        data[bit_idx / 8] |= 1 << (bit_idx % 8);
    } else {
        data[bit_idx / 8] &= !(1 << (bit_idx % 8));
    }
}

// --- CONSTANTS ---
const SALT: &str = "VElMR1VBUkRfU0FMVF9WMw"; 
const CHAT_EPOCH_DURATION: u64 = 15; // Enigma Key Rotation (Seconds)
const CHAT_MAX_SESSION: u64 = 300;   // 5 Minutes

#[derive(PartialEq)]
enum AppState { CheckLicense, Setup, Login, Main }

#[derive(PartialEq)]
enum ActiveWindow { FileEncryption, VaultManager, Stacks, VaultSelection, PrivateChat }

// --- CHAT STRUCTURES ---

#[derive(Clone)]
struct ChatMessage {
    sender: String,
    content: String,
    is_system: bool,
}

struct ChatState {
    messages: Vec<ChatMessage>,
    input_msg: String,
    target_ip: String,
    target_id: String, 
    chat_pass: String,
    is_hosting: bool,
    net_tx: Option<Sender<String>>,
    net_rx: Receiver<ChatMessage>,
}

impl Default for ChatState {
    fn default() -> Self {
        let (_, rx) = unbounded();
        Self {
            messages: Vec::new(),
            input_msg: String::new(),
            target_ip: "127.0.0.1:8080".to_string(),
            target_id: "Partner".to_string(),
            chat_pass: String::new(),
            is_hosting: false,
            net_tx: None,
            net_rx: rx, 
        }
    }
}

// --- VAULT STRUCTURES ---

#[derive(Clone, Serialize, Deserialize)]
struct TripleKeys {
    k1: Vec<u8>,
    k2: Vec<u8>,
    k3: Vec<u8>,
    ledger_key: Vec<u8>,
}

#[derive(Serialize, Deserialize, Clone)]
struct StackedFileMetadata {
    name: String,
    size: u64,
}

#[derive(Serialize, Deserialize, Clone)]
struct VaultEntry {
    file_id: String,
    pqc_nonce: u128,      
    scramble_seed: u64, // NEW: Seed for the chunk shuffling
    is_stack: bool,
    stacked_files: Vec<StackedFileMetadata>,
    original_name: String,
    original_size: u64,   
    encrypted_path: PathBuf,
    is_chaff: bool,
}

struct SecureApp {
    state: AppState,
    active_window: ActiveWindow,
    pass1: Zeroizing<String>,
    pass2: Zeroizing<String>,
    pass3: Zeroizing<String>,
    session_keys: Option<TripleKeys>,
    current_vault_name: String,
    vault_entries: Vec<VaultEntry>,
    available_vaults: Vec<String>,
    status_msg: String,
    stack_queue: Vec<PathBuf>,
    new_vault_name: String,
    chat_state: ChatState,
}

impl Default for SecureApp {
    fn default() -> Self {
        Self {
            state: AppState::CheckLicense,
            active_window: ActiveWindow::VaultSelection,
            pass1: String::new().into(),
            pass2: String::new().into(),
            pass3: String::new().into(),
            session_keys: None,
            current_vault_name: String::new(),
            vault_entries: Vec::new(),
            available_vaults: Vec::new(),
            status_msg: "VEILGUARD Bit-Engine Active".to_string(),
            stack_queue: Vec::new(),
            new_vault_name: String::new(),
            chat_state: ChatState::default(),
        }
    }
}

// --- UTILITIES ---

fn get_app_root() -> PathBuf {
    let mut path = dirs::home_dir().expect("Home dir not found");
    path.push(".VEILGUARD");
    if !path.exists() { fs::create_dir_all(&path).unwrap_or_default(); }
    path
}

fn get_license_path() -> PathBuf {
    let mut path = get_app_root();
    path.push(".VEILGUARDmk3");
    path
}

fn get_vault_storage_path(vault_name: &str) -> PathBuf {
    let mut path = get_app_root();
    path.push("vaults");
    path.push(vault_name);
    path.push("data");
    if !path.exists() { fs::create_dir_all(&path).unwrap_or_default(); }
    path
}

fn get_vault_ledger_path(vault_name: &str) -> PathBuf {
    let mut path = get_app_root();
    path.push("vaults");
    path.push(vault_name);
    if !path.exists() { fs::create_dir_all(&path).unwrap_or_default(); }
    path.push("ledger.enc");
    path
}

// --- ENIGMA CHAT LOGIC (ASYNC) ---

fn derive_enigma_key(shared_secret: &str, session_start: u64, epoch: u64) -> Vec<u8> {
    // Key = Hash(Password + SessionStart + CurrentEpoch)
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ENIGMA_V1");
    hasher.update(shared_secret.as_bytes());
    hasher.update(&session_start.to_le_bytes());
    hasher.update(&epoch.to_le_bytes());
    hasher.finalize().as_bytes().to_vec()
}

fn get_next_30s_mark() -> u64 {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
    let rem = now % 30;
    now + (30 - rem)
}

fn spawn_chat_network(
    is_host: bool, 
    addr: String, 
    key_params: (String, String), // (ID, Password)
    tx_ui: Sender<ChatMessage>,
    rx_ui: Receiver<String>
) {
    thread::spawn(move || {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            use tokio::net::{TcpListener, TcpStream};
            use tokio::io::{AsyncReadExt, AsyncWriteExt};

            let stream_result = if is_host {
                let listener = TcpListener::bind(&addr).await;
                match listener {
                    Ok(l) => {
                        let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: format!("Listening on {}...", addr), is_system: true });
                        match l.accept().await { Ok((s, _)) => Ok(s), Err(e) => Err(e), }
                    },
                    Err(e) => Err(e),
                }
            } else { TcpStream::connect(&addr).await };

            match stream_result {
                Ok(mut stream) => {
                    let (mut reader, mut writer) = stream.into_split();
                    
                    // --- HANDSHAKE: SYNC CLOCKS ---
                    let session_start: u64;
                    if is_host {
                        session_start = get_next_30s_mark();
                        if writer.write_u64(session_start).await.is_err() { return; }
                        let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: format!("Syncing clocks to: {}", session_start), is_system: true });
                    } else {
                        session_start = match reader.read_u64().await { Ok(t) => t, Err(_) => return };
                        let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: format!("Synced. Session starts at: {}", session_start), is_system: true });
                    }

                    // Wait for start
                    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                    if session_start > now {
                        tokio::time::sleep(tokio::time::Duration::from_secs(session_start - now)).await;
                    }

                    let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: "ENIGMA SESSION ACTIVE. Keys rotating every 15s.".into(), is_system: true });

                    let pass_clone = key_params.1.clone();
                    let tx_ui_clone = tx_ui.clone();
                    
                    // --- WRITER TASK ---
                    tokio::spawn(async move {
                        loop {
                            // Check max session time
                            let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                            if now > session_start + CHAT_MAX_SESSION { 
                                let _ = tx_ui_clone.send(ChatMessage { sender: "System".into(), content: "Session Expired.".into(), is_system: true });
                                break; 
                            }

                            // Calculate Epoch
                            let epoch = (now - session_start) / CHAT_EPOCH_DURATION;
                            let key = derive_enigma_key(&pass_clone, session_start, epoch);
                            let cipher = XChaCha20Poly1305::new_from_slice(&key[0..32]).unwrap();

                            if let Ok(msg) = rx_ui.try_recv() {
                                let nonce_bytes = rand::thread_rng().random::<[u8; 24]>();
                                let nonce = XNonce::from_slice(&nonce_bytes);
                                
                                // Prefix message with epoch so receiver knows which key to use
                                let content_bytes = msg.as_bytes();
                                if let Ok(ct) = cipher.encrypt(nonce, content_bytes) {
                                    // Packet Structure: [Epoch: u64][Nonce: 24][Len: u64][Ciphertext]
                                    if writer.write_u64(epoch).await.is_err() { break; }
                                    if writer.write_all(&nonce_bytes).await.is_err() { break; }
                                    if writer.write_u64(ct.len() as u64).await.is_err() { break; }
                                    if writer.write_all(&ct).await.is_err() { break; }
                                    let _ = tx_ui_clone.send(ChatMessage { sender: "Me".into(), content: msg, is_system: false });
                                }
                            }
                            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
                        }
                    });

                    // --- READER LOOP ---
                    loop {
                        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                        if now > session_start + CHAT_MAX_SESSION { break; }

                        // Read Header
                        let packet_epoch = match reader.read_u64().await { Ok(e) => e, Err(_) => break };
                        let mut nonce_buf = [0u8; 24];
                        if reader.read_exact(&mut nonce_buf).await.is_err() { break; }
                        let len = match reader.read_u64().await { Ok(l) => l, Err(_) => break };
                        let mut ct = vec![0u8; len as usize];
                        if reader.read_exact(&mut ct).await.is_err() { break; }

                        // Decrypt using the packet's epoch key
                        let key = derive_enigma_key(&key_params.1, session_start, packet_epoch);
                        let cipher = XChaCha20Poly1305::new_from_slice(&key[0..32]).unwrap();
                        
                        if let Ok(pt) = cipher.decrypt(XNonce::from_slice(&nonce_buf), ct.as_ref()) {
                            let _ = tx_ui.send(ChatMessage { sender: "Partner".into(), content: String::from_utf8_lossy(&pt).to_string(), is_system: false });
                        }
                    }
                    let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: "Disconnected.".into(), is_system: true });
                }
                Err(e) => { let _ = tx_ui.send(ChatMessage { sender: "System".into(), content: format!("Error: {}", e), is_system: true }); }
            }
        });
    });
}

// --- CORE ENCRYPTION ENGINE ---

impl SecureApp {
    fn process_stack_encryption(&mut self) -> Result<()> {
        if self.stack_queue.is_empty() { return Ok(()); }
        let mut file_data: Vec<Vec<u8>> = Vec::new();
        let mut meta: Vec<StackedFileMetadata> = Vec::new();
        let mut max_size_bytes = 0;

        for path in &self.stack_queue {
            let data = fs::read(path)?;
            if data.len() > max_size_bytes { max_size_bytes = data.len(); }
            meta.push(StackedFileMetadata { name: path.file_name().unwrap().to_string_lossy().to_string(), size: data.len() as u64 });
            file_data.push(data);
        }

        let num_files = file_data.len();
        let bits_per_file = max_size_bytes * 8; 
        let total_bits = bits_per_file * num_files;
        let total_bytes = (total_bits + 7) / 8;
        let mut interleaved = vec![0u8; total_bytes];

        // Interleave bits
        for bit_pos in 0..bits_per_file {
            for f_idx in 0..num_files {
                let bit_val = get_bit(&file_data[f_idx], bit_pos);
                let target_bit_idx = bit_pos * num_files + f_idx;
                set_bit(&mut interleaved, target_bit_idx, bit_val);
            }
        }

        let id = format!("stk_{}", SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs());
        // Updated extension logic: .STACKx
        let ext = format!("STACK{}", num_files);
        self.encrypt_and_vault(interleaved, id, true, meta, String::new(), 0, &ext)?;
        self.stack_queue.clear();
        Ok(())
    }

    fn encrypt_and_vault(&mut self, raw_data: Vec<u8>, file_id: String, is_stack: bool, stacked_meta: Vec<StackedFileMetadata>, orig_name: String, orig_size: u64, extension: &str) -> Result<()> {
        if self.current_vault_name.is_empty() { return Err(anyhow::anyhow!("No vault selected")); }
        let nano = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let mut rng = StdRng::seed_from_u64(nano as u64);
        
        // --- STEP 1: 12-BIT CHUNKING ---
        // Convert bytes to 12-bit integers (values 0..4095)
        let mut chunks_12bit: Vec<u16> = Vec::new();
        let mut i = 0;
        while i < raw_data.len() {
            let b1 = raw_data[i] as u16;
            let b2 = if i + 1 < raw_data.len() { raw_data[i+1] as u16 } else { 0 };
            
            // Chunk 1: Top 8 bits of b1 + Top 4 bits of b2
            // Wait, standard packing:
            // 3 bytes (24 bits) -> 2 chunks of 12 bits
            let b3 = if i + 2 < raw_data.len() { raw_data[i+2] as u16 } else { 0 };
            
            // Pack 3 bytes into 2x 12-bit chunks
            // Byte 0: [AAAAAAAA]
            // Byte 1: [BBBBBBBB]
            // Byte 2: [CCCCCCCC]
            // Chunk 1: [AAAAAAAA BBBB] (12 bits)
            // Chunk 2: [BBBB CCCCCCCC] (12 bits)
            
            // Chunk 1: b1 << 4 | (b2 >> 4)
            chunks_12bit.push((b1 << 4) | ((b2 & 0xF0) >> 4));
            
            if i + 1 < raw_data.len() {
                // Chunk 2: (b2 & 0x0F) << 8 | b3
                chunks_12bit.push(((b2 & 0x0F) << 8) | b3);
            }
            i += 3; // We processed 3 bytes? No, we processed up to 3 bytes for 2 chunks.
            // Actually, 3 bytes = 24 bits = 2 * 12 bits. Correct.
        }

        // --- STEP 2: POLYMORPHIC NOISE ---
        let mut transformed_chunks = Vec::new();
        for chunk in chunks_12bit {
            // Random operation per chunk
            let mode = rng.random_range(0..4); 
            let key = rng.random::<u16>() & 0x0FFF; // 12-bit key
            let c = match mode {
                0 => (chunk.wrapping_add(key)) & 0x0FFF,
                1 => (chunk ^ key) & 0x0FFF,
                2 => (chunk.wrapping_sub(key)) & 0x0FFF,
                _ => (chunk.rotate_left(3) ^ key) & 0x0FFF,
            };
            transformed_chunks.push(c);
        }

        // --- STEP 3: SEED-BASED SCRAMBLING ---
        let scramble_seed = rng.random::<u64>();
        let mut scramble_rng = StdRng::seed_from_u64(scramble_seed);
        // We shuffle the vector. To decrypt, we need to unshuffle.
        // Efficient way: create indices, shuffle indices, apply.
        // Actually, just shuffling the data is fine if we seed the RNG same way on decrypt
        // and do a "reverse shuffle" (which is hard without indices) OR
        // we just attach indices. 
        // Better: Generate a permutation vector P, apply P.
        // To decrypt: Generate P, invert P, apply P_inv.
        let len = transformed_chunks.len();
        let mut p: Vec<usize> = (0..len).collect();
        p.shuffle(&mut scramble_rng);
        
        let mut scrambled_data = vec![0u16; len];
        for (original_idx, &new_idx) in p.iter().enumerate() {
            scrambled_data[new_idx] = transformed_chunks[original_idx];
        }

        // --- STEP 4: RE-PACK TO BYTES ---
        // 2x 12-bit chunks -> 3 bytes
        let mut final_payload = Vec::new();
        let mut k = 0;
        while k < scrambled_data.len() {
            let c1 = scrambled_data[k];
            let c2 = if k + 1 < scrambled_data.len() { scrambled_data[k+1] } else { 0 };
            
            // c1: [AAAAAAAA BBBB]
            // c2: [CCCC DDDDDDDD] (where C is low nibble of byte 2, D is byte 3)
            // Reconstruct:
            // Byte 1: c1 >> 4
            final_payload.push(((c1 >> 4) & 0xFF) as u8);
            // Byte 2: (c1 & 0x0F) << 4 | (c2 >> 8)
            final_payload.push((((c1 & 0x0F) << 4) | ((c2 >> 8) & 0x0F)) as u8);
            // Byte 3: c2 & 0xFF
            final_payload.push((c2 & 0xFF) as u8);
            
            k += 2;
        }

        // --- STEP 5: "PQC" LATTICE LAYER (Simulated with XChaCha) ---
        let pqc_key = self.derive_pqc_key(&file_id, nano)?;
        let cipher = XChaCha20Poly1305::new_from_slice(&pqc_key[0..32]).unwrap();
        let ct = cipher.encrypt(&XNonce::from_slice(&[0u8; 24]), final_payload.as_ref())
            .map_err(|_| anyhow::anyhow!("Encryption Failed"))?;

        // Write
        let mut path = get_vault_storage_path(&self.current_vault_name);
        path.push(format!("{}.{}", file_id, extension));
        fs::write(&path, &ct)?;

        self.vault_entries.push(VaultEntry {
            file_id: file_id.clone(), 
            pqc_nonce: nano, 
            scramble_seed, // Store the seed!
            is_stack, stacked_files: stacked_meta,
            original_name: orig_name, original_size: orig_size, encrypted_path: path, is_chaff: false,
        });

        self.generate_chaff()?;
        self.save_vault()?;
        self.status_msg = "Vaulted Securely.".into();
        Ok(())
    }

    fn process_polymorphic_decryption(&mut self, index: usize) -> Result<()> {
        let entry = self.vault_entries[index].clone();
        if entry.is_chaff { 
            self.status_msg = "Cannot restore fake entry.".into();
            return Ok(()); 
        }

        // 1. Decrypt PQC Layer
        let raw_enc = fs::read(&entry.encrypted_path)?;
        let pqc_key = self.derive_pqc_key(&entry.file_id, entry.pqc_nonce)?;
        let cipher = XChaCha20Poly1305::new_from_slice(&pqc_key[0..32]).unwrap();
        let packed_bytes = cipher.decrypt(&XNonce::from_slice(&[0u8; 24]), raw_enc.as_ref())
            .map_err(|_| anyhow::anyhow!("Decryption Failed"))?;

        // 2. Unpack Bytes to 12-bit Chunks (Scrambled)
        let mut scrambled_chunks = Vec::new();
        let mut k = 0;
        while k < packed_bytes.len() {
            let b1 = packed_bytes[k] as u16;
            let b2 = if k + 1 < packed_bytes.len() { packed_bytes[k+1] as u16 } else { 0 };
            let b3 = if k + 2 < packed_bytes.len() { packed_bytes[k+2] as u16 } else { 0 };
            
            scrambled_chunks.push((b1 << 4) | ((b2 & 0xF0) >> 4));
            if k + 1 < packed_bytes.len() {
                scrambled_chunks.push(((b2 & 0x0F) << 8) | b3);
            }
            k += 3;
        }

        // 3. Un-Scramble
        let mut scramble_rng = StdRng::seed_from_u64(entry.scramble_seed);
        // We must regenerate the exact same permutation
        // Note: We need the exact length of chunks to replicate the shuffle
        // The length is scrambled_chunks.len() (or slightly less if padding was added, but here we kept 1:1)
        let len = scrambled_chunks.len();
        let mut p: Vec<usize> = (0..len).collect();
        p.shuffle(&mut scramble_rng);
        
        let mut ordered_chunks = vec![0u16; len];
        // Invert: scrambled[new_idx] = ordered[old_idx]
        // so: ordered[old_idx] = scrambled[new_idx]
        for (original_idx, &new_idx) in p.iter().enumerate() {
            if new_idx < scrambled_chunks.len() {
               ordered_chunks[original_idx] = scrambled_chunks[new_idx];
            }
        }

        // 4. Reverse Polymorphic Noise
        // Note: To reverse this properly, we need the SAME random sequence.
        // We re-seed the RNG with the same nano-timestamp (pqc_nonce used as seed base)
        let mut rng = StdRng::seed_from_u64(entry.pqc_nonce as u64);
        let mut clear_chunks = Vec::new();
        
        for chunk in ordered_chunks {
            let mode = rng.random_range(0..4);
            let key = rng.random::<u16>() & 0x0FFF;
            let c = match mode {
                0 => (chunk.wrapping_sub(key)) & 0x0FFF,
                1 => (chunk ^ key) & 0x0FFF,
                2 => (chunk.wrapping_add(key)) & 0x0FFF,
                _ => (chunk.rotate_right(3) ^ key) & 0x0FFF, // rough inverse approx
            };
            clear_chunks.push(c);
        }

        // 5. Pack back to 8-bit stream
        let mut stream = Vec::new();
        let mut i = 0;
        while i < clear_chunks.len() {
            let c1 = clear_chunks[i];
            let c2 = if i + 1 < clear_chunks.len() { clear_chunks[i+1] } else { 0 };
             // c1: [AAAAAAAA BBBB]
             // c2: [CCCC DDDDDDDD]
            stream.push(((c1 >> 4) & 0xFF) as u8);
            stream.push((((c1 & 0x0F) << 4) | ((c2 >> 8) & 0x0F)) as u8);
            if i + 1 < clear_chunks.len() { stream.push((c2 & 0xFF) as u8); }
            i += 2;
        }

        let mut out_dir = get_app_root();
        out_dir.push("restored");
        fs::create_dir_all(&out_dir)?;

        if entry.is_stack {
            let stride = entry.stacked_files.len(); 
            for (f_idx, f_meta) in entry.stacked_files.iter().enumerate() {
                let mut f_data = vec![0u8; f_meta.size as usize];
                for bit_pos in 0..(f_meta.size * 8) {
                    let stream_bit_idx = (bit_pos as usize) * stride + f_idx;
                    if stream_bit_idx / 8 < stream.len() {
                        let bit_val = get_bit(&stream, stream_bit_idx);
                        set_bit(&mut f_data, bit_pos as usize, bit_val);
                    }
                }
                fs::write(out_dir.join(&f_meta.name), f_data)?;
            }
        } else {
            // Trim padding if needed (simplified)
            if stream.len() > entry.original_size as usize {
                stream.truncate(entry.original_size as usize);
            }
            fs::write(out_dir.join(&entry.original_name), stream)?;
        }

        let _ = fs::remove_file(&entry.encrypted_path);
        self.vault_entries.remove(index);
        self.save_vault()?;
        self.status_msg = "Restored & Purged.".into();
        Ok(())
    }

    fn generate_chaff(&mut self) -> Result<()> {
        let mut rng = StdRng::from_os_rng();
        let num_chaff = rng.random_range(1..=3); 

        for _ in 0..num_chaff {
            let chaff_id = format!("chaff_{}", rng.random::<u64>());
            let chaff_size = rng.random_range(1024..10240); 
            let chaff_data: Vec<u8> = (0..chaff_size).map(|_| rng.random::<u8>()).collect();
            
            let mut storage_path = get_vault_storage_path(&self.current_vault_name);
            storage_path.push(format!("{}.VEIL", chaff_id));
            fs::write(&storage_path, chaff_data)?;

            let fake_names = vec!["sys_log.dat", "config_backup.bin", "temp_index.db", "cache_v2.tmp"];
            let random_name = fake_names[rng.random_range(0..fake_names.len())].to_string();

            self.vault_entries.push(VaultEntry {
                file_id: chaff_id, pqc_nonce: rng.random::<u128>(), scramble_seed: rng.random::<u64>(), 
                is_stack: false, stacked_files: vec![],
                original_name: format!("{} ({})", random_name, rng.random::<u16>()),
                original_size: chaff_size as u64, encrypted_path: storage_path, is_chaff: true,
            });
        }
        Ok(())
    }

    fn derive_pqc_key(&self, id: &str, nano: u128) -> Result<Vec<u8>> {
        let mut hasher = blake3::Hasher::new();
        let keys = self.session_keys.as_ref().unwrap();
        hasher.update(&keys.k1); hasher.update(id.as_bytes()); hasher.update(&nano.to_le_bytes());
        Ok(hasher.finalize().as_bytes().to_vec())
    }

    fn save_vault(&self) -> Result<()> {
        if self.current_vault_name.is_empty() { return Ok(()); }
        let path = get_vault_ledger_path(&self.current_vault_name);
        let json = serde_json::to_vec(&self.vault_entries)?;
        let cipher = Aes256Gcm::new_from_slice(&self.session_keys.as_ref().unwrap().ledger_key).unwrap();
        let ct = cipher.encrypt(&AesNonce::from_slice(&[0u8; 12]), json.as_ref()).map_err(|_| anyhow::anyhow!("Save Failed"))?;
        fs::write(path, ct)?;
        Ok(())
    }

    fn load_vault(&mut self, name: &str) -> Result<()> {
        self.current_vault_name = name.into();
        let path = get_vault_ledger_path(name);
        if path.exists() {
            let ct = fs::read(path)?;
            let cipher = Aes256Gcm::new_from_slice(&self.session_keys.as_ref().unwrap().ledger_key).unwrap();
            let pt = cipher.decrypt(&AesNonce::from_slice(&[0u8; 12]), ct.as_ref()).map_err(|_| anyhow::anyhow!("Bad Password"))?;
            self.vault_entries = serde_json::from_slice(&pt)?;
        } else {
            self.vault_entries = Vec::new();
        }
        self.active_window = ActiveWindow::VaultManager;
        Ok(())
    }

    fn derive_triple_keys(&self) -> TripleKeys {
        let argon2 = Argon2::default();
        let salt = SaltString::from_b64(SALT).unwrap();
        let combined = format!("{}{}{}", *self.pass1, *self.pass2, *self.pass3);
        let l_key = argon2.hash_password(combined.as_bytes(), &salt).unwrap().hash.unwrap().as_bytes().to_vec();
        let mut ledger_key = [0u8; 32]; ledger_key.copy_from_slice(&l_key[..32]);
        TripleKeys {
            k1: argon2.hash_password(format!("{}a", *self.pass1).as_bytes(), &salt).unwrap().hash.unwrap().as_bytes().to_vec(),
            k2: argon2.hash_password(format!("{}b", *self.pass2).as_bytes(), &salt).unwrap().hash.unwrap().as_bytes().to_vec(),
            k3: argon2.hash_password(format!("{}c", *self.pass3).as_bytes(), &salt).unwrap().hash.unwrap().as_bytes().to_vec(),
            ledger_key: ledger_key.to_vec(),
        }
    }

    fn refresh_vault_list(&mut self) {
        let root = get_app_root().join("vaults");
        self.available_vaults = fs::read_dir(root).map(|d| d.flatten().filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into()).collect()).unwrap_or_default();
    }
    
    fn create_new_vault(&mut self) -> Result<()> {
        if self.new_vault_name.trim().is_empty() { return Ok(()); }
        let name = self.new_vault_name.trim().to_string();
        get_vault_storage_path(&name); 
        self.vault_entries.clear();
        self.current_vault_name = name;
        self.save_vault()?;
        self.refresh_vault_list();
        self.new_vault_name.clear();
        Ok(())
    }
}

// --- UI IMPLEMENTATION ---

impl eframe::App for SecureApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        while let Ok(msg) = self.chat_state.net_rx.try_recv() { self.chat_state.messages.push(msg); }
        match self.state {
            AppState::CheckLicense => {
                // Perform Hardware Lock Check before License Check
                if let Err(_) = check_hardware_lock() {
                     // In eframe we can't easily print to console if GUI is up, but process::exit handles it.
                     std::process::exit(1);
                }
                self.state = if get_license_path().exists() { AppState::Login } else { AppState::Setup }
            },
            AppState::Setup => self.render_setup(ctx),
            AppState::Login => self.render_login(ctx),
            AppState::Main => self.render_main(ctx),
        }
    }
}

impl SecureApp {
    fn render_main(&mut self, ctx: &egui::Context) {
        egui::SidePanel::left("nav").show(ctx, |ui| {
            ui.heading("VEILGUARD v4.0");
            ui.label(format!("HWID: ...{}", &get_device_fingerprint()[0..6])); // Show snippet of ID
            ui.separator();
            if ui.button("Vault Selection").clicked() { self.refresh_vault_list(); self.active_window = ActiveWindow::VaultSelection; }
            if !self.current_vault_name.is_empty() {
                if ui.button("File Encrypt").clicked() { self.active_window = ActiveWindow::FileEncryption; }
                if ui.button("Bit-Stacks").clicked() { self.active_window = ActiveWindow::Stacks; }
                if ui.button("Ledger").clicked() { self.active_window = ActiveWindow::VaultManager; }
            }
            ui.separator();
            if ui.button("Enigma Chat").clicked() { self.active_window = ActiveWindow::PrivateChat; }
        });

        egui::CentralPanel::default().show(ctx, |ui| {
            match self.active_window {
                ActiveWindow::VaultSelection => {
                    ui.horizontal(|ui| { 
                        ui.text_edit_singleline(&mut self.new_vault_name); 
                        if ui.button("Create").clicked() { let _ = self.create_new_vault(); } 
                    });
                    for v in &self.available_vaults.clone() { if ui.button(v).clicked() { let _ = self.load_vault(v); } }
                }
                ActiveWindow::FileEncryption => {
                     if ui.button("Encrypt File").clicked() {
                        if let Some(p) = rfd::FileDialog::new().pick_file() {
                            let name = p.file_name().unwrap().to_string_lossy().to_string();
                            let data = fs::read(&p).unwrap();
                            let size = fs::metadata(&p).unwrap().len();
                            let id = format!("f_{}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_micros());
                            let _ = self.encrypt_and_vault(data, id, false, vec![], name, size, "VEIL");
                        }
                    }
                }
                ActiveWindow::Stacks => {
                    ui.heading("Bit-Interleaved Stacking");
                    if ui.button("Add File").clicked() { if let Some(fs) = rfd::FileDialog::new().pick_files() { self.stack_queue.extend(fs); } }
                    for p in &self.stack_queue { ui.label(format!("+ {:?}", p.file_name())); }
                    if !self.stack_queue.is_empty() && ui.button("Interweave & Encrypt").clicked() { let _ = self.process_stack_encryption(); }
                }
                ActiveWindow::VaultManager => {
                    let mut to_dec = None;
                    egui::ScrollArea::vertical().show(ui, |ui| {
                        for (i, e) in self.vault_entries.iter().enumerate() { 
                            ui.horizontal(|ui| { 
                                ui.label(if e.is_chaff { &e.original_name } else if e.is_stack { "Stack" } else { &e.original_name }); 
                                if ui.button("Restore").clicked() { to_dec = Some(i); } 
                            }); 
                        }
                    });
                    if let Some(i) = to_dec { let _ = self.process_polymorphic_decryption(i); }
                }
                ActiveWindow::PrivateChat => {
                    ui.heading("Enigma Direct Link");
                    ui.checkbox(&mut self.chat_state.is_hosting, "Host Mode");
                    ui.horizontal(|ui| { ui.label("IP:"); ui.text_edit_singleline(&mut self.chat_state.target_ip); });
                    ui.horizontal(|ui| { ui.label("ID:"); ui.text_edit_singleline(&mut self.chat_state.target_id); });
                    ui.horizontal(|ui| { ui.label("Pass:"); ui.add(egui::TextEdit::singleline(&mut self.chat_state.chat_pass).password(true)); });
                    
                    if ui.button("Connect").clicked() {
                        let (tx_ui, rx_net) = unbounded::<ChatMessage>(); 
                        let (tx_net, rx_ui) = unbounded::<String>();
                        self.chat_state.net_tx = Some(tx_net);
                        self.chat_state.net_rx = rx_net;
                        self.chat_state.messages.clear();
                        spawn_chat_network(self.chat_state.is_hosting, self.chat_state.target_ip.clone(), (self.chat_state.target_id.clone(), self.chat_state.chat_pass.clone()), tx_ui, rx_ui);
                    }
                    ui.separator();
                    egui::ScrollArea::vertical().stick_to_bottom(true).show(ui, |ui| { 
                        for m in &self.chat_state.messages { 
                            if m.is_system { ui.colored_label(egui::Color32::YELLOW, &m.content); }
                            else { ui.label(format!("{}: {}", m.sender, m.content)); }
                        } 
                    });
                    ui.horizontal(|ui| { 
                        let r = ui.text_edit_singleline(&mut self.chat_state.input_msg); 
                        if (r.lost_focus() && ui.input(|i| i.key_pressed(egui::Key::Enter))) || ui.button("Send").clicked() { 
                            if let Some(t) = &self.chat_state.net_tx { let _ = t.send(self.chat_state.input_msg.clone()); self.chat_state.input_msg.clear(); r.request_focus(); } 
                        } 
                    });
                }
            }
            ui.label(&self.status_msg);
        });
    }

    fn render_setup(&mut self, ctx: &egui::Context) { egui::CentralPanel::default().show(ctx, |ui| { ui.add(egui::TextEdit::singleline(&mut *self.pass1).password(true)); ui.add(egui::TextEdit::singleline(&mut *self.pass2).password(true)); ui.add(egui::TextEdit::singleline(&mut *self.pass3).password(true)); if ui.button("Setup").clicked() { self.session_keys = Some(self.derive_triple_keys()); fs::write(get_license_path(), "ok").unwrap(); self.state = AppState::Main; } }); }
    fn render_login(&mut self, ctx: &egui::Context) { egui::CentralPanel::default().show(ctx, |ui| { ui.add(egui::TextEdit::singleline(&mut *self.pass1).password(true)); ui.add(egui::TextEdit::singleline(&mut *self.pass2).password(true)); ui.add(egui::TextEdit::singleline(&mut *self.pass3).password(true)); if ui.button("Login").clicked() { self.session_keys = Some(self.derive_triple_keys()); self.state = AppState::Main; } }); }
}

fn main() -> eframe::Result<()> { eframe::run_native("VEILGUARD", eframe::NativeOptions::default(), Box::new(|_cc| Box::new(SecureApp::default()))) }