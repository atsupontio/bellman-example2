use crypto::digest::Digest;


pub fn encode_bit() ->[u8; 32] {
use hex;
use crypto::sha2::Sha256;

    const NUM_BLINDING_BITS: usize = 128;
    
    let id = "1d7361b1-5018-4043-804b-7c589bdabc31";
    let secret = "12345678";
    let nonce = "afe387d2";

    let new_id: String = id.split('-').collect();
    println!("new_id: {:?}", new_id);
    
    let mut id_bytes = hex::decode(&new_id).unwrap();
    let id = hexdump(&id_bytes);
    let mut id_bool = Vec::new();
    for (i, c) in id.chars().enumerate() {
        // do something with character `c` and index `i`
        if c == '1' {
            id_bool.push(true);
        } else {
            id_bool.push(false);
        }
    }

    let secret_bytes = hex::decode(&secret).unwrap();
    println!("secret: {:?}", secret_bytes);
    let secret = hexdump(&secret_bytes);
    let mut secret_bool = Vec::new();
    for (i, c) in secret.chars().enumerate() {
        // do something with character `c` and index `i`
        if c == '1' {
            secret_bool.push(true);
        } else {
            secret_bool.push(false);
        }
    }
    let nonce_bytes = hex::decode(&nonce).unwrap();
    println!("nonce:{:?}", nonce_bytes);
    let nonce = hexdump(&nonce_bytes);
    let mut nonce_bool = Vec::new();
    for (i, c) in nonce.chars().enumerate() {
        // do something with character `c` and index `i`
        if c == '1' {
            nonce_bool.push(true);
        } else {
            nonce_bool.push(false);
        }
    }

    id_bool.extend(secret_bool.clone());
    id_bool.extend(nonce_bool);

    let bytes = be_bit_vector_into_bytes(&id_bool);

    let mut hash_result1 = [0u8; 32];
    let mut hash_result2 = [0u8; 32];

    let mut b = Sha256::new();
    b.input(&bytes);
    b.result(&mut hash_result2[..]);
    println!("b: {:?}", hash_result2);

    hash_result2

    // let old_blinding_bits: Vec<bool> = (0..NUM_BLINDING_BITS).map(|_| preimage).collect();
}

fn hexdump(bytes: &[u8]) -> String {

    let mut sum = String::new();

    println!("{} bytes:", bytes.len());
    for (i, b) in bytes.iter().enumerate() {
        // b: &u8 の値を2桁の16進数で表示する
        print!("{:?}", b);
        let a = format!("{:b}", b);
        sum += &a;

        // 値を16個表示するごとに改行する
        if (i + 1) % 16 == 0 {
            println!();
        }
    }
    println!();
    println!("{:?}", sum);
    sum
}

fn split(bytes: Vec<u8>) -> (String, String) {
    let mut xl: String = String::default();
    let mut xr: String = String::default(); 

    println!("{} bytes:", bytes.len());
    for (i, b) in bytes.iter().enumerate() {
        // b: &u8 の値を2桁の16進数で表示する
        let a = format!("{:?}", b);
        xl += &a;

        // 値を16個表示するごとに改行する
        if i > bytes.len() / 2 {
            let a = format!("{:?}", b);
            xr += &a;
        }
    }
    (xl, xr)
}

fn be_bit_vector_into_bytes
    (bits: &Vec<bool>) -> Vec<u8>
{
    let mut bytes: Vec<u8> = vec![];
    for byte_chunk in bits.chunks(8)
    {
        let mut byte = 0u8;
        // pack just in order
        for (i, bit) in byte_chunk.iter().enumerate()
        {
            if *bit {
                byte |= 1 << (7 - i);
            }
        }
        bytes.push(byte);
    }

    bytes
}