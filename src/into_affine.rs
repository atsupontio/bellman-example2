use bellman::pairing::bls12_381::{G1Affine};
use bellman::pairing::{RawEncodable, CurveAffine, CurveProjective, EncodedPoint, Engine, GroupDecodingError};
use bellman::pairing::bls12_381::{Bls12, Fq, Fq12, FqRepr, Fr, FrRepr};
use bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};


pub fn into_affine_unchecked(bytes: &[u8; 96]) -> Result<G1Affine, GroupDecodingError> {
    // Create a copy of this representation.
    let mut copy = [0; 96];

    if copy[0] & (1 << 7) != 0 {
        // Distinguisher bit is set, but this should be uncompressed!
        return Err(GroupDecodingError::UnexpectedCompressionMode);
    }

    if copy[0] & (1 << 6) != 0 {
        // This is the point at infinity, which means that if we mask away
        // the first two bits, the entire representation should consist
        // of zeroes.
        copy[0] &= 0x3f;

        if copy.iter().all(|b| *b == 0) {
            Ok(G1Affine::zero())
        } else {
            Err(GroupDecodingError::UnexpectedInformation)
        }
    } else {
        if copy[0] & (1 << 5) != 0 {
            // The bit indicating the y-coordinate should be lexicographically
            // largest is set, but this is an uncompressed element.
            return Err(GroupDecodingError::UnexpectedInformation);
        }

        // Unset the three most significant bits.
        copy[0] &= 0x1f;

        let mut x = FqRepr([0; 6]);
        let mut y = FqRepr([0; 6]);

        {
            let mut reader = &copy[..];

            x.read_be(&mut reader).unwrap();
            y.read_be(&mut reader).unwrap();
        }

        Ok(G1Affine {
            x: Fq::from_repr(x).map_err(|e| {
                GroupDecodingError::CoordinateDecodingError("x coordinate", e)
            })?,
            y: Fq::from_repr(y).map_err(|e| {
                GroupDecodingError::CoordinateDecodingError("y coordinate", e)
            })?,
            infinity: false,
        })
    }
}