

import java.security.*;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.X509EncodedKeySpec;
import java.util.Base64;

import javax.crypto.KeyAgreement;
import javax.crypto.SecretKey;
import javax.crypto.spec.SecretKeySpec;

public class DiffieHellmanKeyExchange {

    public static KeyPair generateKeyPair() throws NoSuchAlgorithmException {
        KeyPairGenerator keyPairGenerator = null;
        keyPairGenerator = KeyPairGenerator.getInstance("DH");
        keyPairGenerator.initialize(512); // Adjust the key size as needed
        return keyPairGenerator.generateKeyPair();
    }

    public static String getPublicKeyBase64(KeyPair keyPair) {
        PublicKey publicKey = keyPair.getPublic();
        return Base64.getEncoder().encodeToString(publicKey.getEncoded());
    }

    // Truncate or pad the byte array to the specified length
    private static byte[] truncateOrPad(byte[] input, int length) {
        byte[] output = new byte[length];
        System.arraycopy(input, 0, output, 0, Math.min(input.length, length));
        return output;
    }
    public static SecretKey performKeyExchange(String otherPartyPublicKeyBase64, KeyPair ownKeyPair) throws NoSuchAlgorithmException, InvalidKeyException, InvalidKeySpecException, NoSuchProviderException {
        KeyFactory keyFactory = KeyFactory.getInstance("DH");
        X509EncodedKeySpec keySpec = new X509EncodedKeySpec(Base64.getDecoder().decode(otherPartyPublicKeyBase64));
        PublicKey otherPartyPublicKey = keyFactory.generatePublic(keySpec);

        KeyAgreement keyAgreement = KeyAgreement.getInstance("DH");
        keyAgreement.init(ownKeyPair.getPrivate());
        keyAgreement.doPhase(otherPartyPublicKey, true);

        byte[] sharedSecret = keyAgreement.generateSecret();
        byte[] truncatedSecret = truncateOrPad(sharedSecret, 32);

        return new SecretKeySpec(truncatedSecret, "AES");
    }

}

