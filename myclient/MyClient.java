/**
 * Created by graham on 10/12/16.
 */

import org.apache.commons.codec.binary.Base64;
import org.apache.http.HttpResponse;
import org.apache.http.client.methods.HttpGet;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.entity.StringEntity;
import org.apache.http.impl.client.CloseableHttpClient;
import org.apache.http.impl.client.HttpClientBuilder;
import org.json.JSONArray;
import org.json.JSONObject;

import javax.crypto.*;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.bind.DatatypeConverter;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.security.*;
import java.security.spec.X509EncodedKeySpec;
import java.util.Arrays;
import java.util.zip.CRC32;
import java.util.zip.Checksum;


public class MyClient {

    private static final String helpstring = "Available commands:\n" +
            "get (or empty line)  - check for new messages\n" +
            "c(ompose) <user>     - compose a message to <user>\n" +
            "f(ingerprint) <user> - return the key fingerprint of <user>\n" +
            "l(ist)               - lists all the users in the system\n" +
            "genkeys              - generates and registers a fresh keypair\n" +
            "h(elp)               - prints this listing\n" +
            "q(uit)               - exits";
    private static final String usage = "Missing required options. (-s and -u are required)\n" +
            "usage: java -cp \"*:.\" MyClient\n" +
            " -p <arg>       server port (default 80)\n" +
            " -s <arg>       server name\n" +
            " -t <arg>       target username";
    private static String serverurl = null;
    private static String clientuser = null;
    private static String target = null;
    private static int port = 80;
    private static CloseableHttpClient httpClient;
    private static PrivateKey skrsa;
    private static PublicKey pkrsa;
    private static PrivateKey skdsa;
    private static PublicKey pkdsa;
    //private static int messageCounter = 0;

    public static void main(String[] args) {
        try {
            getCommandLineArgs(args);
            httpClient = HttpClientBuilder.create().build();
            rollRandomKeys();

            System.out.println("Fishing for a message to " + target + "...");

            JSONArray messages = null;
            String sender = null;
            String originalMessage = null;
            int numbytes = -1;
            while(true) {
                JSONObject obj = getRequest(serverurl + "/getMessages/" + target);
                messages = obj.getJSONArray("messages");
                if (messages.length() > 0) {
                    sender = messages.getJSONObject(0).getString("senderID");
                    originalMessage = messages.getJSONObject(0).getString("message");
                    numbytes = getByteLength(originalMessage);
                    if (numbytes < 50) {
                        System.out.println("Caught a suspected read receipt to " + target + " from " + sender);
                    } else {
                        System.out.println("Caught a substantial message to " + target + " from " + sender);
                        break;
                    }
                }
            }

            clientuser = "" + sender.charAt(0);
            register(); //register as first letter of sender name. "a" for alice

            System.out.println("Looking for an accepted mauling (':' as 2nd char of message)...");
            int found = huntForByte(originalMessage, 17); //change the 17th byte until accepted by target (colon)

            System.out.println("Begin padding oracle attack!");
            String baseMessage = maulMessage(originalMessage, (byte) found, 17);

            //This is so that 04 04 04 ?? succeeds only on 01 and not on 04
            baseMessage = maulMessage(baseMessage, (byte) 0, numbytes - 2);
            baseMessage = maulMessage(baseMessage, (byte) 0, numbytes - 3);


            byte[] unknownpad = new byte[16]; //numbytes];
            byte[] plaintext = new byte[16]; //numbytes];
            byte ogCipherByte;
            byte padByte;
            byte ogPlaintextByte;
            byte hunted = 0;
            for (int i = 1; i <= 16; i++) {
                //special case for second to last since last could have been 0 or 1 to pass padding
                if (i == 2) {
                    hunted = specialCaseFor2(originalMessage, numbytes, baseMessage, unknownpad, plaintext, hunted);
                }
                else {
                    hunted = (byte) huntForByte(baseMessage, numbytes - i);
                }

                ogCipherByte = getByte(originalMessage, numbytes - i);
                padByte = (byte) ( hunted ^  i);
                ogPlaintextByte = (byte) (ogCipherByte ^ padByte);

                unknownpad[16-i] = padByte;
                plaintext[16-i] = ogPlaintextByte;
                System.out.println(padByte + " padbyte" );
                System.out.println(hunted + " hunted");
                System.out.println(i + " i");
                System.out.println(ogCipherByte + "ogCipher");
                System.out.println(ogPlaintextByte + " ogPlain");

                for (int j = 1; j <= i; j++) {
                    baseMessage = maulMessage(baseMessage, (byte) (((byte) (i + 1)) ^ unknownpad[16-j]), numbytes - j);
                }
            }

            System.out.println("DONE!");
            System.out.println(unknownpad);
            System.out.println(new String(unknownpad));
            System.out.println(plaintext);
            System.out.println(new String(plaintext));



            httpClient.close();

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
        }
    }

    private static byte specialCaseFor2(String originalMessage, int numbytes, String baseMessage, byte[] unknownpad, byte[] plaintext, byte lower) throws IOException, NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        byte padByte;
        byte ogCipherByte;
        byte ogPlaintextByte;
        processInbox(); //often second message is in the pipes
        int higher = lower + 1;

        System.out.println("Cleaned");
        //last padbyte is either lower ^ 0 or lower ^ 1. Same as saying lower or higher
        int pen = huntForPenultimate(baseMessage, numbytes - 1, (byte) ((higher^1)^2) );
        if (pen < 0) { //higher was correct
            System.out.println("Correcting 0/1!!!!");
            //fix last iteration
            padByte = (byte) (higher ^ 1);
            ogCipherByte = getByte(originalMessage, numbytes - 1);
            ogPlaintextByte = (byte) (ogCipherByte ^ padByte);
            unknownpad[16-1] = padByte;
            plaintext[16-1] = ogPlaintextByte;
            System.out.println(ogPlaintextByte + " last plaintext changed");

            return (byte) (pen + 1000);
        } else {//lower is correct
            return (byte) (pen - 1000);
        }
    }

    private static int huntForPenultimate(String msgToMaul, int lastpos, byte other2) throws NoSuchAlgorithmException, InvalidKeyException, SignatureException, IOException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        String msg2 = maulMessage(msgToMaul, other2 ,lastpos);
        for (int hunter = -128; hunter < 127; hunter++) {
            String mauled = maulMessage(msgToMaul, (byte) hunter, lastpos - 1);
            sendRawMessage(mauled, target, hunter + 1000);
            String mauled2 = maulMessage(msg2, (byte) hunter, lastpos - 1);
            sendRawMessage(mauled2, target, hunter - 1000);
        }
        int found = -666;
        while(found == -666) {
            found = processInbox();
        }
        return found;
    }

    private static int huntForByte(String msgToMaul, int pos) throws NoSuchAlgorithmException, InvalidKeyException, SignatureException, IOException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        for (int hunter = -128; hunter < 127; hunter++) {
            String mauled = maulMessage(msgToMaul, (byte) hunter, pos);
            sendRawMessage(mauled, target, hunter);
        }
        int found = -666;
        while(found == -666) {
            found = processInbox();
        }
        return found;
    }

    private static int processInbox() throws IOException, NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        JSONObject obj = getRequest(serverurl + "/getMessages/" + clientuser);
        JSONArray messages = obj.getJSONArray("messages");
        for (int i = 0; i < messages.length(); i++) {
            int ret = receiveMessage(messages.getJSONObject(i));
            if (ret != -666) return ret; // read receipt
        }
        return -666; // no read receipt
    }

    private static int receiveMessage(JSONObject messagejson) throws IOException, NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        String sender = messagejson.getString("senderID");
        int messageID = messagejson.getInt("messageID");
        String message = messagejson.getString("message");

        PublicKey[] pks = decodeRegistrationString(lookupKey(sender));
        PublicKey senderpkrsa = pks[0];
        PublicKey senderpkdsa = pks[1];
        String textMessage = decryptMessage(sender, message, senderpkdsa);
        System.out.println(textMessage);
        if (!(textMessage.equals("") || textMessage.startsWith(">>>READMESSAGE ") || textMessage.startsWith("!!"))) {
            //System.out.println(textMessage);
            String receipt = ">>>READMESSAGE " + messageID;
            //sendMessage(receipt.getBytes(), sender);
        } else if (textMessage.startsWith(">>>READMESSAGE ")) {
            System.out.println("Got a receipt for " + textMessage.split(" ")[1]);
            return Integer.parseInt(textMessage.split(" ")[1]);
        }

        return -666;
    }

    private static byte getByte(String message , int pos) {
        String[] encoded = message.split(" ");

        Base64 base64 = new Base64();
        byte[] C2 = base64.decode(encoded[1]);
        return C2[pos];
    }

    private static int getByteLength(String message) {
        String[] encoded = message.split(" ");

        Base64 base64 = new Base64();
        byte[] C2 = base64.decode(encoded[1]);
        return C2.length;
    }

    private static String maulMessage(String message, byte mauling, int pos) throws NoSuchAlgorithmException, UnsupportedEncodingException, InvalidKeyException, SignatureException {
        String[] encoded = message.split(" ");

        Base64 base64 = new Base64();
        byte[] C1 = base64.decode(encoded[0]);
        byte[] C2 = base64.decode(encoded[1]);

        C2[pos] = mauling;

        byte[] C164 = new String(base64.encode(C1)).getBytes("UTF-8");
        byte[] C264 = new String(base64.encode(C2)).getBytes("UTF-8");

        //9 DSA signature sigma
        Signature dsasig = Signature.getInstance("SHA1withDSA");
        dsasig.initSign(skdsa);
        byte[] tosig = concat(concat(C164, " ".getBytes("US-ASCII")), C264);
        dsasig.update(tosig);
        byte[] sigma = dsasig.sign();

        //10 sigma64
        byte[] sigma64 = new String(base64.encode(sigma)).getBytes("UTF-8");

        //11 C164|| ||C264|| ||sigma64
        byte[] Cbytes = concat(C164, concat(" ".getBytes("US-ASCII"), concat(C264, concat(
                " ".getBytes("US-ASCII"), sigma64))));

        /*System.out.println("~~~");
        System.out.println(message);
        System.out.println("---");
        System.out.println(new String(Cbytes));*/


        return new String(Cbytes);
    }

    /*private static void sendMessage(byte[] M, String recipient) throws IOException {
        PublicKey[] pks = decodeRegistrationString(lookupKey(recipient));
        PublicKey targetpkrsa = pks[0];
        PublicKey targetpkdsa = pks[1];
        if (M != null) {
            String encryptedMessage = encryptMessage(targetpkrsa, M);

            JSONObject payload = new JSONObject();
            payload.put("recipient", recipient);
            payload.put("messageID", messageCounter++);
            payload.put("message", encryptedMessage);
            postRequest(serverurl + "/sendMessage/" + clientuser, payload);
        }
    }*/

    private static void sendRawMessage(String message, String recipient, int id) throws IOException {
        JSONObject payload = new JSONObject();
        payload.put("recipient", recipient);
        payload.put("messageID", id);
        payload.put("message", message);
        postRequest(serverurl + "/sendMessage/" + clientuser, payload);
    }


    private static String decryptMessage(String sender, String message, PublicKey senderpkdsa) {
        try {
            //1 have senderpkdsa
            //2 parse the message C into C164 C264 and sigma64
            String[] encoded = message.split(" ");

            //3 decode to C1 C2 and sigma
            Base64 base64 = new Base64();
            byte[] C1 = base64.decode(encoded[0]);
            byte[] C2 = base64.decode(encoded[1]);
            byte[] sigma = base64.decode(encoded[2]);

            //4 verify sig
            Signature dsasig = Signature.getInstance("SHA1withDSA");
            dsasig.initVerify(senderpkdsa);
            dsasig.update(message.substring(0, message.lastIndexOf(" ")).getBytes());
            boolean verified = dsasig.verify(sigma);
            if (!verified) return "!!Sig verify failed!!";

            //5 RS decrypt C1 -> K
            Cipher rsacipher = Cipher.getInstance("RSA/ECB/PKCS1Padding");
            rsacipher.init(Cipher.DECRYPT_MODE, skrsa);
            byte[] Kbytes = rsacipher.doFinal(C1);
            SecretKey K = new SecretKeySpec(Kbytes, 0, Kbytes.length, "AES");

            //6 Parse and decrypt C2 -> Mpadded
            byte[] iv = Arrays.copyOfRange(C2, 0, 16);
            byte[] C2original = Arrays.copyOfRange(C2, 16, C2.length);
            Cipher aescipher = Cipher.getInstance("AES/CTR/NoPadding");
            aescipher.init(Cipher.DECRYPT_MODE, K, new IvParameterSpec(iv));
            byte[] Mpadded = aescipher.doFinal(C2original);

            //7 verify and remove padding Mpadded->Mcrc
            int padding = Mpadded[Mpadded.length - 1];
            for (int j = 0; j < padding; j++) {
                if (Mpadded[Mpadded.length - j - 1] != padding) {
                    return "!!Manual padding check failed!!";
                }
            }
            byte[] Mcrc = Arrays.copyOfRange(Mpadded, 0, Mpadded.length - padding);

            //8 Mcrc -> Mformatted and verify crc
            byte[] Mformatted = Arrays.copyOfRange(Mcrc, 0, Mcrc.length - 4);
            byte[] crc = Arrays.copyOfRange(Mcrc, Mcrc.length - 4, Mcrc.length);
            Checksum crc32 = new CRC32();
            crc32.update(Mformatted, 0, Mformatted.length);
            boolean crcmatch = Arrays.equals(crc,
                    Arrays.copyOfRange(longToBytes(crc32.getValue()), 4, 8));
            //if (!crcmatch) return "!!CRC check failed!!";

            //9 verify sender, get message!
            String mfstring = new String(Mformatted);
            String claimedsender = mfstring.substring(0, mfstring.indexOf(':'));
            if (!sender.equals(claimedsender)) return "!!Sender check failed!!~~~~~~\n" + mfstring;
            String textmessage = mfstring.substring(mfstring.indexOf(':') + 1, mfstring.length());
            return textmessage;
        } catch (Exception e) {
            //Silent abort
            return "!!" + e;
            //return "!!Exception!!";
        }
    }

    private static byte[] getMessage(BufferedReader br) throws IOException {
        System.out.println("Enter your message and hit return (empty line cancels message):");
        String message = br.readLine();
        if (message.equalsIgnoreCase("")) {
            System.out.println("Message cancelled.");
            return null;
        }
        byte[] M = message.getBytes("UTF-8");
        return M;
    }

    private static String encryptMessage(PublicKey targetpkrsa, byte[] m) {
        try {
            // 1 Generate 128 bit AES Key K
            SecureRandom secrand = SecureRandom.getInstance("SHA1PRNG");
            KeyGenerator aesgen = KeyGenerator.getInstance("AES");
            aesgen.init(128, secrand);
            SecretKey K = aesgen.generateKey();

            // 2 Encrypt K -> C1
            Cipher rsacipher = Cipher.getInstance("RSA/ECB/PKCS1Padding");
            rsacipher.init(Cipher.ENCRYPT_MODE, targetpkrsa);
            byte[] C1 = rsacipher.doFinal(K.getEncoded());

            // 3 prepend on M -> Mformatted
            byte[] Mformatted = concat((clientuser + ":").getBytes("US-ASCII"), m);

            //4 append CRC32 on Mformatted -> Mcrc
            Checksum crc32 = new CRC32();
            crc32.update(Mformatted, 0, Mformatted.length);
            byte[] Mcrc = concat(Mformatted, Arrays.copyOfRange(longToBytes(crc32.getValue()), 4, 8));

            //5 pad with pkcs5 -> Mpadded
            int n = Mcrc.length % 16;
            byte[] ps = new byte[16 - n];
            Arrays.fill(ps, (byte) (16 - n));
            byte[] Mpadded = concat(Mcrc, ps);

            //6 secure random 16 bit IV
            byte[] iv = new byte[16];
            secrand.nextBytes(iv);

            //7 Mpadded -> C2
            Cipher aescipher = Cipher.getInstance("AES/CTR/NoPadding");
            aescipher.init(Cipher.ENCRYPT_MODE, K, new IvParameterSpec(iv));
            byte[] C2 = concat(iv, aescipher.doFinal(Mpadded));

            //8 base64 C1 and C2
            Base64 base64 = new Base64();
            byte[] C164 = new String(base64.encode(C1)).getBytes("UTF-8");
            byte[] C264 = new String(base64.encode(C2)).getBytes("UTF-8");

            //9 DSA signature sigma
            Signature dsasig = Signature.getInstance("SHA1withDSA");
            dsasig.initSign(skdsa);
            byte[] tosig = concat(concat(C164, " ".getBytes("US-ASCII")), C264);
            dsasig.update(tosig);
            byte[] sigma = dsasig.sign();

            //10 sigma64
            byte[] sigma64 = new String(base64.encode(sigma)).getBytes("UTF-8");

            //11 C164|| ||C264|| ||sigma64
            byte[] Cbytes = concat(C164, concat(" ".getBytes("US-ASCII"), concat(C264, concat(
                    " ".getBytes("US-ASCII"), sigma64))));

            return new String(Cbytes);
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
            return null;
        }
    }

    private static void fingerprint(String username) throws IOException {
        String keydata = lookupKey(username);
        if (keydata == null) {
            System.out.println("Could not find a key for user " + username);
        } else {
            System.out.println(toHexString(sha256(keydata.getBytes(StandardCharsets.UTF_8))));
        }

    }

    private static String lookupKey(String username) throws IOException {
        JSONObject obj = getRequest(serverurl + "/lookupKey/" + username);
        String status = obj.getString("status");

        if (!status.equalsIgnoreCase("found key")) {
            System.out.println("Did not receive a key from the server");
            return null;
        } else {
            return obj.getString("keyData");
        }
    }

    private static void register() throws IOException {
        JSONObject payload = new JSONObject();
        payload.put("keyData", formRegistrationString());
        String resp = postRequest(serverurl + "/registerKey/" + clientuser, payload);
        System.out.println("Successfully registered a public key for '" + clientuser + "'");
    }

    private static String formRegistrationString() {
        Base64 base64 = new Base64();
        try {
            return new String(concat(concat(base64.encode(pkrsa.getEncoded()),
                                            "%".getBytes("US-ASCII")),
                                     base64.encode(pkdsa.getEncoded())));
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
            System.exit(0);
            return null;
        }
    }

    private static PublicKey[] decodeRegistrationString(String registrationString) {
        Base64 base64 = new Base64();
        byte[] bytes = registrationString.getBytes();

        String[] encoded = registrationString.split("%");
        byte[] first = base64.decode(encoded[0]);
        byte[] second = base64.decode(encoded[1]);
        PublicKey[] ret = new PublicKey[2];
        try {
            ret[0] = KeyFactory.getInstance("RSA").generatePublic(new X509EncodedKeySpec(first));
            ret[1] = KeyFactory.getInstance("DSA").generatePublic(new X509EncodedKeySpec(second));
            return ret;
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
            return null;
        }
    }

    private static void rollRandomKeys() {
        try {
            SecureRandom secrand = SecureRandom.getInstance("SHA1PRNG");
            KeyPairGenerator rsagen = KeyPairGenerator.getInstance("RSA");
            KeyPairGenerator dsagen = KeyPairGenerator.getInstance("DSA");
            rsagen.initialize(1024, secrand);
            dsagen.initialize(1024, secrand);

            KeyPair rsapair = rsagen.generateKeyPair();
            skrsa = rsapair.getPrivate();
            pkrsa = rsapair.getPublic();

            KeyPair dsapair = dsagen.generateKeyPair();
            skdsa = dsapair.getPrivate();
            pkdsa = dsapair.getPublic();

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
        }
    }

    private static void getUserList() throws IOException {
        JSONArray users = getRequest(serverurl + "/lookupUsers").getJSONArray("users");
        for (int i = 0; i < users.length(); i++) {
            System.out.println(i + ":" + users.getString(i));
        }
    }

    private static JSONObject getRequest(String url) throws IOException {
        //https://www.mkyong.com/webservices/jax-rs/restful-java-client-with-apache-httpclient/
        HttpGet getRequest = new HttpGet(url);
        getRequest.addHeader("Accept", "application/json");

        HttpResponse response = httpClient.execute(getRequest);

        if (response.getStatusLine().getStatusCode() != 200) {
            throw new RuntimeException("Failed : HTTP error code : "
                    + response.getStatusLine().getStatusCode());
        }

        BufferedReader br = new BufferedReader(
                new InputStreamReader((response.getEntity().getContent())));

        StringBuffer result = new StringBuffer();
        String line = "";
        while ((line = br.readLine()) != null) {
            result.append(line);
        }

        return new JSONObject(result.toString());
    }

    private static String postRequest(String url, JSONObject json) throws IOException {
        HttpPost postRequest = new HttpPost(url);
        postRequest.addHeader("Accept", "application/json");
        postRequest.addHeader("Content-Type", "application/json");
        StringEntity params = new StringEntity(json.toString());
        postRequest.setEntity(params);

        HttpResponse response = httpClient.execute(postRequest);

        if (response.getStatusLine().getStatusCode() != 200) {
            throw new RuntimeException("Failed : HTTP error code : "
                    + response.getStatusLine().getStatusCode());
        }
        BufferedReader br = new BufferedReader(
                new InputStreamReader((response.getEntity().getContent())));

        StringBuffer result = new StringBuffer();
        String line = "";
        while ((line = br.readLine()) != null) {
            result.append(line);
        }
        return result.toString();
    }

    private static byte[] concat(byte[] one, byte[] two) {
        byte[] result = new byte[one.length + two.length];
        System.arraycopy(one, 0, result, 0, one.length);
        System.arraycopy(two, 0, result, one.length, two.length);
        return result;
    }

    private static byte[] sha256(byte[] toSHA) {
        try {
            MessageDigest sha1Func = MessageDigest.getInstance("SHA-256");
            sha1Func.reset();
            sha1Func.update(toSHA);
            return sha1Func.digest();
        } catch (NoSuchAlgorithmException e) {
            System.err.println("Insufficient Programmer Error");
            System.exit(0);
            return null;
        }
    }

    private static String toHexString(byte[] array) {
        String hex = DatatypeConverter.printHexBinary(array);
        String spaced = "";
        for (int i = 0; i < hex.length(); i +=2) {
            spaced += hex.substring(i, i+2) + " ";
        }
        return spaced.toUpperCase();
    }

    //http://stackoverflow.com/questions/4485128/how-do-i-convert-long-to-byte-and-back-in-java
    private static byte[] longToBytes(long x) {
        ByteBuffer buffer = ByteBuffer.allocate(Long.BYTES);
        buffer.putLong(x);
        return buffer.array();
    }

    private static void getCommandLineArgs(String[] args) {
        for (int i = 0; i < args.length; i++) {
            switch(args[i].toLowerCase()) {
                case "-p":
                    port = Integer.parseInt(args[++i]);
                    break;
                case "-s":
                    serverurl = args[++i];
                    break;
                case "-t":
                    target = args[++i];
                    break;
                default:
            }
        }
        if (serverurl == null || target == null) {
            System.out.println(usage);
            System.exit(0);
        }
        serverurl += ":" + port;
    }
}
