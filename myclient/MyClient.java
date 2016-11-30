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
            " -u <arg>       username";
    private static String serverurl = null;
    private static String clientuser = null;
    private static int port = 80;
    private static CloseableHttpClient httpClient;
    private static PrivateKey skrsa;
    private static PublicKey pkrsa;
    private static PrivateKey skdsa;
    private static PublicKey pkdsa;
    private static int messageCounter = 0;

    public static void main(String[] args) {
        try {
            getCommandLineArgs(args);
            httpClient = HttpClientBuilder.create().build();
            rollRandomKeys();
            register();
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            System.out.println("Server connection successful. Type (h)elp for commands.");
            boolean quit = false;
            while (!quit) {
                System.out.print("enter command> ");
                String input = br.readLine();
                switch (input.toLowerCase().split(" ", 2)[0]) {
                    case "g": case "get": case "":
                        processInbox();
                        break;
                    case "c": case "compose":
                        sendMessage(getMessage(br), input.split(" ")[1]);
                        break;
                    case "f": case "fingerprint":
                        fingerprint(input.split(" ")[1]);
                        break;
                    case "l": case "list":
                        getUserList();
                        break;
                    case "genkeys":
                        System.out.println("Generating a new keypair...");
                        rollRandomKeys();
                        register();
                        break;
                    case "h": case "help":
                        System.out.println(helpstring);
                        break;
                    case "q": case "quit":
                        System.out.println("Shutting down...");
                        quit = true;
                        break;
                    case "a": case "attack":
                        String target =  input.split(" ")[1];
			JSONArray messages = null;
                        while(true) {
                            JSONObject obj = getRequest(serverurl + "/getMessages/" + target);
                            messages = obj.getJSONArray("messages");
                            if (messages.length() > 0) {
				//System.out.println("gotem");
                                break;
                            }
                        }
                        
                        System.out.println(messages.getJSONObject(0));
                    default:
                }
            }
            httpClient.close();
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
        }
    }

    private static void processInbox() throws IOException, NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        JSONObject obj = getRequest(serverurl + "/getMessages/" + clientuser);
        JSONArray messages = obj.getJSONArray("messages");
        for (int i = 0; i < messages.length(); i++) {
            receiveMessage(messages.getJSONObject(i));
        }
    }

    private static void receiveMessage(JSONObject messagejson) throws IOException, NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException, InvalidAlgorithmParameterException {
        String sender = messagejson.getString("senderID");
        int messageID = messagejson.getInt("messageID");
        String message = messagejson.getString("message");

        PublicKey[] pks = decodeRegistrationString(lookupKey(sender));
        PublicKey senderpkrsa = pks[0];
        PublicKey senderpkdsa = pks[1];
        String textMessage = decryptMessage(sender, message, senderpkdsa);
        if (!(textMessage.equals("") || textMessage.startsWith(">>>READMESSAGE "))) {
            System.out.println(textMessage);
            String recipt = ">>>READMESSAGE " + messageID;
            sendMessage(recipt.getBytes(), sender);
        }
    }

    private static void sendMessage(byte[] M, String recipient) throws IOException {
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
            if (!verified) return "";

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
                    return "";
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
            if (!crcmatch) return "";

            //9 verify sender, get message!
            String mfstring = new String(Mformatted);
            String claimedsender = mfstring.substring(0, mfstring.indexOf(':'));
            if (!sender.equals(claimedsender)) return "";
            String textmessage = mfstring.substring(mfstring.indexOf(':') + 1, mfstring.length());
            return textmessage;
        } catch (Exception e) {
            //Silent abort
            return "";
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
                case "-u":
                    clientuser = args[++i];
                    break;
                default:
            }
        }
        if (serverurl == null || clientuser == null) {
            System.out.println(usage);
            System.exit(0);
        }
        serverurl += ":" + port;
    }
}
