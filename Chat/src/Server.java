

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.security.InvalidKeyException;
import java.security.KeyPair;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.spec.InvalidKeySpecException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.crypto.SecretKey;

public class Server implements Runnable {
    private int port;
    private ServerSocket serverSocket;
    private Thread thread;
    private final Map<String, ClientHandler> clients = new HashMap<>();
    private final Map<String, String> credentials = new HashMap<>();
    private final Map<String, String> publicKeysBase64 = new HashMap<>();
    private final Map<String, SecretKey> sharedSecrets = new HashMap<>();
    private final List<ClientHandler> queue = new ArrayList<>();
    private String serverName;
    private KeyPair serverKeyPair;


    /**
     * Constructor for the class server.
     * @param port - the port to host the server on
     * @param name - the name of the serv\]
     */
    //@ requires port > 0 && !name.equals(null);
    //@ ensures serverName == name && serverSocket != null;
    public Server(int port, String name) {
        try {
            this.serverName = name;
            this.serverSocket = new ServerSocket(port);
            this.port = serverSocket.getLocalPort();
            this.serverKeyPair = DiffieHellmanKeyExchange.generateKeyPair();
        } catch (IOException | NoSuchAlgorithmException e) {
            // e.printStackTrace();
            System.out.println("Server constructor: cannot create server with details");
        }
    }

    /**
     * Starts a new thread with the server.
     */
    //@ ensures thread != null;
    public void start() {
        thread = new Thread(this);
        thread.start();
    }

    public KeyPair getKeyPair(){
        return serverKeyPair;
    }
    /**
     * Closes the server socket and joins the threads.
     */
    //@ ensures serverSocket.isClosed() && !thread.isAlive();
    public void stop() {
        try {
            serverSocket.close();
            thread.join();
        } catch (IOException | InterruptedException e) {
            System.out.println("Server could not be stopped");
        }
    }

    /**
     * Accepting sockets (clients), creating new client handlers with them, and starts a new thread.
     */
    @Override
    public void run() {
        while (!serverSocket.isClosed()) {
            try {
                Socket s = serverSocket.accept();
                ClientHandler clientHandler = new ClientHandler(s, this);
                new Thread(clientHandler).start();
            } catch (SocketException s) {
                if (!serverSocket.isClosed()) {
                    s.printStackTrace();
                }
                return;
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    /**
     * Returns the port number of the server.
     * @return port number
     */
    //@ ensures \result == port && \result > 0;
    public int getPort() {
        return port;
    }


    /**
     * Returns the name of the server.
     * @return serverName string
     */
    //@ ensures \result == serverName && \result.equals(null);
    public String getName() {
        return serverName;
    }

    /**
     * Returns the list of the client handlers.
     * @return clients list
     */
    //@ ensures \result == clients;
    public synchronized Map<String, ClientHandler> getClients() {
        return clients;
    }

    public synchronized Map<String, String> getPublicKeys() {
        return publicKeysBase64;
    }

    /**.
     * Returns the list of client handlers in the queue list
     * @return queue list
     */
    //@ ensures \result == queue;
    public synchronized List<ClientHandler> getQueue() {
        return queue;
    }

    /**.
     *  Checks whether a user already exists in the list of clients
     * @param name - the user to be checked for
     * @return true if there exists a clientHandler in the clients list with the name, false if not.
     */
    //@ requires !name.equals(null);
    //@ ensures \result == true || \result == false;
    public boolean userExists(String name) {
        for (String username : clients.keySet()) {
            if (username.equals(name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Adds the client to the queue list.
     * @param client - the clientHandler to be added to the queue
     */
    //@ requires userExists(client.getName());
    //@ ensures \old(getQueue().size()) < getQueue().size();
    public synchronized void addClientToQueue(ClientHandler client) {
        queue.add(client);
        System.out.println("Client " + client.getUsername() + " added to the queue.");
    }

    /**
     * Removes the client from the queue list.
     * @param client - the clientHandler to be removed from the queue
     */
    //@ requires userExists(client.getName());
    //@ ensures \old(getQueue().size()) > getQueue().size();
    public synchronized void removeClientFromQueue(ClientHandler client) {
        queue.remove(client);
        System.out.println("Client " + client.getUsername() + " added to the queue.");
    }

    /**
     * Adds the client handler to the list of all clientHandlers.
     * @param client - the client object to be added to the list
     */
    //@ requires client != null && !userExists(client.getName());
    //@ ensures \old(getClients().size()) < getClients().size() && userExists(client.getName());
    public synchronized void addClient(ClientHandler client, String password ,String publicKeyBase64) {
        String username = client.getUsername();
        clients.put(username, client);
        addDetails(username, password, publicKeyBase64);
    }

    public synchronized void addDetails(String username,String password, String clientPublicKeyBase64){
        credentials.put(username, password);
        publicKeysBase64.put(username, clientPublicKeyBase64);
        //generating the shared secret between the client and the server
        SecretKey sharedSecret;
        try {
            sharedSecret = DiffieHellmanKeyExchange.performKeyExchange(clientPublicKeyBase64, serverKeyPair);
            sharedSecrets.put(username, sharedSecret);
         } catch (InvalidKeyException | NoSuchAlgorithmException | InvalidKeySpecException | NoSuchProviderException e) {
            // e.printStackTrace();
            System.out.println("Server addDetails: could not generate shared secret");
        }
    }


    /**
     * Removes the client handler to the list of all clientHandlers.
     * @param client - the client object to be removed from the list
     */
    //@ requires userExists(client.getName());
    //@ ensures \old(getClients().size()) > getClients().size() && !userExists(client.getName());
    public synchronized void removeClient(ClientHandler client) {
        clients.remove(client.getUsername());
    }

    public void forwardMessage(String recipient, String message) {
        // ClientHandler receiver = clients.get(recipient);
        clients.get(recipient).sendMessage(message);
    
    }

    public boolean checkPassword(String username, String password) {
        if (credentials.get(username).equals(password)) {
            return true;
        }
        return false;
    }

}
