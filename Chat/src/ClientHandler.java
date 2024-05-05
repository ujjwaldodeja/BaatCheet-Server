
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.SocketException;
import java.util.Arrays;
import java.util.Map;

public class ClientHandler implements Runnable {
    private Socket socket;
    private Server server;
    private PrintWriter writer;
    private BufferedReader reader;
    private String username;
    boolean isInQueue = false;
    boolean isInGame = false;

    //@ requires socket != null && server != null;
    public ClientHandler(Socket socket, Server server) {
        this.socket = socket;
        this.server = server;
    }

    /**
     * Sends a message by writing to the local PrintWriter writer.
     *
     * @param message String
     */
    //@ requires !message.equals(null);
    public void sendMessage(String message) {
        writer.println(message);
        writer.flush();
    }

    /**
     * Closes the connection with the client.
     */
    //@ensures socket.isClosed() && !server.userExists(this.getName());
    private void close() {
        try {
            System.out.println("Connection lost");
            server.removeClient(this);
            socket.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * The communication between the client, sending and receiving commands and act accordingly.
     */
    @Override
    public void run() {
        try {
            writer = new PrintWriter(socket.getOutputStream(), true);
            reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            System.out.println("Connection established");

            String[] command;

            // boolean stop = false;
            // while (!stop) {
            //     command = reader.readLine().split("~");
            //     System.out.println(Arrays.toString(command));

            //     if (!server.userExists(command[1])) {
            //         //the incoming message structure REGISTER~username~password~publicKey
            //         username = command[1];
            //         server.addClient(this, command[2], command[3]);

            //         // server.addCredentials(username, command[2], command[3]);

            //         //sending the server public key tot he client upon registration
            //         String serverPublicKeyBase64 = DiffieHellmanKeyExchange.getPublicKeyBase64(server.getKeyPair());
            //         sendMessage("REGISTERED" + "~" + serverPublicKeyBase64);

            //         System.out.println("CLIENT REGISTERED");
            //         stop = true;
            //     }
            //     sendMessage("ALREADYSIGNEDUP");
            //     System.out.println("fucked up");
            // }

            while (!socket.isClosed()) {
                try {
                    command = reader.readLine().split("~");
                    // System.out.println(Arrays.toString(command));

                } catch (SocketException e) {
                    System.out.println("Client " + username + " disconnected.");
                    server.removeClient(this);
                    server.removeClientFromQueue(this);
                    this.close();
                    break;
                }
                switch (command[0]) {
                    case "REGISTER": {
                        if (!server.userExists(command[1])) {
                            //the incoming message structure REGISTER~username~password~publicKey
                            this.username = command[1];
                            server.addClient(this, command[2], command[3]);

                            //sending the server public key tot he client upon registration
                            String serverPublicKeyBase64 = DiffieHellmanKeyExchange.getPublicKeyBase64(server.getKeyPair());
                            sendMessage("REGISTERED" + "~" + serverPublicKeyBase64);
                            System.out.println("CLIENT REGISTERED");
                        } else {
                            sendMessage("USERNAME_TAKEN");
                            System.out.println("fucked up");
                        }   
                    }
                    break;
                    case "LOGIN": {
                        String username = command[1];
                        String password = command[2];
                        if (server.checkPassword(username, password)) {
                            this.username = username;
                            sendUpdatetoAllClients();
                            sendMessage("LOGGED_IN");
                            //the queue will be used for saving clients that are online from now on
                            //server.addClientToQueue(this);  
                        } else {
                            sendMessage("INVALID_PASSWORD");
                        }
                    }
                    break;
                    case "LIST": {
                        System.out.println("processing");
                        sendLists();
                    }
                    
                    break;
                    case "TEXT": {
                            String recipient = command[1];
                            String sender = command[2];
                            String message = command[3];
                            server.forwardMessage(recipient, "TEXT~" + sender + "~" + message);;
                            System.out.println("Message sent:" +  command);
                    }
                    break;
                    case "SEND_IMAGE": {
                            String recipient = command[1];
                            String sender = username;
                            String image = command[2];
                            String length = command[3];
                            System.out.println(command[2]);
                            
                            server.forwardMessage(recipient, "IMAGE~" + sender + "~" + image + "~" + length);;
                            // System.out.println("Message sent:" +  command);
                    }
                    break;
                    case "SESSION_REQUEST": {
                        String recipient = command[1];
                        String sender = username;
                        String key = command[2];
                        server.forwardMessage(recipient, "SESSION_REQUEST~" + sender + "~" + key);
                    }
                    break;
                    case "SESSION_ACCEPT": {
                        String recipient = command[1];
                        String sender = username;
                        String key = command[2];
                        server.forwardMessage(recipient, "SESSION_ACCEPT~" + sender + "~" + key);
                    }
                    break;
                    default: {
                        System.out.println("Not valid command." +
                                "\n LIST - request a list of other clients"
                        );
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
            close();
        } catch (NullPointerException e) {
            // e.printStackTrace();
            System.out.println("No messages incoming");
        }
    }

    /**
     * Returns the name of the client handler.
     *
     * @return name String
     */
    //@ ensures !\result.equals(null) && \result == name;
    public synchronized String getUsername() {
        return username;
    }

    public void sendUpdatetoAllClients(){
        String username = getUsername();
        for (ClientHandler client : server.getClients().values()) {
            if(!client.getUsername().equals(username)) {
                String user_command = "NEW_USER~" + username + "," + server.getPublicKeys().get(username);
                client.sendMessage(user_command); //add the username and key to the command
            }
        }
    }

    public void sendLists(){
        StringBuilder clients = new StringBuilder("LIST");
            Map<String, String> clientKeys = server.getPublicKeys();
            for (String user : server.getClients().keySet()) {
                    if(!user.equals(this.getUsername())) {
                        clients.append("~").append(user + "," + clientKeys.get(user));
                    }
                }
            System.out.println(clients.toString());
            sendMessage(clients.toString());
    }

    /**
     * Sets the setInQueue boolean to the given boolean.
     *
     * @param var boolean
     */
    //@ ensures isInQueue == var;
    public void setInQueue(boolean var) {
        isInQueue = var;
    }

    /**
     * Sets the setInGame boolean to the given boolean.
     *
     * @param var boolean
     */
    //@ ensures isInGame == var;
    public void setInGame(boolean var) {
        isInGame = var;
    }

    // /**
    //  * Sends the given move to the given player.
    //  *
    //  * @param sendTo Player
    //  * @param location int
    //  */
    //@ requires sendTo != null && location < -1;
    // public void sendMoveToPlayer(Player sendTo, int location) {
    //     for (ClientHandler ch : server.getClients()) {
    //         if (ch.getName().equals(sendTo.getName())) {
    //             ch.sendMessage("MOVE~" + location);
    //         }
    //     }
    // }
}
