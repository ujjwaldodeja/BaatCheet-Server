
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;

public class ServerUI {
    private static Server server = null;
 
    /**
     * Mainly receives the input from the user and act accordingly.
     * @param args String[]
     * @throws IOException Exception
     */
    public static void main(String[] args) throws IOException {

        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        System.out.println(InetAddress.getLocalHost());
        String name = "BaatCheet's Server";
        int port = 8080;
        // System.out.println("Give port number");
        // int port = 0;
        // try {
        //     port = Integer.parseInt(reader.readLine());
        // } catch (NumberFormatException e) {
        //     e.printStackTrace();
        // }

        //starts the server
        if (port > 0) {
            server = new Server(port, name);
            server.start();
        }

        System.out.println("\nCommands:" +
                "\n LIST_C - prints out all clients connected to the server" +
                "\n LIST_Q - prints out all clients in the queue" +
                "\n QUIT - stops the server\n");

        boolean sw = true;
        while (sw) {
            String line = reader.readLine();
            switch (line) {
                case "LIST_C": {
                    for (String username : server.getClients().keySet()) {
                        System.out.println(username);
                    }
                }
                break;
                case "LIST_Q": {
                    for (ClientHandler ch : server.getQueue()) {
                        System.out.println(ch.getUsername());
                    }
                }
                break;
                case "QUIT": {
                    server.stop();
                    System.out.println("Server was stopped manually.");
                    sw = false;
                }
                break;
                default: {
                    System.out.println("\nCommands:" +
                            "\n LIST_C - prints out all clients connected to the server" +
                            "\n LIST_Q - prints out all clients in the queue" +
                            "\n QUIT - stops the server\n");
                }
            }
        }
    }
}
