import java.io.IOException;

public class main {

    public static void main(String[] args) throws IOException {
        long startTime = System.nanoTime();
        readBPMNToConsole reader = new readBPMNToConsole();

        reader.printToAlloy("p1.bpmn");
        long endTime   = System.nanoTime();
        long totalTime = endTime - startTime;
        System.out.println("Runtime is: " + totalTime + " nanoseconds.");
    }
}
