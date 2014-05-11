import com.jmatio.io.*;
import com.jmatio.types.*;
import java.util.Map;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.lang.String;
import java.util.concurrent.Semaphore;


public class Main {

    
    public static void main(String[] args) { 

        int numWeeks = 2;

        Semaphore IOLock = new Semaphore(1);

        AtomicInteger currentWeek = new AtomicInteger(1);
        int cores = Runtime.getRuntime().availableProcessors();
        for(int i = 0; i < cores; i++){
            System.out.println("Spawning thread");
            ESRunnable thread = new ESRunnable(numWeeks, currentWeek, IOLock);            
            new Thread(thread).start();
        }
    }
}


















