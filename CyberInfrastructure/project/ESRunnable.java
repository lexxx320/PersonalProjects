import com.jmatio.io.*;
import com.jmatio.types.*;
import java.util.Map;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.Semaphore;

public class ESRunnable implements Runnable{
    private int years;
    private AtomicInteger currentWeek;
    private Semaphore ioLock;

    private static int rows = 721;
    private static int cols = 1440;
    
    public ESRunnable(int years, AtomicInteger counter, Semaphore ioLock){
        this.years = years; currentWeek = counter; this.ioLock = ioLock;
    }

    public static double[][] getTimeFrame(int i) throws Exception{
        String f = "data/ssh" + i + ".mat";
        MatFileReader mfr = new MatFileReader(f);
        Map<String, MLArray> contents = mfr.getContent();
        
        MLArray data = contents.get("ssh");
        if(data == null){
            System.out.println("No data field in mat file\n");
            throw new Exception();
        }   
        MLDouble matrix = (MLDouble)data;
        double [][] rawMatrix = matrix.getArray();
        System.out.println("Releasing lock");
        return rawMatrix;
    }

    public static long[][] intToLong(int[][] a, int x, int y){
        long[][] b = new long[x][y];
        for(int i = 0; i < x; i++){
            for(int j = 0; j < y; j++){
                b[i][j] = (long)a[i][j];
            }
        }
        return b;
    }

    public static void writeTimeFrame(int i, int [][] eddies) throws Exception{
        System.out.println("Acquired lock, writing week " + i);
        String f = "output/eddies" + i + ".mat";
        long[][] longData = intToLong(eddies, rows, cols);
        MLInt64 mlarray = new MLInt64("eddies", longData);
        
        ArrayList<MLArray> list = new ArrayList<MLArray>();
        list.add(mlarray);

        MatFileWriter mfw = new MatFileWriter();
        mfw.write(f, list);
        System.out.println("Releasing lock");
    }

    public static void printMatrix(double [][] data, int x, int y){
        for(int i=0; i < x; i++){
            for(int j = 0; j < y; j++){
                System.out.println("data[" + i + "][" + j + "] = " + data[i][j]);
            }
        }
        System.out.println("\n");
    }

    public void run(){
        int localWeek = currentWeek.getAndIncrement();
        try{
            while(localWeek <= years){
                System.out.println("Executing week: " + localWeek);
                double[][] data = getTimeFrame(localWeek);
                Eddyscan es = new Eddyscan(rows, cols, data);
                int [][] eddies = es.scan();
                writeTimeFrame(localWeek, eddies);
                localWeek = currentWeek.getAndIncrement();
            }
        }catch(Exception e){
            System.out.println("Exception caught, exiting...");
            return;
        }
            
    }
}











