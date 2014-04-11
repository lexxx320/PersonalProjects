import com.jmatio.io.*;
import com.jmatio.types.*;
import java.util.Map;
import java.util.ArrayList;


public class Main {
    
    static int years = 1;
    
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
        String f = "output/ssh" + i + ".mat";
        long[][] longData = intToLong(eddies, 721, 1440);
        MLInt64 mlarray = new MLInt64("ssh", longData);
        
        ArrayList<MLArray> list = new ArrayList<MLArray>();
        list.add(mlarray);

        MatFileWriter mfw = new MatFileWriter();
        mfw.write(f, list);

    }

    public static void printMatrix(double [][] data, int x, int y){
        for(int i=0; i < x; i++){
            for(int j = 0; j < y; j++){
                System.out.println("data[" + i + "][" + j + "] = " + data[i][j]);
            }
        }
        System.out.println("\n");
    }

    public static void main(String[] args) {
        MLArray data;
        try{
            double [][][] yearlyData = new double[years][][];
            for(int i=0; i < years; i++){
                yearlyData[i] = getTimeFrame(i+1);
                Eddyscan es = new Eddyscan(721, 1440, yearlyData[i]);
                int [][] eddies = es.scan();
                writeTimeFrame(i+1, eddies);
            }
        }catch(Exception e){
            System.out.println("Exception caught, exiting...");
            return;
        }
    }
}
