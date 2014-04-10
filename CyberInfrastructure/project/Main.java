
import com.jmatio.io.*;
import com.jmatio.types.*;
import java.util.Map;


public class Main {
    
    static int years = 3;
    
    public static double[][] getTimeFrame(int i) throws Exception{
        try{
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
            
        }catch (Exception e){
            throw new Exception();
        }
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
                printMatrix(yearlyData[i], 5, 6);

            }
            
            
        }catch(Exception e){
            System.out.println("Exception caught, exiting...");
            return;
        }
    }
}
