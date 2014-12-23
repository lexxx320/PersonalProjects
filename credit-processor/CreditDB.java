import java.util.*;
import java.io.*;

public class CreditDB{
    private HashMap<String, String> db;

    public CreditDB(){
        db = new HashMap<String, String>();
        try{
            File creditDBFile = new File("credit-database.txt");
            BufferedReader reader = new BufferedReader(new FileReader(creditDBFile));
            String nextLine = reader.readLine();
            while(nextLine != null){
                //processLine
                nextLine = reader.readLine();
            }
        }catch(Exception e){
            System.out.println("Couldn't open file\n");
            //TODO: create credit-database.txt file
        }
    }   

    public boolean inDB(Entry entry){
        return db.containsKey(entry.getVendor());
    }
    
}
