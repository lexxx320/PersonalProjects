/**
* A database that maps vendors to their categories
*/
import java.util.*;
import java.io.*;

public class CreditDB{
    private HashMap<String, String> db;

    public CreditDB(){
        db = new HashMap<String, String>();
        try{
            File creditDBFile = new File("credit-database.txt");
            if(!creditDBFile.exists()){
                creditDBFile.createNewFile();
            }
            BufferedReader reader = new BufferedReader(new FileReader(creditDBFile));
            String nextLine = reader.readLine();
            while(nextLine != null){
                //processLine
                nextLine = reader.readLine();
            }
        }catch(FileNotFoundException e){
            System.out.println("Couldn't open credit DB: " + e.getMessage());
            
        }catch(IOException e){
            System.out.println("CreditDB IO Error: " + e.getMessage());
        }
    }   

    //determines if an entry exists in the database
    public boolean inDB(Entry entry){
        return db.containsKey(entry.getVendor());
    }

    //lookup the value of a key in the database
    public String lookup(Entry entry){
        return db.get(entry.getVendor());
    }

    //extend the database with this mapping
    public void extend(Entry entry, String category){
        db.put(entry.getVendor(), category);
    }   
    
}
