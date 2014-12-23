import java.io.*;
import java.util.*;

class FileProcessor{
    private CreditDB db;
    private BufferedReader reader;
    private LinkedList<Entry> contents;  //contents of file
    private ListIterator<Entry> current; //pointer to next element to be processed
    private LinkedList<Entry> unknown;   //items we ask the user to figure out

    //Constructor
    public FileProcessor(File f) throws FileNotFoundException, IOException{
        contents = new LinkedList<Entry>();
        unknown = new LinkedList<Entry>();
        db = new CreditDB(); //reads credit-database.txt file
        reader = new BufferedReader(new FileReader(f));
        String nextLine = reader.readLine();
        while(nextLine != null){
            //process line and add it to linked list (contents)
            nextLine = reader.readLine();
        }
        current = contents.listIterator(0);
    }

    public void process() throws NotInDBException {
        while(current.hasNext()){
            Entry entry = current.next(); //next entry to be processed
            if(db.inDB(entry)){
                //lookup category in database
            }else{
                //Not in database...prompt user for input
                throw new NotInDBException(entry);
            }
        }
    }

    public void processWith(Entry entry, String category) {
        //extend database
        //update current linked list
    }

    //Done processing?
    public boolean done(){
        return !current.hasNext();
    }
    
}
