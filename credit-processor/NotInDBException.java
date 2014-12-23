

class NotInDBException extends Exception{
    private Entry entry;

    public NotInDBException(Entry entry){
        this.entry = entry;
    }

    public Entry getEntry(){
        return entry;
    }
}


