

public class Entry{
    private String vendor;
    private String category;

    public Entry(String vendor){
        this.vendor = vendor;
        this.category = null;
    }

    public Entry(String vendor, String category){
        this.vendor = vendor;
        this.category = category;
    }

    public String getVendor(){
        return vendor;
    }

    public String getCategory(){
        return category;
    }

    public void setCategory(String category){
        if(this.category == null){
            this.category = category;
        }else{
            System.out.println("Warning: overwriting non-null category");
        }
    }
}


