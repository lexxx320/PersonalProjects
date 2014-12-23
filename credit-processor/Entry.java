

public class Entry{
    private String vendor;
    private String category;
    private double amount;

    public Entry(String vendor, double amount){
        this.vendor = vendor;
        this.category = null;
        this.amount = amount;
    }

    public Entry(String vendor, String category, double amount){
        this.vendor = vendor;
        this.category = category;
        this.amount = amount;
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

    public double getAmount(){
        return amount;
    }
}


