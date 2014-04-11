

public class Eddyscan{
    private int rows;
    private int cols;
    private double [][] data;

    public Eddyscan(int rows, int cols, double [][] data){
        this.rows = rows; this.cols = cols; this.data = data;
    }

    private boolean [][] image2BW(double thresh){
        boolean [][] res = new boolean [rows][cols];
        for(int i = 0; i < rows; i++){
            for(int j = 0; j < cols; j++){
                res[i][j] = data[i][j] <= thresh;
            }
        }
        return res;
    }

    public int [][] scan(){
        int [][] eddies = new int [rows][cols];

        boolean [][] bw = image2BW(thresh);
        ConnComp cc = new ConnComp(rows, cols, bw, data);
        eddies = cc.getComponents();

        for(int thresh = 100; thresh >= -100; thresh--){
            System.out.println("Executing threshold " + thresh);
            boolean [][] bw = image2BW(thresh);
            ConnComp cc = new ConnComp(rows, cols, bw, data);
            eddies = cc.getComponents();
            
        }
        return eddies;
    }

}
