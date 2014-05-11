import java.util.Stack;

public class ConnComp{

    private int rows;
    private int cols;
    private boolean [][] bw;
    private int [][] ccs;
    private double [][] data;
    private int label;

    public ConnComp(int rows, int cols, boolean [][] bw, double [][] data){
        this.rows = rows; this.cols = cols; this.bw = bw;
        ccs = new int [rows][cols]; this.data = data;
        label = 1;
    }

    public void updateBW(boolean [][] bw){
        this.bw = bw;
    }

    public void print(){
        for(int i = 0; i < rows; i++){
            for(int j = 0; j < cols; j++){
                System.out.print(ccs[i][j] + ", ");
            }
            System.out.print("\n");
        }
    }

    /*Reset the labels of a connected component to zero*/
    private void erasePixels(Stack<Integer> xStack, Stack<Integer> yStack){
        while(!xStack.empty()){
            int x = xStack.pop(); int y = yStack.pop();
            ccs[x][y] = 0;         
        }
    }

    /*Check if a point is on the perimeter of a connected component*/
    private boolean perimiter(int i, int j){
        int xUp = Math.min(rows-1, i+1); int xLow = Math.max(0, i-1);
        int yUp = Math.min(cols-1, j+1); int yLow = Math.max(0, j-1);
        return bw[xLow][yLow] == false || 
               bw[xLow][j] == false ||
               bw[xLow][yUp] == false ||
               bw[i][yLow] == false ||
               bw[i][j] == false ||
               bw[i][yUp] == false || 
               bw[xUp][yLow] == false || 
               bw[xUp][j] == false ||
               bw[xUp][yUp] == false;
    }
    
    /*Stack based connected component algorithm*/
    public int [][] getComponents(){
        Stack<Integer> xStack = new Stack<Integer>();
        Stack<Integer> yStack = new Stack<Integer>();
        Stack<Integer>eraseX = new Stack<Integer>(); 
        Stack<Integer>eraseY = new Stack<Integer>();
        for(int i = 0; i < rows; i++){
            for(int j = 0; j < cols; j++){
                /*Analyze a connected component*/
                if(bw[i][j] && ccs[i][j] == 0){
                    int count = 0; int perimCount = 0;
                    double perim = 0.0;
                    double min = Double.MAX_VALUE;
                    xStack.push(i); yStack.push(j);
                    while(!xStack.empty()){
                        int x = xStack.pop(); 
                        int y = yStack.pop();
                        if(x>=0&&x<rows&&y>=0&&y<cols&&bw[x][y]&&ccs[x][y]==0){
                            count++;
                            eraseX.push(x); eraseY.push(y);
                            boolean p = perimiter(x, y);
                            ccs[x][y] = label;
                            perim += p ? data[x][y] : 0.0;
                            perimCount += p ? 1 : 0;
                            min = data[x][y] < min ? data[x][y] : min;
                            xStack.push(x-1); yStack.push(y);
                            xStack.push(x+1); yStack.push(y);
                            xStack.push(x); yStack.push(y-1);
                            xStack.push(x); yStack.push(y+1);
                        }
                    }
                    double amp = (perim / perimCount) - min;
                    if(count > 8 && count < 1000 && amp >= 1){
                        //Remove pixels from erase stack
                        for(int k = 0; k < count; k++){
                            eraseX.pop(); eraseY.pop();
                        }
                        label++;
                    }
                }
            }
        }
        erasePixels(eraseX, eraseY);
        return ccs;
    }
}
