import java.util.Stack;

public class ConnComp{

    private static int rows;
    private static int cols;
    private static boolean [][] bw;
    private static int [][] ccs;
    private static double [][] data;

    public ConnComp(int rows, int cols, boolean [][] bw, double [][] data){
        this.rows = rows; this.cols = cols; this.bw = bw;
        ccs = new int [rows][cols]; this.data = data;
    }

    public updateBW(boolean [][] bw){
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
        int label = 1;
        for(int i = 0; i < rows; i++){
            for(int j = 0; j < cols; j++){
                /*Analyze a connected component*/
                if(bw[i][j] && ccs[i][j] == 0){
                    System.out.println("Beginning CC");
                    int count = 0;
                    double perim = 0.0;
                    double min = Double.MAX_VALUE;
                    xStack.push(i); yStack.push(j);
                    while(!xStack.empty()){
                        int x = xStack.pop(); 
                        int y = yStack.pop();
                        if(x>=0&&x<rows&&y>=0&&y<cols&&bw[x][y]&&ccs[x][y]==0){
                            count++;
                            eraseX.push(x); eraseY.push(y);
                            ccs[x][y] = label;
                            boolean p = perimiter(x, y);
                            perim += p ? data[x][y] : 0.0;
                            min = data[x][y] < min ? data[x][y] : min;
                            xStack.push(x-1); yStack.push(y);
                            xStack.push(x+1); yStack.push(y);
                            xStack.push(x); yStack.push(y-1);
                            xStack.push(x); yStack.push(y+1);
                        }
                    }
                    double amp = (perim / count) - min;
                    System.out.println("perim = " + perim + ", count = " + count + 
                        ", min = " + min + ", amp = " + amp + ", avg perim = " + perim/count);
                    System.out.println("count = " + count + ", amplitude = " + amp);
                    if(count > 8 || count <= 1000 && amp >= 1){
                        for(int k = 0; k < count; k++){
                            eraseX.pop(); eraseY.pop();
                        }
                        label++;
                    }
                    System.out.println("Done with CC, size = " + count);
                }
            }
        }
        erasePixels(eraseX, eraseY);
        return ccs;
    }
}
