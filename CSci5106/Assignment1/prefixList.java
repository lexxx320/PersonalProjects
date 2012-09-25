import java.io.*;

/****************************************************************
Program Description:
This function reads in a list using the getList method, which fills
out the elements of the list, and then returns the number of elements
read in by the stdin.  The program then calls the prefixList function, 
which returns whether or not the n elements in the first list make up
the first n elements in the second list.
*****************************************************************/

public class prefixList{
  public static boolean prefix(int listA[], int sizeA, int listB[], int sizeB){
    for(int i = 0; i < sizeA; i++){
      if(listA[i] != listB[i]){
        return false;
      }
    }
    return true;
  }

  public static int getList(int listA[]){
    int i = 0;
    int num = 0;
    String tempString;
    BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
    System.out.println("please enter a list element by element that is terminated by a negative number");
    try{
      do{
        tempString = reader.readLine();
        num = Integer.parseInt(tempString);
        if(num > 0)
          listA[i] = num;
        i++;
      }while(num > 0);
    } catch (IOException e){}
    return i-1;
  }

  public static void main(String [] args){
    int listA[] = new int[500];
    int listB[] = new int[500];
    
    int sizeA = getList(listA);
    int sizeB = getList(listB);
    
    boolean result = prefix(listA, sizeA, listB, sizeB);
    if(result){
      System.out.println("The first list is the prefix of the second.");
    }
    else{
      System.out.println("The first list is not he prefix of the second.");
    }
    
  }
}
