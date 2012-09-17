import java.io.*;


public class prefixList{
  public static boolean prefix(int listA[], int sizeA, int listB[], int sizeB){
    for(int i = 0; i < sizeA; i++){
      if(listA[i] != listB[i]){
        return false;
      }
    }
    return true;
  }

  public static void main(String [] args){
    int listA[] = new int[500];
    int listB[] = new int[500];
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
    int sizeA = i-1;
    System.out.println("please enter another list element by element");
    i = 0;
    try{
      do{
        tempString = reader.readLine();
        num = Integer.parseInt(tempString);
        if(num > 0)
          listB[i] = num;
        i++;
      }while(num > 0);
    } catch (IOException e){}
    int sizeB = i-1;
    
    boolean result = prefix(listA, sizeA, listB, sizeB);
    if(result){
      System.out.println("The first list is the prefix of the second.");
    }
    else{
      System.out.println("The first list is not he prefix of the second.");
    }
    
  }
}
