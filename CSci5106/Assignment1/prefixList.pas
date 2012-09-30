{-------------------------------------------
Matthew Le
3975089
lexxx320

Progam Description:
This program reads in two lists of funbers, using the 
getList function, which enters the numbers into the list
as they are read from the terminal, returning the number
of elements entered by the user.  The listPrefix function
then checks to see if all of the elements of the first list
make up the first n elements of the second list, where n is 
the number of elements of the first list.
---------------------------------------------------}

program prefix;
  Type
    IntArray = array[0..499] of integer;
  Var
    listA : IntArray;
    listB : IntArray;
    sizeA : Integer;
    sizeB : Integer;
    i : Integer;
    tempString : String(255);
    num : Integer;
    code : Integer;
    result : Boolean;
    //Prefix Function
  function prefix(listA : IntArray; sizeA : Integer; listB : IntArray; sizeB : Integer) : boolean;
  var
    i : Integer;
    n : Integer;
  begin
    writeln('Entering prefix function');
    writeln(sizeA);
    writeln(sizeB);
    prefix := true;
    n := sizeA - 1;
    for i := 0 to n do
      begin
        writeln(listA[i]);
        writeln(listB[i]);
        if listA[i] <> listB[i] then 
          prefix := false;
    end;
  end;
  //Read list function
  function readList() : IntArray;
  var
    i : Integer;
    j : Integer;
    list : IntArray;
  begin
    i := 0;
    writeln('Please enter a list element by element terminated by a negative number');
    repeat
      readln(tempString);
      Val(tempString, num, code);
      if code <> 0 then
      begin
        writeln('Error, one of the numbers was not a valid number');
        exit;
      end;
      list[i] := num;
      i := i+1;
    until(num < 0);
    for j := 0 to i-1 do
      writeln(list[j]);
    
    readList := list;
  end;
  function getSize(list : IntArray) : Integer;
  var
    i : Integer;
    count : Integer;
  begin
    count := 0;
    while list[i] > 0 do
    begin
      
       count := count+1;
       i := i+ 1;
    end;
    getSize := count;
  end;
  //Main Function
  Begin
    listA := readList();
    listB := readList();
    sizeA := getSize(listA);
    sizeB := getSize(listB);
    result := prefix(listA, sizeA, listB, sizeB);
    if result = true then 
      writeln('The first list is the prefix of the second list')
    else 
      writeln('The first list is not the prefix of the second list')


    
end.
