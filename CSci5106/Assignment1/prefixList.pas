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
  function readList(list : IntArray) : Integer;
  var
    i : Integer;
  begin
    i := 0;
    writeln('Please enter a list element by element terminated by a negative number');
    repeat
      readln(tempString);
      Val(tempString, num, code);
      if code <> 0 then
      begin
        writeln('Error, one of the numbers was not a valid number');
        Exit;
      end;
      list[i] := num;
      i := i+1;
    until(num < 0);
    readList := i-1;
  end;
  //Main Function
  Begin
    
    sizeA := readList(listA);
    sizeB := readList(listB);
    result := prefix(listA, sizeA, listB, sizeB);
    if result = true then 
      writeln('The first list is the prefix of the second list')
    else 
      writeln('The first list is not the prefix of the second list')


    
end.
