program prefix(input, output);
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
  function prefix(listA : IntArray; sizeA : Integer; listB : IntArray; sizeB : Integer) : boolean;
  var
    i : Integer;
  begin
    prefix := true;
    for i := 0 to sizeA do
    begin
      if listA[i] <> listB[i] then 
        prefix := false;
    end;
  end;
  Begin
    i := 0;
    writeln('Please enter a list element by element terminated by a negative number');
    repeat
      writeln('reading number');
      read(tempString);
      Val(tempString, num, code);
      writeln(code);
      if code <> 0 then
      begin
        writeln('Error, one of the numbers was not a valid number');
        Exit;
      end;
      listA[i] := num;
      i := i+1;
    until(num < 0);
    sizeA := i-1;
    i := 0;
    repeat
      read(tempString);
      Val(tempString, num, code);
      if code <> 0 then
      begin
        writeln('Error, one of the numbers was not a valid number');
        Exit;
      end;
      listB[i] := num;
      i := i+1;
    until(num < 0);
    sizeB := i-1;
    result := prefix(listA, sizeA, listB, sizeB);
    if result = true then 
      writeln('The first list is the prefix of the second list')
    else 
      writeln('The first list is not the prefix of the secod list')


    
end.
