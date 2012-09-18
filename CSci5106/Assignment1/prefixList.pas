program prefix(input, output);
  Type
    IntArray = array[1..500] of integer;
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
    repeat
      read(tempString);
      Val(tempString, num, code);
      if code <> 0 then
      begin
        write('Error, one of the numbers was not a valid number\n');
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
        write('Error, one of the numbers was not a valid number\n');
        Exit;
      end;
      listB[i] := num;
      i := i+1;
    until(num < 0);
    sizeB := i-1;
    result := prefix(listA, sizeA, listB, sizeB);
    if (result = true) then 
      write('The first list is the prefix of the second list\n');
    else 
      write('The first list is not the prefix of the secod list\n');


    
end.
