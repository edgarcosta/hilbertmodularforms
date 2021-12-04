tests := Split(Pipe("ls Tests", ""), "\n");
AttachSpec("ModFrmHilD/spec");
failed := [];
for filename in tests do
  fullPath := "Tests/" cat filename;
  timestamp := Time();
  try
    printf "%o: ", filename;
    assert eval Read(fullPath);
    printf "Success! %o s\n", Time(timestamp);
  catch e
    Append(~failed, filename);
    printf "Fail! %o s\n", Time(timestamp);;
  end try;
end for;
if #failed gt 0 then
  print "Tests failed:";
  for f in failed do
    print f;
  end for;
end if;
