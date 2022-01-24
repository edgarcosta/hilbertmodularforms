// usage: magma target:=SUBSTRING run_tests.m

tests := Split(Pipe("ls Tests", ""), "\n");
load "config.m";
failed := [];
if not assigned target then
  target := "";
end if;

for filename in tests do
  if target in filename then
    fullPath := "Tests/" cat filename;
    timestamp := Time();
    try
      printf "%o: ", filename;
      assert eval Read(fullPath);
      printf "Success! %o s\n", Time(timestamp);
    catch e
      Append(~failed, filename);
      printf "Fail! %o s\n %o\n", e, Time(timestamp);;
    end try;
  end if;
end for;
if #failed gt 0 then
  print "Tests failed:";
  for f in failed do
    print f;
  end for;
end if;
