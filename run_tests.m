// usage: magma target:=SUBSTRING (debug:=) run_tests.m
load "config.m";
if assigned filename then
  tests := [filename];
else
  tests := Split(Pipe("ls Tests", ""), "\n");
end if;
if assigned debug then
  SetDebugOnError(true);
end if;
if assigned verbose then
  SetVerbose("HilbertModularForms", StringToInteger(verbose));
end if;
failed := [];
if not assigned target then
  target := "";
end if;

for filename in tests do
  if target in filename then
    fullPath := "Tests/" cat filename;
    timestamp := Time();
    if assigned debug then
      printf "%o: ", filename;
      assert eval (Read(fullPath) cat  "return true;");
      printf "Success! %o s\n", Time(timestamp);
    else
      try
        printf "%o: ", filename;
        assert eval (Read(fullPath) cat  "return true;");
        printf "Success! %o s\n", Time(timestamp);
      catch e
        Append(~failed, filename);
        printf "Fail! %o s\n %o\n", e, Time(timestamp);;
      end try;
    end if;
  end if;
end for;
if #failed gt 0 then
  print "Tests failed:";
  for f in failed do
    print f;
  end for;
end if;
exit #failed;

