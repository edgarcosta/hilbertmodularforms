// usage: magma target:=SUBSTRING exitsignal:=BOOL run_tests.m
// filename and target are full relative paths, e.g. Tests/foo.m or examples/foo.m
if assigned filename then
  tests := [filename];
else
  tests := Split(Pipe("ls Tests/*.m examples/*.m 2>/dev/null", ""), "\n");
end if;
if assigned debug then
  SetDebugOnError(true);
end if;
_ := eval (Read("config.m") cat  "return true;");
//load "config.m";
if assigned verbose then
  try
    verbose := StringToInteger(verbose);
  catch e
    verbose := 1;
  end try;
  SetVerbose("HilbertModularForms", verbose);
end if;
failed := [];
if not assigned target then
  target := "";
end if;

counter := 0;
for filename in tests do
  if target in filename then
    counter +:=1;
    fullPath := filename;
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
if counter eq 0 then
  print "No matching target";
  exit 1;
end if;
if #failed gt 0 then
  print "Tests failed:";
  for f in failed do
    print f;
  end for;
end if;
if assigned exitsignal then
  exit #failed;
end if;
