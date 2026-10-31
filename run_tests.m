// usage: magma [filename:=PATH | target:=SUBSTRING] exitsignal:=BOOL run_tests.m
// filename:=PATH runs that one file, e.g. Tests/foo.m or examples/slow/foo.m.
// target:=SUBSTRING runs the files in Tests/, examples/ and their slow/ subdirectories
//   whose path contains SUBSTRING.
// With neither, it runs every file directly in Tests/ and examples/, without slow/.
if assigned filename then
  tests := [filename];
elif assigned target and target ne "" then
  tests := Split(Pipe("ls Tests/*.m Tests/slow/*.m examples/*.m examples/slow/*.m 2>/dev/null",
                      ""), "\n");
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
