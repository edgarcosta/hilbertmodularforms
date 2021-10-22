tests := [
  "e2_Qsqrt13.m",
  "Theta_Qsqrt13.m"
  ];
AttachSpec("ModFrmHilD/spec");
failed := [];
for filename in tests do
  fullPath := "Tests/" cat filename;
  try
    printf "%o: ", filename;
    assert eval Read(fullPath);
    printf "Success!\n";
  catch e
    Append(~failed, filename);
    printf "Fail!\n";
  end try;
end for;
if #failed gt 0 then
  print "Tests failed:";
  for f in failed do
    print f;
  end for;
end if;
