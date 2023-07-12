/*
# about 1min
parallel magma -b D:={} scripts/generate_box.m  ::: {0..3000} > group_labels.txt
time parallel -a data/group_labels.txt --joblog data/joblog/lmfdb_invariants_table.log -j 200 --eta magma -b label:={} scripts/generate_lmfdb_invariants_table.m  > data/lmfdb_invariants_table.txt
*/


AttachSpec("spec");
SetClassGroupBounds("GRH");

if assigned debug then
  SetDebugOnError(true);
end if;

if assigned label then
  if label eq "header" then
    print WriteInvariantsHeader();
    exit 0;
  else
    G := LMFDBCongruenceSubgroup(label);
    try
      print WriteInvariantsRow(label);
      exit 0;
    catch e
      WriteStderr(Sprintf("Failed WriteLMFDBRow for %o\n", label));
      WriteStderr(e);
      exit 1;
    end try;
  end if;
else
  WriteStderr("Label is a necessary argument\n");
  exit 1;
end if;
