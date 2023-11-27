/*
# about 1min
time parallel magma -b D:={} scripts/generate_box.m  ::: {0..10000} > data/group_labels.txt
for table in invs elliptic cusps; do
echo ${table}; time parallel -a data/group_labels.txt --joblog data/joblog/lmfdb_${table}_table.log -j 200 --eta magma -b -S 0 table:=${table} label:={} scripts/generate_lmfdb_tables.m  > data/lmfdb_${table}_table.txt; done
*/


AttachSpec("spec");
SetClassGroupBounds("GRH");

if assigned debug then
  SetDebugOnError(true);
end if;


handlers := [elt : elt in
  [*
  <"invs", WriteInvariantsHeader, WriteInvariantsRow>,
  <"elliptic", WriteElllipticPointsHeader, WriteElllipticPointsRows>,
  <"cusps", WriteCuspsHeader, WriteCuspsRows>
  *]
  | table eq elt[1]][1];
if assigned label then
  if label eq "header" then
    print handlers[2]();
    exit 0;
  else
    G := LMFDBCongruenceSubgroup(label);
    try
      out := handlers[3](label);
      if #out gt 0 then print out; end if;
      exit 0;
    catch e
      WriteStderr(Sprintf("Failed %o for %o\n", GetIntrinsicName(handlers[3]), label));
      WriteStderr(e);
      exit 1;
    end try;
  end if;
else
  WriteStderr("Label is a necessary argument\n");
  exit 1;
end if;
