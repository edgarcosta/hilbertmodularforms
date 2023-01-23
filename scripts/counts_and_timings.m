// counts
recs_all := ReadRecords("/scratch/home/sschiavo/github/hilbertmodularsurfacesdata/GL_Gamma0_lt3000_cut5000_kposs.txt");
//recs_all := ReadRecords("/scratch/home/sschiavo/github/hilbertmodularsurfacesdata/SL_Gamma0_lt3000_cut5000_kposs.txt");
recs_str := [rec : rec in recs_all | (not "SKIPPED" in rec) and (not "FAILED" in rec)];
recs := [];
for rec in recs_str do
  label := rec[1];
  poss := eval rec[2];
  Append(~recs, [* label, poss *]);
end for;
#recs_all;
#recs_str;
#recs;
unique := [el : el in recs | #el[2] eq 1];
#unique;
unclear:= [el : el in recs | #el[2] gt 1];
#unclear;

counts := AssociativeArray();
for el in unique do
  if el[2] in Keys(counts) then
    counts[el[2]] +:= 1;
  else
    counts[el[2]] := 1;
  end if;
end for;

for k in Keys(counts) do
  print k;
  print counts[k];
  print "-----------------------";
end for;

counts := AssociativeArray();
for el in unclear do
  if el[2] in Keys(counts) then
    counts[el[2]] +:= 1;
  else
    counts[el[2]] := 1;
  end if;
end for;

for k in Keys(counts) do
  print k;
  print counts[k];
  print "-----------------------";
end for;

for el in higher do
  G := LMFDBCongruenceSubgroup(el[1]);
  printf "chi = %o, K^2 = %o\n", ArithmeticGenus(G), K2(G);
end for;

// shell script for timings
for i in joblog/*  ; do echo $i; awk -v OFMT=%.17g -F' ' '{sum+=$4;} END{print sum;}' $i; done

