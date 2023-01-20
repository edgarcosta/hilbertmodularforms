// Verifying Theorem 3.3 in vdG.

printf "Verifying Theorem 3.3 in vdG D=";
for D in [13,17,24,28,33] do
  printf "%o ", D;
  F := QuadraticField(D);
  gamma := Gamma0(F, 1*Integers(F), 1*Integers(F));
  assert KodairaDimensionPossibilities(gamma) eq [-1];
end for;

for D in [29,37,40,41,44,56,57,69, 105] do
  printf "%o ", D;
  F := QuadraticField(D);
  gamma := Gamma0(F, 1*Integers(F), 1*Integers(F));
  assert KodairaDimensionPossibilities(gamma) eq [0,1];
end for;

for D in [53,61,65,73,76,77,85,88,92,93,120,140,165] do
  printf "%o ", D;
  F := QuadraticField(D);
  gamma := Gamma0(F, 1*Integers(F), 1*Integers(F));
  assert KodairaDimensionPossibilities(gamma) eq [1];
end for;


// for D in [5, 13, 17,21,24,28,33,60] do
//   print D;
//   F := QuadraticField(D);
//   gamma := Gamma0(F, 1*Integers(F), 1*Integers(F));
//   RationalityCriterion(gamma);
// end for;
