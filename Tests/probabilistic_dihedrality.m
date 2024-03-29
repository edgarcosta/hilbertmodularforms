F := QuadraticField(5);
prec := 180;
M := GradedRingOfHMFs(F, prec);
N := 23*Integers(F);
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1^11;
Mk := HMFSpace(M, N, [1,1], chi);
Sk := CuspFormBasis(Mk);
assert #Sk eq 1;
f := Sk[1];
assert ProbabilisticDihedralTest(f);
