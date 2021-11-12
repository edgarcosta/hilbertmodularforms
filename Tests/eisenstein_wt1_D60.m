printf "Testing Eisenstein series of weight 1...";
D := 60;
F := QuadraticField(D);
ZF := Integers(F);
prec := 3; // 62 coeffs
M := GradedRingOfHMFs(F, prec);
N := 1*ZF;
X := HeckeCharacterGroup(N, [1,2]);
M1 := HMFSpace(M, N, [1,1], X.2);
E1 := EisensteinBasis(M1);
M2 := HMFSpace(M, N, [1,1], X.2*X.1);
E2 := EisensteinBasis(M2);
assert #E1 eq 2;
assert #E2 eq 2;
assert E1[1]*E2[1] eq E1[2]*E2[2];
print "Success!";
return true;

