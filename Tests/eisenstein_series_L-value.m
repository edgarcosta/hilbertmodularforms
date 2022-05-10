printf "Testing that the Eisenstein series code works when image of character is not codomain..."; //use printf with no \n
// Create the graded ring
F:=QuadraticField(5);
prec:=10;
M:=GradedRingOfHMFs(F, prec);

// Create the Eisenstein series
ZF:=Integers(F);
N:= 23*ZF;
H := HeckeCharacterGroup(N, [1,2]);
chi := (H.1^11); // aka 11 mod 22
assert Order(chi) eq 2;
Mchi := HMFSpace(M, N, [1,1], chi);

B :=  EisensteinBasis(Mchi);

//In the future, add further check of coefficients
