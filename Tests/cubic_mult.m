// tests multiplication for HMFs over cubic fields 
// 
// checks that the square of an Eisenstein series of parallel weight 1
// lies in the computed space of [2,2,2] forms. 
//
// TODO abhijitm - this test will be made more robust once we can compute
// cusp spaces for weights beyond parallel weight 2. 

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 150);
N := 3*ZF;
M222 := HMFSpace(M, N, [2,2,2]);
B222 := Basis(M222);
H := HeckeCharacterGroup(N, [1,2,3]);
chi := H.1;
assert Order(chi) eq 2;
M111 := HMFSpace(M, N, [1,1,1], chi);
E111 := EisensteinBasis(M111);
E111_squared := [f^2 : f in E111];  
assert #Intersection(E111_squared, B222) eq #E111_squared;
