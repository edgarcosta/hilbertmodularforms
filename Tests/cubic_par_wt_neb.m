R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

prec := 50;
M := GradedRingOfHMFs(F, prec);
N := 3*ZF;
chi := HeckeCharacterGroup(N, [1,2,3]).1;
k := [3,3,3];

M111chi := HMFSpace(M, N, [1,1,1], chi);
E111chi := EisensteinBasis(M111chi);

M333chi := HMFSpace(M, N, [3,3,3], chi);
S333chi := CuspFormBasis(M333chi);

M222 := HMFSpace(M, N, [2,2,2]);
S222 := CuspFormBasis(M222);

M444 := HMFSpace(M, N, [4,4,4]);
S444 := CuspFormBasis(M444);

assert #LinearDependence(S444) eq 0;
assert #LinearDependence(S333chi) eq 0;
assert #S222 eq 1;
assert #E111chi eq 1;
assert #S333chi eq 3;

// TODO abhijitm maybe add a check that everything in S333chi is
// a base change form?

f := S222[1];
g := E111chi[1];

assert #Intersection([f * g], S333chi) eq 1;
assert #Intersection([h * g : h in S333chi], S444) eq 3;
