// TODO abhijitm right now, this test needs to be run
// while forcing the indefinite algorithm, since the definite
// algorithm throws an error in this case.
//
// This test takes several hours on my machine, so it's not 
// included in the standard suite right now.
R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

prec := 222;
M := GradedRingOfHMFs(F, prec);
N := ideal<ZF | 6*ZF.1 - 3*ZF.2 - 2*ZF.3>;
k := [1,1,3];
chi := HeckeCharacterGroup(N, [1,2,3]).1;

Mk := HMFSpace(M, N, k, chi);
Sk := HeckeStabilityCuspBasis(Mk : prove:=false, stable_only:=true);
Dk := DihedralBasis(Mk);

assert #Sk eq 1;
assert #Dk eq 1;

// the unique cusp form in this space is dihedral
assert #LinearDependence([Sk[1], Dk[1]]) eq 1;

