// At this level, there's a nontrivial oldspace,
// and this test checks that the degeneracy operators
// work properly. It does not test the Atkin-Lehner operator.

F := QuadraticField(5);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 150);
N := 6*ZF;
k := [3,3];
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;
assert Order(chi) eq 2;

Mk := HMFSpace(M, N, k, chi);
Sk := CuspFormBasis(Mk);


Sk_hs := HeckeStabilityCuspBasis(Mk : stable_only:=true, Proof:=true);

assert #Intersection(Sk, Sk_hs) eq #Sk;
assert #Sk eq 4;
