// Testing computation of HMFs with nontrivial nebentypus
// using the definite method.

F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 150);

/* 
 * Compute a space of weight [2, 2] forms with quadratic nebentypus 
 * and check that the square of the space is contained within
 * the space of [4, 4] forms.
 */

k := [2, 2];
N := 4*Factorization(5*ZF)[1][1];
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;
assert Order(chi) eq 2;

M22chi := HMFSpace(M, N, k, chi);
S22chi := CuspFormBasis(M22chi);
M44 := HMFSpace(M, N, [4,4]);
S44 := CuspFormBasis(M44);
M22_squared := Basis(&cat[[f * g : g in S22chi] : f in S22chi]);
assert #LinearDependence(M22_squared) eq 0;
assert #LinearDependence(S44) eq 0;
assert #Intersection(M22_squared, S44) eq #M22_squared;

/* 
 * Compute a space of weight [3, 3] forms with quadratic nebentypus 
 * and check that they agree with the same space produced via
 * Hecke stability
 */

k := [3, 3];
N := ideal<ZF | 4*ZF.2 - 2>;
qq := 2*ZF;
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1;
assert HeckeCharLabel(chi) eq "-5.0.1_20.1_2u1u1.2u";
assert Order(chi) eq 2;

Mk := HMFSpace(M, N, k, chi);

Sk_def := CuspFormBasis(Mk);
Sk_hs := HeckeStabilityCuspBasis(Mk : Proof:=true, stable_only:=true);

assert #LinearDependence(Sk_def) eq 0;
assert #Sk_hs eq #Sk_def;
assert #LinearDependence(Sk_def cat Sk_hs) eq #Sk_def;
