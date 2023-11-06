// Given a weight [1,1] Eisenstein series E with quadratic nebentypus, 
// and writing S_24 and S_46 for the weight [2,4] and [4,6] cusp forms,
// checks that S_24 * E^2 is contained in S_46 and that
// applying Hecke stability to S_46/E^2 recovers S_24. 

F := QuadraticField(5);
ZF := Integers(F);
prec := 11;
pp := 2*ZF;
M := GradedRingOfHMFs(F, prec);
triv_char := HeckeCharacterGroup(1*ZF, [1,2]).0;

N := Factorization(41*ZF)[1][1];
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;

M11chi := HMFSpace(M, N, [1,1], chi);
eis := EisensteinSeries(M11chi, chi, triv_char);

k_lo := [2,4];
k_hi := [4,6];

M_lo := HMFSpace(M, N, k_lo);
M_hi := HMFSpace(M, N, k_hi);

B_hi := CuspFormBasis(M_hi);
B_lo := CuspFormBasis(M_lo);

// B_lo should be Hecke stable
HB_lo := [HeckeOperator(f, pp) : f in B_lo];
assert #LinearDependence(B_lo cat HB_lo) eq #B_lo;

// B_hi should be Hecke stable
HB_hi := [HeckeOperator(f, pp) : f in B_hi];
assert #LinearDependence(B_hi cat HB_hi) eq #B_hi;

// dependence of B_hi with eis^2 * B_lo should be 
// the dimension of B_lo
x := #LinearDependence(B_hi cat [f * eis^2 : f in B_lo]);
assert x eq #B_lo;

// If we divide B_hi by eis^2, we should get
// a space of meromorphic quotients which contains B_lo, and 
// the Hecke stable subspace should actually be B_lo
V := [f/eis^2 : f in B_hi];
W := HeckeStableSubspace(V, pp);
assert #LinearDependence(W cat B_lo) eq #B_lo;

