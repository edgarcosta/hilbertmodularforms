K  := QuadraticField(5);
OK := Integers(K);
P  := Factorization(31*OK)[1][1];

// Construct the HMF Mothership.
prec := 50;
R := GradedRingOfHMFs(K, prec);

W := HMFSpace(R, P, [2,2]);
f := Basis(W)[1];
g := Product([* f^0, f, f^0 *]);

assert IsIsomorphic(CoefficientRing(f^0), Rationals());
assert IsIsomorphic(CoefficientRing(f), Rationals());
assert g eq f;

