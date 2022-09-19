K  := QuadraticField(5);
OK := Integers(K);
P  := Factorization(31*OK)[1][1];

// Construct the HMF Mothership.
prec := 5;
R := GradedRingOfHMFs(K, prec);

W := HMFSpace(R, P, [2,2]);
f := Basis(W)[1];
g := Product([* f^0, f, f^0 *]);
assert CoefficientRing(f^0) ne CoefficientRing(f);
assert g eq f;

