// Test to compute relations among only some of the elements of the canonical ring via linear algebra.

K  := QuadraticField(5);
ZK := MaximalOrder(K);
P  := Factorization(31*ZK)[1][1];

// Construct the HMF Mothership.
prec := 10;
R := GradedRingOfHMFs(K, prec);

// Compute the space of 2-forms and pick a single 4-form.
W2 := HMFSpace(R, P, [2,2]);
W4 := HMFSpace(R, P, [4,4]);
f := Basis(W4)[1];
forms := [* g : g in Basis(W2) *] cat [* f *];

// Compute the image of the HMS under the rational map determined by forms.
// The user needs to tell it the degrees to look for Syzygies. We don't have a degree bound for the
// degree of the relations of a projection, not to mention precision issues, so we insist that the user
// chooses a degree bound explicitly.
X := HilbertModularImage(forms, 10);
assert Dimension(X) eq 2;
