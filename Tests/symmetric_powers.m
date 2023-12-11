printf "Testing SymmetricPowers...k=";
// Algebraic data.
K  := QuadraticField(5);
OK := Integers(K);
P  := Factorization(31*OK)[1][1];

// Construct the HMF Mothership.
prec := 250;
R := GradedRingOfHMFs(K, prec);

// Look at the image of 2-forms in weight 6, and compute its complement.
W := HMFSpace(R, P, [2,2]);
new6 := ComplementBasis(SymmetricPower(W, 3) : Alg:="Orthogonal");

printf "2 ";
// Now try to find quadric relations.
sym2new6 := SymmetricPower(new6, 2);
assert #sym2new6 eq Binomial(#new6 + 1, 2); // SymmetricPower returns a basis.

printf "12 ";
// Alternatively,
assert #Generators(Syzygies(new6, 12)) eq 0;
