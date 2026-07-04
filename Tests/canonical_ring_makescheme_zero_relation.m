// Regression: MakeScheme's relation-ordering self-check must not crash on a
// zero relation polynomial. A zero relation yields empty coeffs/mons, so the
// check `assert &+[...] eq 0` reduced an empty sequence (`&+[]`), which is
// illegal in Magma. Such a relation is trivially satisfied and must be skipped.
//
// For a zero relation the monomial list is empty, so EvaluateMonomials never
// touches the generators; placeholder generators suffice to drive the public
// MakeScheme path that hits the bug.

Gens := AssociativeArray();
Gens[1] := [1, 2];   // two weight-1 generators; only the count/shape is used here

R := ConstructWeightedPolynomialRing(Gens);              // Q[x1, x2], both weight 1
nmons2 := #MonomialsOfWeightedDegree(R, 2);              // weight-2 monomials: x1^2, x1*x2, x2^2

Relations := AssociativeArray();
Relations[2] := [[Rationals() | 0 : j in [1..nmons2]]];  // a single all-zero (zero) relation

// On the buggy code this errors at `&+[]`; with the fix it returns the scheme.
S := MakeScheme(Gens, Relations);
assert ISA(Type(S), Sch);
