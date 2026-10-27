SetNthreads(1);
SetSeed(1);

F := QuadraticField(5);
ZF := Integers(F);
M := NewSubspace(HilbertCuspForms(F, 19*ZF));
D := NewformDecomposition(M : Dimensions := 2);
assert #D eq 1;
S := D[1];

// Cache these operators before seeding the Hecke-module search.
for p in PrimesUpTo(11, F) do
  _ := HeckeOperator(S, p);
end for;

// This seed draws a zero orbit generator after the scalar Hecke operators.
SetSeed(3929);
f := Eigenform(S);
assert IsEigenform(f);
assert Degree(BaseField(f)) eq 2;
