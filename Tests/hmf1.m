
// Test definite algorithm over quadratic field

SetVerbose("ModFrmHil", 2);

_<x> := PolynomialRing(Rationals());
F<w> := NumberField(x^2 - 3);
ZF := Integers(F);

SetStoreModularForms(F, true);

N := 8*w*ZF;
print "\n\nLevel", N;

M := HilbertCuspForms(F, N);
Mnew := NewSubspace(M);
assert Dimension(Mnew) eq 2;
nfd := NewformDecomposition(Mnew);
assert #nfd eq 2;
f := Eigenform(nfd[1]);
assert IsEigenform(f);

N := 16*w*ZF;
print "\n\nLevel", N;

M := HilbertCuspForms(F, N);
Mnew := NewSubspace(M);
assert Dimension(Mnew) eq 16;
nfd := NewformDecomposition(Mnew);
assert #nfd eq 16;

N := 8*3*ZF;
print "\n\nLevel", N;

M := HilbertCuspForms(F, N);
Mnew := NewSubspace(M);
nfd := NewformDecomposition(Mnew);

N := 16*3*ZF;
print "\n\nLevel", N;

M := HilbertCuspForms(F, N);
Mnew := NewSubspace(M);
nfd := NewformDecomposition(Mnew);

