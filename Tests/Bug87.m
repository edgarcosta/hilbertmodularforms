_<x> := PolynomialRing(Rationals());
F<w> := NumberField(x^2 - x - 1);
OF := Integers(F);
NN := ideal<OF | [61, 61, 3*w - 10]>;
f := Eigenform(NewformDecomposition(NewSubspace(HilbertCuspForms(F,NN)))[1]);
InnerProduct(f, f);
// added the following to test wanted behavior.
D := NewformDecomposition(NewSubspace(HilbertCuspForms(F,2*NN)));
f := Eigenform(D[1]);
g := Eigenform(D[2]);
assert InnerProduct(f,g) eq 0;
