// A fresh orbit sample can have smaller dimension even as the Hecke algebra grows.
SetSeed(20, 1100);

K := QuadraticField(6);
OK := MaximalOrder(K);
P := Factorization(2*OK)[1,1];
Q := Factorization(3*OK)[1,1];
M := HilbertCuspForms(K, P^8*Q);
MN := NewSubspace(M);

eigenspaces := NewformDecomposition(MN);
assert Dimension(MN) eq 48;
assert &+[Dimension(S) : S in eigenspaces] eq 48;
