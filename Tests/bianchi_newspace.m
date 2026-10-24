// Over Q(i), 65 is the smallest level norm with a nonzero Bianchi newspace.
K := QuadraticField(-1);
OK := Integers(K);
NM := NewSubspace(BianchiCuspForms(K, ideal<OK | 65, K.1 - 18>));
assert Dimension(NM) eq 1;
assert DirichletCharacter(NM) cmpeq 1;
