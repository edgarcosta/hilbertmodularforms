printf "Testing creation of cusps...\n";
GammaTypes := ["Gamma", "Gamma1", "Gamma0"];

//print "QQ(sqrt(40))";
K := QuadraticField(40);
ZK := Integers(K);
NN := 1*ZK;
for type in GammaTypes do
  assert CuspSanityCheck(NN : GammaType := type);
end for;

// Check cusps on the non-trivial component.
cg, mp := NarrowClassGroup(K);
B := mp(cg.1); // The component with nontrivial signs.
cusps := Cusps(1*MaximalOrder(K), B);
assert #cusps eq 2;

//print "QQ(sqrt(5))";
K<sqrt5> := QuadraticField(5);
PP := PrimeIdealsOverPrime(K, 31)[1];
QQ := PrimeIdealsOverPrime(K, 5)[1];
NN := PP*QQ;
CuspSanityCheck(n : GammaType := "Gamma0");
for type in GammaTypes do
  assert CuspSanityCheck(NN : GammaType := type);
end for;