printf "Testing creation of cusps...\n";
GammaTypes := ["Gamma", "Gamma1", "Gamma0"];

//print "QQ(sqrt(40))";
K := QuadraticField(40);
ZK := Integers(K);
NN := 1*ZK;
for type in GammaTypes do
  assert CuspSanityCheck(NN : GammaType := type);
end for;

//print "QQ(sqrt(5))";
K<sqrt5> := QuadraticField(5);
PP := PrimeIdealsOverPrime(K, 31)[1];
QQ := PrimeIdealsOverPrime(K, 5)[1];
for type in GammaTypes do
  assert CuspSanityCheck(PP^2 : GammaType := type);
  assert CuspSanityCheck(QQ^2 : GammaType := type);
  assert CuspSanityCheck(PP*QQ : GammaType := type);
end for;
