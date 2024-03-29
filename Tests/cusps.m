printf "Testing creation of cusps... D=";
//GammaTypes := ["Gamma", "Gamma1", "Gamma0"];
GammaTypes := ["Gamma1", "Gamma0"]; // Gamma currently broken
//GammaTypes := ["Gamma1"];

printf "5 ";
F<nu> := QuadraticField(5);
PP := PrimeIdealsOverPrime(F, 31)[1];
QQ := PrimeIdealsOverPrime(F, 5)[1];
NNs := [PP, PP^2, PP*QQ, QQ^2];
for type in GammaTypes do
  for NN in NNs do
    assert CuspSanityCheck(NN : GammaType := type);
  end for;
end for;

printf "12 ";
F<nu> := QuadraticField(12);
ZF := Integers(F);
P11 := PrimeIdealsOverPrime(F,11)[1];
NNs := [7*ZF, P11, 11*ZF, P11^2];
for type in GammaTypes do
  for NN in NNs do
    assert CuspSanityCheck(NN : GammaType := type);
  end for;
end for;

printf "40 ";
F<nu> := QuadraticField(40);
ZF := Integers(F);
NNs := [1*ZF, 2*ZF, 3*ZF];
for type in GammaTypes do
  for NN in NNs do
    assert CuspSanityCheck(NN : GammaType := type);
  end for;
end for;

// Check cusps on the non-trivial component.
cg, mp := NarrowClassGroup(F);
B := mp(cg.1); // The component with nontrivial signs.
cusps := Cusps(1*ZF, B);
assert #cusps eq 2;

printf "69 ";
F<nu> := QuadraticField(69);
ZF := Integers(F);
P13 := PrimeIdealsOverPrime(F,13)[1];
NNs := [1*ZF, 22*ZF, P13, P13^2];
for type in GammaTypes do
  for NN in NNs do
    assert CuspSanityCheck(NN : GammaType := type);
  end for;
end for;
