
// Indefinite, over Q : verify vs classical modular forms

SetVerbose("ModFrmHil",2);
SetVerbose("Shimura", 1);

for N in [6, 15, 33, 34, 35] do

 "\n********************* N =", N, "******************";
 "Seed:", GetSeed();

  QO := MaximalOrder(QuaternionAlgebra(N));
  M := NewSubspace(HilbertCuspForms(Rationals(), N) : QuaternionOrder:=QO); M;
  S := NewSubspace(CuspForms(N));
  assert Dimension(S) eq Dimension(M);
  "Dimension =", Dimension(M); "";
  ps := [p : p in PrimesUpTo(30) | GCD(p,N) eq 1];
  time Tps := [HeckeOperator(M,p) : p in ps];
  time Tps1 := [HeckeOperator(S,p) : p in ps];  Tps[1]; ""; Tps1[1];
  assert [CharacteristicPolynomial(T) : T in Tps]
      eq [CharacteristicPolynomial(T) : T in Tps1];

end for;

