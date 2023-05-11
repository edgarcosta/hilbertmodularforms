intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,M::ModFrmHilDGRng,bb::RngQuadIdl:prec:=10) -> ModFrmElt
  {Given an HMF f of parallel weight k, returns the classical modular curve of weight nk and level obtained from restricting
  the component bb of the HMF to the diagonal.}
  require #SequenceToSet(Weight(f)) eq 1: "Only defined for parallel weight.";
  F := M`BaseField;
  ZF := Integers(F);
  C := BaseField(F);
  R<q> := PowerSeriesRing(C);
  restriction := R!0;
  NN := Level(f);
  N := Integers()!(Denominator(NN)^(-1)*Generator((Denominator(NN)*NN) meet Integers()));
  D := Different(ZF);
  k :=  Weight(f)[1];
  n := #Weight(f);
  fbb := f`Components[bb];
  // modForms only accepts integer coefficients
  denom := 1;
  b := Integers()!(Denominator(bb)^(-1)*Generator((Denominator(bb)*bb) meet Integers()));
  assert prec*b le M`Precision; //Increase precision!
  for j in [0..(prec*b)] do
    tracej := PositiveElementsOfTrace(bb*D^(-1),j);
    coefficient := 0;
    for nu in tracej do
      nuRed := ReduceShintani(M,bb,nu);
      coeffNu := Coefficients(fbb)[nuRed];
      coefficient +:= coeffNu;
      denom := Lcm(denom, Denominator(coeffNu));
    end for;
    restriction +:= coefficient*q^(j div b);
  end for;
  modForms := ModularForms(Gamma0(N),n*k);
  return modForms!(denom*(restriction +O(q^(prec))));
end intrinsic;
