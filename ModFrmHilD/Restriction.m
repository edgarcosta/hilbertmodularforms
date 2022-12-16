intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,Mk::ModFrmHilD:Precision:=15) -> ModFrmElt
  {Given an HMF f of parallel weight k, returns the classical modular curve of weight nk and level NNcapQQ obtained from restricting
  the HMF to the diagonal.}
  require #SequenceToSet(Weight(Mk)) eq 1: "Only defined for parallel weight.";
  M := Parent(Mk);
  F := BaseField(M);
  ZF := Integers(F);
  C := BaseField(F);
  R<q> := PowerSeriesRing(C);
  restriction := R!0;
  ideals := M`NarrowClassGroupReps;
  NN := Mk`Level;
  N := Integers()!(Denominator(NN)^(-1)*Generator((Denominator(NN)*NN) meet Integers()));
  D := Different(ZF);
  k :=  Mk`Weight[1];
  n := #Mk`Weight;
  // modForms only accepts integer coefficients
  denom := 1;
  for bb in ideals do
    b := Integers()!(Denominator(bb)^(-1)*Generator((Denominator(bb)*bb) meet Integers()));
    for j in [0..Precision] do
      trace_j := PositiveElementsOfTrace(D^(-1)*bb,j);
      coefficient := 0;
      for i in [1..#trace_j] do
        nu := ReduceShintani(M,bb,trace_j[i]);
        coefficient +:= Coefficients(f)[bb][nu];
        denom := Lcm(denom, Denominator(Coefficients(f)[bb][nu]));
      end for;
      restriction +:= coefficient*q^(j div b);
    end for;
  end for;
  modForms := ModularForms(Gamma0(N),n*k);
  return modForms!(denom*(restriction +O(q^(Precision))));
  // return (restriction +O(q^(Precision+1)));
end intrinsic;
