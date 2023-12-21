intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,M::ModFrmHilDGRng,bb::RngQuadIdl) -> ModFrmElt
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
  prec := 0;
  for j in [0 .. Precision(fbb)] do 
    tracej := PositiveElementsOfTrace(bb*D^(-1),j);
    coefficient := 0;
    for nu in tracej do
      nuRed := FunDomainRep(M, nu: CheckComponent := bb);
      has_nuRed, coeffNu := IsDefined(Coefficients(fbb), nuRed);
      if not has_nuRed then
        break j;
      end if;
      coefficient +:= coeffNu;
      denom := Lcm(denom, Denominator(coeffNu));
    end for;
    restriction +:= coefficient*q^(j div b);
    prec +:= 1;
  end for;
  modForms := ModularForms(Gamma0(N),n*k);
  return modForms!(denom*(restriction +O(q^(prec))));
end intrinsic;

/*
// Totally Positive Elements in an Ideal
   From a basis {a,b} for the ideal bb where
     Tr(a) = n and Tr(b) = 0.
   Elements in ideal will look like xa + yb where x,y in ZZ
   and have embedding xa_1 + yb_1 and xa_2 + yb_2.
   All totally positive elements of given trace t will satisfy
   1)    t = Tr(xa+yb)    <=>   t = xn
   2)    xa+yb totally positive       <=>   y > -x*a_1/b_1   and  y > -x*a_2/b_2
   Eq 1) determines the value for x,
     and Eq 2) allows us to loop over values of y
*/
intrinsic PositiveElementsOfTrace(aa::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given aa a fractional ideal and t a nonnegative integer,
   returns the totally positive elements of aa with trace t.}
  basis := TraceBasis(aa);
  places := InfinitePlaces(NumberField(Parent(basis[1])));
  smallestTrace := Integers()!Trace(basis[1]);
  T := [];
  if t mod smallestTrace eq 0 then
    x := t div smallestTrace;
    a_1 := Evaluate(basis[1],places[1]);
    a_2 := Evaluate(basis[1],places[2]);
    b_1 := Evaluate(basis[2],places[1]);
    b_2 := Evaluate(basis[2],places[2]);
    assert b_1 lt 0 and b_2 gt 0; // if this assumption changes, the inequalities get swapped
    // at place 2, x*a2 + y*b2 >= 0 => y >= -x*a2/b2
    lower_bnd := Ceiling(-x*a_2/b_2);
    // at place 1, x*a1 + y*b1 >= 0 => y <= -x*a1/b1
    upper_bnd := Floor(-x*a_1/b_1);
    for y in [lower_bnd .. upper_bnd] do
      Append(~T, x*basis[1]+y*basis[2]);
    end for;
  end if;
  return T;
end intrinsic;


