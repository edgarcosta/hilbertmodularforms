intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,M::ModFrmHilDGRng,bb::RngOrdIdl) -> ModFrmElt
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

intrinsic PositiveElementsOfTrace(aa::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {
    Given aa a fractional ideal and t a nonnegative integer,
    returns the totally positive elements of aa with trace t.
  }
  basis := TraceBasis(aa);
  smallest_trace := Integers()!Trace(basis[1]);
  if (t mod smallest_trace) eq 0 then
    F := NumberField(Parent(basis[1]));
    n := Degree(F);

    B := Matrix([[Evaluate(b, v) : v in InfinitePlaces(F)] : b in basis]);
    B := t * B^-1;

    // drop the first coordinate, it'll always be t / smallest_trace
    vertices := [Rationalize(Vector([v[i] : i in [2 .. n]])) : v in Rows(B)];
    assert #vertices[1] eq n-1 and #vertices eq n;
    P := Polytope(vertices);
    pts := InteriorPoints(P);
    // put t / smallest_trace back in each vector
    x := t div smallest_trace;
    return [x * basis[1] + &+[Eltseq(pt)[i] * basis[i+1] : i in [1 .. n-1]] : pt in pts];
  else
    return [];
  end if;
end intrinsic;
