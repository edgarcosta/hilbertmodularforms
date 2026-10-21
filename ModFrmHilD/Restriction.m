intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,M::ModFrmHilDGRng,bb::RngOrdIdl : AsCoefficients:=false) -> Any
  {The diagonal restriction of component bb of f in M, of weight &+Weight(f)
  and level the positive generator of (Level(f)*bb) meet Z.
  The parameter AsCoefficients (default false) gives the coefficient sequence without requiring rational coefficients.
  See also qExpansion}
  F := M`BaseField;
  ZF := Integers(F);
  NN := Level(f);
  // On component bb, the lower-left matrix entry lies in NN*bb.
  N := Integers()!Generator((NN*bb) meet Integers());
  D := Different(ZF);
  classical_weight := &+Weight(f);
  fbb := f`Components[bb];

  if not AsCoefficients then
    C := BaseField(F);
    R<q> := PowerSeriesRing(C);
    restriction := R!0;
    denom := 1;
  else
    coeffs := [];
  end if;

  prec := 0;
  for j in [0 .. Precision(fbb)] do
    tracej := PositiveElementsOfTrace(bb * D^(-1), j);
    norms := [Norm(nu) : nu in tracej];
    coefficient := j eq 0 select Coefficient(fbb, F!0) else 0;
    if #norms gt 0 then
      if (Max(norms) * Norm(D)) gt Precision(fbb) then
        break j;
      end if;
      coefficient := &+[Coefficient(fbb, F!nu) : nu in tracej];
    end if;

    if AsCoefficients then
      Append(~coeffs, coefficient);
    else
      denom := LCM(denom, Denominator(coefficient));
      restriction +:= coefficient*q^j;
    end if;
    prec +:= 1;
  end for;

  if AsCoefficients then
    return coeffs;
  end if;

  modForms := ModularForms(Gamma0(N),classical_weight);
  if denom ne 1 then
    modForms := BaseExtend(modForms, Rationals());
  end if;
  return modForms!(restriction + O(q^(prec)));
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
