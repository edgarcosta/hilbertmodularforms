function ClassicalNebentypusOfRestriction(chiF, N, ZF)
  // chiF - the Hilbert nebentypus (GrpHeckeElt) of the HMF being restricted
  // N    - the rational classical level (RngIntElt)
  // ZF   - the ring of integers of the base field
  //
  // Returns the classical Dirichlet character psi mod N (over Q) carried by
  // the diagonal restriction, or `false` if it cannot be matched. For a
  // positive rational integer n coprime to N the restricted form has
  // nebentypus value psi(n) = chiF(n*ZF): the diagonal embedding sends the
  // lower-right entry d of a Gamma_0(N) matrix to the principal ideal (d),
  // so the automorphy character is chiF evaluated there. Evaluating on
  // positive representatives of the unit generators automatically bakes in
  // the correct parity psi(-1) = (-1)^(classical weight), since chiF's
  // archimedean type is what makes it compatible with the weight.
  ord := Order(chiF);
  Cf := CyclotomicField(ord);
  G := DirichletGroup(N, Cf);
  ug := UnitGenerators(G);
  targets := [Cf ! chiF((Integers()!u)*ZF) : u in ug];
  for d in Elements(G) do
    if [Cf ! d(u) : u in ug] eq targets then
      return MinimalBaseRingCharacter(d);
    end if;
  end for;
  return false;
end function;

intrinsic RestrictionToDiagonal(f::ModFrmHilDElt,M::ModFrmHilDGRng,bb::RngOrdIdl : AsCoefficients:=false) -> Any
  {Given an HMF f of weight k = [k_1,...,k_n] (not necessarily parallel), returns the classical modular
  form of weight Sum(k) and level obtained from restricting the component bb of the HMF to the diagonal,
  as a ModFrmElt. This is because for gamma in Gamma0(N) (embedded diagonally, so having rational entries,
  hence agreeing with every infinite place of F), the automorphy factor is Prod_i (c z + d)^(k_i) =
  (c z + d)^(Sum k_i), regardless of whether the k_i agree. If AsCoefficients is true, instead
  returns the SeqEnum of q-expansion coefficients of the restriction, in whatever ring they naturally live,
  without coercing into a classical ModularForms space (which only supports rational coefficients) -- this
  also works when the restriction's coefficients are not rational.}
  F := M`BaseField;
  ZF := Integers(F);
  NN := Level(f);
  N := Integers()!(Denominator(NN)^(-1)*Generator((Denominator(NN)*NN) meet Integers()));
  D := Different(ZF);
  classical_weight := &+Weight(f);
  fbb := f`Components[bb];
  b := Integers()!(Denominator(bb)^(-1)*Generator((Denominator(bb)*bb) meet Integers()));

  if not AsCoefficients then
    C := BaseField(F);
    R<q> := PowerSeriesRing(C);
    restriction := R!0;
    // modForms only accepts integer coefficients
    denom := 1;
  else
    raw_coeffs := AssociativeArray();
  end if;

  prec := 0;
  for j in [0 .. Precision(fbb)] do
    tracej := PositiveElementsOfTrace(bb * D^(-1), j);
    norms := [Norm(nu) : nu in tracej];
    coefficient := 0;
    exp := j div b;
    if #norms gt 0 then
      if (Max(norms) * Norm(D)) gt Precision(fbb) then
        break j;
      end if;
      coefficient := &+[Coefficient(fbb, F!nu) : nu in tracej];
    end if;

    if AsCoefficients then
      raw_coeffs[exp] := IsDefined(raw_coeffs, exp) select raw_coeffs[exp] + coefficient else coefficient;
    else
      denom := LCM(denom, Denominator(coefficient));
      restriction +:= coefficient*q^exp;
    end if;
    prec +:= 1;
  end for;

  if AsCoefficients then
    if #Keys(raw_coeffs) eq 0 then
      return [];
    end if;
    max_exp := Max(Keys(raw_coeffs));
    return [IsDefined(raw_coeffs, e) select raw_coeffs[e] else 0 : e in [0 .. max_exp]];
  end if;

  // The restriction lands in M_k(Gamma_0(N), psi) where psi is the classical
  // nebentypus induced by the Hilbert nebentypus. When psi is trivial this is
  // the usual Gamma_0(N) space; otherwise we must build the space with that
  // character, or the coercion below fails ("series does not define a modular
  // form in the space"). This happens whenever classical_weight is odd (the
  // trivial-character space is {0} then) or the Hilbert nebentypus restricts
  // to a nontrivial Dirichlet character.
  chiF := Character(Parent(f));
  if IsTrivial(chiF) then
    modForms := ModularForms(Gamma0(N), classical_weight);
  else
    psi := ClassicalNebentypusOfRestriction(chiF, N, ZF);
    require psi cmpne false :
      "Could not determine the classical nebentypus of the restriction; use AsCoefficients:=true instead";
    modForms := IsTrivial(psi) select ModularForms(Gamma0(N), classical_weight)
                                 else ModularForms(psi, classical_weight);
  end if;
  return modForms!(denom*(restriction + O(q^(prec))));
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
