intrinsic IsIsomorphic(S1::Sch, S2::Sch) -> BoolElt
{Return true if S1 is isomorphic to S2. False is inconclusive!}
  eqns_S1 := Sort(DefiningEquations(S1));
  eqns_S2 := Sort(DefiningEquations(S2));
  P := CoordinateRing(Ambient(S1));
  wts := Grading(P);
  mons := [MonomialsOfWeightedDegree(P, d) : d in wts];
  num_mons := [&+[Integers() | #m : m in mons[1..i]] : i in [0..#mons]];
  num_vars := num_mons[#num_mons];
  QQ := Rationals();
  Pvars<[a]> := PolynomialRing(QQ,num_vars);
  Pa<[X]> := ChangeRing(P, Pvars);
  a_grps := [a[num_mons[i]+1..num_mons[i+1]] : i in [1..#mons]];
  big_mons := [MonomialsOfWeightedDegree(Pa, d) : d in wts];
  F := [&+[a_grps[j][i]*big_mons[j][i] : i in [1..#mons[j]]] : j in [1..#mons]];
  eqns_S1_aut := [Evaluate(eqns_S1[i],F) : i in [1..#eqns_S1]];
  eqns_S2_vars := [Pa!eqns_S2[i] : i in [1..#eqns_S2]];
  assert #eqns_S1_aut eq #eqns_S2_vars;
  diffs := [eqns_S1_aut[i] - eqns_S2_vars[i] : i in [1..#eqns_S1_aut]];
  coeffs := &cat [Coefficients(d) : d in diffs];
  I := ideal< Pvars | coeffs>;
  G := GroebnerBasis(I);
  solns := SolveZeroDimIdeal(I);
  if (#solns gt 0) then
      return true;
  end if;
  Pvars<[a]> := FunctionField(QQ,num_vars);
  Pa<[X]> := ChangeRing(P, Pvars);
  a_grps := [a[num_mons[i]+1..num_mons[i+1]] : i in [1..#mons]];
  big_mons := [MonomialsOfWeightedDegree(Pa, d) : d in wts];
  F := [&+[a_grps[j][i]*big_mons[j][i] : i in [1..#mons[j]]] : j in [1..#mons]];
  eqns_S1_aut := [Evaluate(eqns_S1[i],F) : i in [1..#eqns_S1]];
  eqns_S2_vars := [Pa!eqns_S2[i] : i in [1..#eqns_S2]];
  assert #eqns_S1_aut eq #eqns_S2_vars;
  G := GroebnerBasis(eqns_S2_vars);
  reduced := [NormalForm(poly,G) : poly in eqns_S1_aut];
  coeffs := [];
  for f in reduced do
      coeffs cat:= Coefficients(f);
  end for;
  coeffs cat:= [a[3] + 1];
  coeffs := [Numerator(el) : el in coeffs];
  G_vars := GroebnerBasis(coeffs);
  Pvars_poly := Integers(Pvars);
  I := ideal< Pvars_poly | G_vars >;
  solns := SolveZeroDimIdeal(I);
  if (#solns gt 0) then
      return true;
  end if;
  return false;
end intrinsic;
