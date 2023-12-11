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
  diffs := [Evaluate(eqns_S1[i],F)-Pa!eqns_S2[i] : i in [1..#eqns_S1]];
  coeffs := &cat[Coefficients(d) : d in diffs];
  I := ideal< Pvars | coeffs>;
  G := GroebnerBasis(I);
  solns := SolveZeroDimIdeal(I);
  if (#solns gt 0) then
      return true;
  end if;
  return false;
end intrinsic;
