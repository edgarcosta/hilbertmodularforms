intrinsic EliminateRedundantGenerators(I::RngMPol) -> RngMPol
  {Given an ideal I, try to eliminate redundant generators. Return the list of these non-redundant generators.}
  R := Generic(I);
  gens := Generators(I);
  //gens_red := gens;
  done := false;
  while not done do
    //print "top of while loop";
    new := false;
    for i := 1 to #gens do
      gens_i := gens[1..i-1] cat gens[i+1..#gens];
      I_i := ideal< R | gens_i >;
      if gens[i] in I_i then
        //printf "redudant gen found! i=%o, f=%o\n", i, gens[i];
        gens := gens_i;
        new := true;
        break i;
      end if;
    end for;
    if not new then
      done := true;
    end if;
  end while;
  assert ideal< R | gens > eq I;
  return gens;
end intrinsic;

intrinsic EliminateRedundantGenerators(L::SeqEnum[RngMPolElt]) -> RngMPol
  {Given a sequence of polynomials, return a non-redundant subsequence generating the same ideal.}
  if #L eq 0 then
    return L;
  end if;
  I := ideal< Parent(L[1]) | L >;
  return EliminateRedundantGenerators(I);
end intrinsic;

intrinsic IsIsomorphic(S1::Sch, S2::Sch) -> BoolElt
{Return true if S1 is isomorphic to S2. False is inconclusive!}
  eqns_S1 := EliminateRedundantGenerators(DefiningEquations(S1));
  eqns_S2 := EliminateRedundantGenerators(DefiningEquations(S2));
  eqns_S1 := Sort(eqns_S1);
  eqns_S2 := Sort(eqns_S2);
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

intrinsic VerifyGradedIsomorphism(I::RngMPol, J::RngMPol,
    PhiImages::SeqEnum, PsiImages::SeqEnum) -> BoolElt
{ Deterministically certify that the graded-algebra map phi from Generic(I)/I to
  Generic(J)/J, sending the i-th source variable to PhiImages[i], is an isomorphism
  with inverse psi given by PsiImages. Returns true iff all of:
  (1) phi(g) in J for every generator g of I;
  (2) psi(h) in I for every generator h of J;
  (3) psi(phi(x_i)) - x_i in I for every source variable x_i;
  (4) phi(psi(y_j)) - y_j in J for every target variable y_j;
  (5) phi and psi are weighted-homogeneous of the variable weights.
  Checks (1),(2) make phi,psi descend to the quotients; (3),(4) make them mutual
  inverses (containments alone do NOT prove an isomorphism); (5) makes the induced
  map of weighted-projective schemes well defined. The Hilbert-series equality of I
  and J is a separate sanity check, not performed here. No SolveZeroDimIdeal search
  is used, so the verdict is stable across Magma versions. Requires I and J to be
  homogeneous (graded) ideals (returns false otherwise) and Generic(I), Generic(J) to
  share the same weight vector (the caller normalizes proportional weights to the
  canonical ones; see spec Section 5.1). A variable whose image is the zero polynomial
  is rejected by check (5). }
  Rsrc := Generic(I);
  Rtgt := Generic(J);
  require #PhiImages eq Rank(Rsrc):
    "PhiImages must have one entry per variable of Generic(I)";
  require #PsiImages eq Rank(Rtgt):
    "PsiImages must have one entry per variable of Generic(J)";

  // A graded isomorphism of the quotients is only meaningful when I and J are homogeneous
  // (graded) ideals. The five checks below would otherwise certify a non-graded quotient
  // (e.g. I = <x + 1>). Reject non-homogeneous input up front.
  if not IsHomogeneous(I) or not IsHomogeneous(J) then
    return false;
  end if;

  phi := hom< Rsrc -> Rtgt | [Rtgt | f : f in PhiImages] >;
  psi := hom< Rtgt -> Rsrc | [Rsrc | f : f in PsiImages] >;

  // (5) grading: each variable image is homogeneous of the source/target variable weight
  for i in [1..Rank(Rsrc)] do
    im := Rtgt ! PhiImages[i];
    if im eq 0 or not IsHomogeneous(im) or WeightedDegree(im) ne WeightedDegree(Rsrc.i) then
      return false;
    end if;
  end for;
  for j in [1..Rank(Rtgt)] do
    im := Rsrc ! PsiImages[j];
    if im eq 0 or not IsHomogeneous(im) or WeightedDegree(im) ne WeightedDegree(Rtgt.j) then
      return false;
    end if;
  end for;

  // (1) phi(I) subset J
  for g in Generators(I) do
    if not (phi(g) in J) then return false; end if;
  end for;
  // (2) psi(J) subset I
  for h in Generators(J) do
    if not (psi(h) in I) then return false; end if;
  end for;
  // (3) psi . phi = identity on Generic(I)/I
  for i in [1..Rank(Rsrc)] do
    if not (psi(phi(Rsrc.i)) - Rsrc.i in I) then return false; end if;
  end for;
  // (4) phi . psi = identity on Generic(J)/J
  for j in [1..Rank(Rtgt)] do
    if not (phi(psi(Rtgt.j)) - Rtgt.j in J) then return false; end if;
  end for;

  return true;
end intrinsic;

intrinsic GradedInverseImages(R::RngMPol, PhiImages::SeqEnum) -> SeqEnum
{ Given a graded endomorphism phi of the weighted polynomial ring R with
  phi(R.i) = PhiImages[i], return [psi(R.1), ..., psi(R.n)] for the inverse
  endomorphism psi, solved weight by weight. This lets a stored witness map be
  recorded once (as the forward images phi) and its inverse recovered for the
  deterministic check in VerifyGradedIsomorphism. Requires phi to be linear-
  invertible in each generator weight (the weight-w monomials must map to a basis);
  raises a clear error naming the offending weight otherwise. }
  require #PhiImages eq Rank(R): "PhiImages must have one entry per variable of R";
  n := Rank(R);
  Psi := [R | 0 : i in [1..n]];
  for i in [1..n] do
    w := WeightedDegree(R.i);
    mons := MonomialsOfWeightedDegree(R, w);
    rows := [[MonomialCoefficient(Evaluate(m, PhiImages), b) : b in mons] : m in mons];
    M := Matrix(BaseRing(R), rows);
    require IsInvertible(M): Sprintf("GradedInverseImages: phi is not invertible on the weight-%o graded piece; this intrinsic requires phi to be an ambient graded automorphism (the weight-w monomials must map to a basis)", w);
    rhs := Vector(BaseRing(R), [ (mons[k] eq R.i) select 1 else 0 : k in [1..#mons] ]);
    cc := Solution(M, rhs);
    Psi[i] := &+[ cc[k]*mons[k] : k in [1..#mons] ];
  end for;
  return Psi;
end intrinsic;

intrinsic LoadStoredCanonicalRing(label::MonStgElt) -> RngMPol
{ Load the stored canonical-ring ideal for the LMFDB variety <label>
  (e.g. "2.2.13.1-1.1") from Verification/CanonicalRingEquations/<label>-gl-0.m,
  as an ideal in the file's weighted polynomial ring. Single-component files only;
  errors on multi-component (h+ = 2) files, which have one scheme per narrow-class
  component and need a component-wise loader. }
  filename := Sprintf("Verification/CanonicalRingEquations/%o-gl-0.m", label);
  s := Read(filename);
  ncomp := #[ m : m in Split(s, "\n") | Position(m, "component with label") gt 0 ];
  require ncomp le 1:
    Sprintf("%o has %o components; LoadStoredCanonicalRing handles single-component files only", filename, ncomp);
  R, A, eqns, S := eval (s cat "\nreturn R, A, eqns, S;");
  return ideal< R | eqns >;
end intrinsic;
