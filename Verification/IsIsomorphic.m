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
{Best-effort test for a graded isomorphism of the weighted-projective schemes S1, S2.
 A true result is a proof (a witness map is found and confirmed by
 VerifyGradedIsomorphism); false is INCONCLUSIVE. Extracts the two defining ideals,
 rebuilds S2's ideal inside the coordinate ring of S1 (proportional gradings, e.g.
 [1,2,3,3,4] and [2,4,6,6,8], are matched by rescaling) so the variable weights and
 parents agree, and delegates to SearchGradedIsomorphism.}
  R1 := CoordinateRing(Ambient(S1));
  R2 := CoordinateRing(Ambient(S2));
  g1 := Grading(R1);
  g2 := Grading(R2);
  // best-effort: different ambient dimensions are inconclusive, not an error
  if Rank(R1) ne Rank(R2) then
    return false;
  end if;
  // gradings need only be PROPORTIONAL (weighted-projective schemes are unchanged by a
  // uniform rescaling of the weights); reject if not, mapping variable i -> variable i.
  n := Rank(R1);
  prop := [ Rationals() | g1[i]/g2[i] : i in [1..n] ];
  if #{ r : r in prop } ne 1 then
    return false;
  end if;
  I := ideal< R1 | DefiningEquations(S1) >;
  toR1 := hom< R2 -> R1 | [R1.i : i in [1..n]] >;
  J := ideal< R1 | [toR1(f) : f in DefiningEquations(S2)] >;
  found := SearchGradedIsomorphism(I, J);
  return found;
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

intrinsic SearchGradedIsomorphism(I::RngMPol, J::RngMPol : Candidates := [], MaxAttempts := 100000)
  -> BoolElt, SeqEnum, SeqEnum
{ Search for a graded-algebra isomorphism phi from Generic(I)/I to Generic(J)/J, where
  Generic(I) and Generic(J) are the SAME weighted polynomial ring (identical variable
  weights). On success return true, PhiImages, PsiImages, with PhiImages the images
  phi(x_1),...,phi(x_n) of the source variables and PsiImages the images of the target
  variables under the inverse psi; the map is confirmed by VerifyGradedIsomorphism
  before returning, so the verdict is stable across Magma versions. Returns
  false, empty, empty if no map is found within the search.

  This is the OFFLINE tool that PRODUCES witness maps (CI then re-checks stored maps
  with VerifyGradedIsomorphism). Method: write phi(x_i) with undetermined rational
  coefficients over the weight-w_i monomials; impose that phi(g) lie in J for each
  generator g of I by LINEAR ALGEBRA over Q (the functionals vanishing on J in that
  degree applied to the coefficient vector of phi(g)), not NormalForm (which needs a
  field base ring). Fixing the whole automorphism group of the target at once is
  intractable (the solution set is positive-dimensional). Instead we pin the diagonal
  scalings of every single-generator variable weight EXCEPT the top-weight one (whose
  scaling is then determined), which reduces the membership system to a
  0-dimensional one solved by Variety in a fraction of a second; the remaining lower
  diagonal scalings are searched over a small rational candidate set (signed powers of
  two by default) ordered by height. Equal-weight generators (e.g. two weight-6 forms)
  are left as a free linear block that Variety solves, so a map that permutes them (as
  for the field of discriminant 13) is found automatically. Optional parameters:
  Candidates (rational values to try for each searched diagonal) and MaxAttempts (a cap
  on the number of Variety solves). Requires I and J homogeneous with the same weights. }
  R := Generic(I);
  require Generic(J) cmpeq R:
    "SearchGradedIsomorphism requires Generic(I) and Generic(J) to be the same ring";
  if not IsHomogeneous(I) or not IsHomogeneous(J) then
    return false, [R|], [R|];
  end if;
  Q := Rationals();
  require BaseRing(R) cmpeq Q:
    "SearchGradedIsomorphism requires the ambient ring to be defined over the rationals";
  n := Rank(R);
  wts := [Integers()! WeightedDegree(R.i) : i in [1..n]];

  // undetermined phi(x_i) = sum_k a[.]*mon over weight-w_i monomials of R
  monsByVar := [MonomialsOfWeightedDegree(R, wts[i]) : i in [1..n]];
  counts := [#m : m in monsByVar];
  N := &+counts;
  A := PolynomialRing(Q, N);
  aa := [A.i : i in [1..N]];
  RA := ChangeRing(R, A);
  PhiG := [RA | 0 : i in [1..n]];
  offset := [];
  off := 0;
  for i in [1..n] do
    Append(~offset, off);
    PhiG[i] := &+[ aa[off+k]*(RA!monsByVar[i][k]) : k in [1..counts[i]] ];
    off +:= counts[i];
  end for;

  // group variables by weight; single-generator weights get a "diagonal" unknown
  // (coefficient of x_i in phi(x_i)); equal-weight weights are left free
  wset := Sort(SetToSequence({w : w in wts}));
  varsOfWt := AssociativeArray();
  for w in wset do varsOfWt[w] := [i : i in [1..n] | wts[i] eq w]; end for;
  singleDiag := [];   // A-variable indices of single-generator diagonals
  for w in wset do
    if #varsOfWt[w] eq 1 then
      i := varsOfWt[w][1];
      Append(~singleDiag, offset[i] + Index(monsByVar[i], R.i));
    end if;
  end for;

  // membership system: for each generator g of I, apply the functionals vanishing on
  // J in degree deg(g) to the coefficient vector of phi(g)
  Jgens := [R! gj : gj in Generators(J)];
  Jdeg := [Integers()! WeightedDegree(gj) : gj in Jgens];
  sys := [];
  for g in Generators(I) do
    dg := Integers()! WeightedDegree(R!g);
    Md := MonomialsOfWeightedDegree(R, dg);
    pos := AssociativeArray();
    for t in [1..#Md] do pos[Md[t]] := t; end for;
    rows := [];
    for jj in [1..#Jgens] do
      if Jdeg[jj] le dg then
        for mm in MonomialsOfWeightedDegree(R, dg - Jdeg[jj]) do
          vec := [Q | 0 : t in [1..#Md]];
          cs, ms := CoefficientsAndMonomials(mm*Jgens[jj]);
          for t in [1..#ms] do vec[pos[ms[t]]] := cs[t]; end for;
          Append(~rows, vec);
        end for;
      end if;
    end for;
    if #rows eq 0 then
      Kern := [ [ (t eq s select Q!1 else Q!0) : t in [1..#Md] ] : s in [1..#Md] ];
    else
      Kern := [ Eltseq(y) : y in Basis(Kernel(Transpose(Matrix(Q, rows)))) ];
    end if;
    pg := Evaluate(RA!(R!g), PhiG);
    cvec := [ MonomialCoefficient(pg, RA!Md[t]) : t in [1..#Md] ];
    for y in Kern do Append(~sys, &+[ (A!y[t])*cvec[t] : t in [1..#Md] ]); end for;
  end for;

  BuildPhi := function(pt)
    Phi := [R | 0 : i in [1..n]];
    o := 0;
    for i in [1..n] do
      Phi[i] := &+[ (R!pt[o+k])*monsByVar[i][k] : k in [1..counts[i]] ];
      o +:= counts[i];
    end for;
    return Phi;
  end function;

  TestPoint := function(pt)
    Phi := BuildPhi([Q!c : c in pt]);
    Psi := [R|];
    try
      Psi := GradedInverseImages(R, Phi);
    catch e
      return false, [R|], [R|];
    end try;
    if VerifyGradedIsomorphism(I, J, Phi, Psi) then
      return true, Phi, Psi;
    end if;
    return false, [R|], [R|];
  end function;

  SolvePinned := function(pins)
    // pins: sequence of <A-index, value>; returns list of Variety points (may be empty).
    // On a non-isomorphic or poorly-structured target this pinned membership system can be
    // positive-dimensional, and Variety would throw "not zero-dimensional". Such a pinning
    // yields no usable candidate map, so treat it as contributing no solutions and let the
    // search move on; soundness is unaffected because every point that IS returned is still
    // re-checked by VerifyGradedIsomorphism.
    Id := ideal< A | sys cat [ aa[p[1]] - p[2] : p in pins ] >;
    if not IsZeroDimensional(Id) then
      return [];
    end if;
    return Variety(Id);
  end function;

  // Choose which coefficients to pin/search so the membership system becomes
  // 0-dimensional (Variety-fast). The target's automorphisms make the raw system
  // positive-dimensional; pinning the single-generator diagonals removes almost all of
  // it. With >= 2 single-generator weights we pin all but the top one (whose scaling is
  // then determined by the relations) and search the rest; the searched values also fix
  // the overall projective scale. With exactly one single-generator weight we search
  // that one (to fix the scale). With none (all variables share weights, e.g. a plane
  // cubic), we search the self-coefficient of the first variable to fix the scale; the
  // remaining equal-weight block is a finite (0-dimensional) set that Variety resolves.
  nsingle := #singleDiag;
  if nsingle ge 2 then
    searchIdx := singleDiag[1..nsingle-1];
  elif nsingle eq 1 then
    searchIdx := singleDiag;
  else
    searchIdx := [ offset[1] + Index(monsByVar[1], R.1) ];
  end if;
  ksearch := #searchIdx;

  // candidate diagonal values (signed powers of two by default), and a height order
  cand := #Candidates gt 0 select [Q!c : c in Candidates]
          else [Q | 1,-1,2,-2,4,-4,8,-8,16,-16,
                    1/2,-1/2,1/4,-1/4,1/8,-1/8];
  height := function(c)
    a := Abs(Numerator(c)); b := Denominator(c);
    return (a le 1 select 0 else Ilog(2, a)) + (b le 1 select 0 else Ilog(2, b));
  end function;

  attempts := 0;

  // enumerate candidate tuples for the searched diagonals, ordered by total height
  space := CartesianPower([1..#cand], ksearch);
  tlist := [ [t[s] : s in [1..ksearch]] : t in space ];
  Sort(~tlist, func< u, v | (&+[height(cand[u[s]]) : s in [1..ksearch]])
                          - (&+[height(cand[v[s]]) : s in [1..ksearch]]) >);
  for tp in tlist do
    if attempts ge MaxAttempts then break; end if;
    attempts +:= 1;
    pins := [ <searchIdx[s], cand[tp[s]]> : s in [1..ksearch] ];
    V := SolvePinned(pins);
    for pt in V do
      ok, Phi, Psi := TestPoint(pt);
      if ok then return true, Phi, Psi; end if;
    end for;
  end for;
  return false, [R|], [R|];
end intrinsic;
