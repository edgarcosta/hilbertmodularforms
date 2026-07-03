/////////////////////////////////////////////////////
//                                                   //
//   Change of presentation for canonical rings      //
//                                                   //
/////////////////////////////////////////////////////
//
// When the canonical-ring code changes and returns a DIFFERENT but isomorphic
// set of generators for the SAME graded ring, we can recover the graded ring
// map old-ring -> new-ring cheaply from the generators' q-expansions instead of
// re-running an algebraic isomorphism search.
//
// For each weight w, every NEW generator of weight w is a Q-linear combination
// of the weight-w MONOMIALS in the OLD generators.  We solve that linear system
// on q-expansion coefficients (new generator's coefficient vector = combination
// of old-monomials' coefficient vectors).  Stacking these per weight yields the
// map on generators as a list `PhiImages` of polynomials in the old ring's
// variables, one per new generator.

/////////////////////  Helpers  //////////////////////

// Flatten an Assoc (weight -> SeqEnum[ModFrmHilDElt]) into a single list, using
// the SAME order that ConstructWeightedPolynomialRing / EvaluateMonomials use for
// the ring variables: sorted key (weight) order, not associative-array hash order.
// On feat those intrinsics iterate Sort(Setseq(Keys(.))) (commit f208eb0), so the
// flattened forms must line up with the ring variables the same way.
function FlattenGens(Gens)
  return Sum([* SequenceToList(Gens[w]) : w in Sort(Setseq(Keys(Gens))) *] : empty := [* *]);
end function;

// Evaluate a polynomial p (in the old ring) on the flattened List of old
// generator forms, returning a ModFrmHilDElt.  We do this via EvaluateMonomials
// rather than the generic Evaluate(RngMPolElt, List), which mis-evaluates pure
// monomials.  The forms may have different parents, so we combine via '+'/'*'.
function EvaluatePolynomialOnForms(p, genForms)
  coeffs, mons := CoefficientsAndMonomials(p);
  evaledMons := EvaluateMonomials(genForms, mons);
  return &+[coeffs[i] * evaledMons[i] : i in [1..#evaledMons]];
end function;

/////////////////  Main intrinsics  ///////////////////

intrinsic ChangeOfPresentation(
  OldGens::Assoc,
  NewGens::Assoc
  :
  IdealClassesSupport := false,
  Prec := false,
  Verify := true
  ) -> SeqEnum, RngMPol
{
  Recover the graded ring map (old ring) -> (new ring) on generators from the
  q-expansions of two generating sets of the SAME graded ring of Hilbert modular
  forms.  Both inputs are associative arrays weight -> SeqEnum[ModFrmHilDElt];
  they must have the SAME multiset of weights.

  For each weight w, each new generator of weight w is written as a Q-linear
  combination of the weight-w monomials in the old generators by solving a linear
  system on q-expansion coefficients.

  Returns:
    PhiImages - a SeqEnum of polynomials in the old ring R (built by
                ConstructWeightedPolynomialRing(OldGens)), one per new generator,
                in the flattened order of NewGens.  This is the image of each new
                generator, so PhiImages gives the map (old ring) -> (new ring) via
                R.i |-> old_gen_i and describes each new generator in terms of the
                old ones.
    R         - the old weighted polynomial ring.

  Optional parameters:
    IdealClassesSupport - restrict the coefficient comparison to a subset of the
                          narrow class group representatives (default: all).
    Prec                - number of q-expansion coefficients to use per component
                          (default: the shared precision of the forms).
    Verify              - if true (default), assert q-expansion equality between
                          each recovered image (evaluated on the old generators)
                          and the corresponding new generator.
}

  require Keys(OldGens) eq Keys(NewGens) :
    "OldGens and NewGens must be indexed by the same set of weights";

  weights := Sort(SetToSequence(Keys(NewGens)));
  require &and[#OldGens[w] eq #NewGens[w] : w in weights] :
    "OldGens and NewGens must have the same number of generators in each weight";

  oldList := FlattenGens(OldGens);
  require #oldList gt 0 : "OldGens must contain at least one generator";

  R := ConstructWeightedPolynomialRing(OldGens);

  // Fix the flattened order of the new generators once, matching FlattenGens.
  newList := FlattenGens(NewGens);
  PhiImages := [R | 0 : i in [1..#newList]];

  // We index into newList in the same weight order used to build it (sorted keys,
  // matching FlattenGens); iterating NewGens in hash order here would scramble the
  // offsets relative to newList / the ring variables.
  newOffset := AssociativeArray();
  running := 0;
  for w in Sort(Setseq(Keys(NewGens))) do
    newOffset[w] := running;
    running +:= #NewGens[w];
  end for;

  for w in weights do
    newGensW := NewGens[w];
    if #newGensW eq 0 then
      continue;
    end if;

    // Weight-w monomials in the old generators, as polynomials in R and as forms.
    // MonomialsOfWeightedDegree returns a SetIndx; EvaluateMonomials wants a SeqEnum.
    mons := [m : m in MonomialsOfWeightedDegree(R, w)];
    require #mons gt 0 :
      Sprintf("No weight-%o monomials in the old generators; cannot express new generators of that weight", w);
    monForms := EvaluateMonomials(OldGens, mons);

    // Coefficient vectors over a shared (bb, nu) index set.  We stack the old
    // monomials' forms and the new generators together so that CoefficientsMatrix
    // uses a single consistent set of coefficient keys and a single (compositum)
    // coefficient ring for both sides.
    allForms := monForms cat newGensW;
    coeffs := CoefficientsMatrix(allForms : IdealClasses := IdealClassesSupport, prec := Prec);

    A := RowSubmatrix(coeffs, 1, #monForms);          // rows: old-monomial coeff vectors
    B := RowSubmatrix(coeffs, #monForms + 1, #newGensW); // rows: new-generator coeff vectors

    // Solve X * A = B: row i of X expresses new generator i in the monomial basis.
    consistent, X := IsConsistent(A, B);
    require consistent :
      Sprintf("A new generator of weight %o is not in the span of the weight-%o monomials of the old generators (check that both sides present the same ring and precision is high enough)", w, w);

    off := newOffset[w];
    for i in [1..#newGensW] do
      PhiImages[off + i] := &+[R | X[i][j] * mons[j] : j in [1..#mons]];
    end for;
  end for;

  if Verify then
    ok, msg := VerifyChangeOfPresentation(OldGens, NewGens, PhiImages
        : IdealClassesSupport := IdealClassesSupport, Prec := Prec);
    require ok : "Recovered change of presentation failed q-expansion verification: " * msg;
  end if;

  return PhiImages, R;
end intrinsic;


intrinsic VerifyChangeOfPresentation(
  OldGens::Assoc,
  NewGens::Assoc,
  PhiImages::SeqEnum
  :
  IdealClassesSupport := false,
  Prec := false
  ) -> BoolElt, MonStgElt
{
  Verify a recovered change of presentation at the level of q-expansions.  For
  each new generator, evaluate its image PhiImages[i] (a polynomial in the old
  ring's variables) back on the old generators and check that the resulting form
  equals the corresponding new generator (as q-expansions, up to precision).

  Returns true and "" on success; false and a diagnostic message otherwise.
}
  newList := FlattenGens(NewGens);
  require #PhiImages eq #newList :
    Sprintf("Expected %o images (one per new generator), got %o", #newList, #PhiImages);

  oldList := FlattenGens(OldGens);
  require #oldList gt 0 : "OldGens must contain at least one generator";

  M := GradedRing(oldList[1]);
  if IdealClassesSupport cmpeq false then
    bbs := NarrowClassGroupReps(M);
  else
    bbs := [bb : bb in IdealClassesSupport];
  end if;

  for i in [1..#newList] do
    // Evaluate the polynomial image on the old generators to get a form, and
    // compare its q-expansion against the target new generator coefficient by
    // coefficient over a shared (bb, nu) index set.  We avoid forming a
    // SeqEnum of the two forms directly because their parents (spaces) and
    // coefficient rings may differ, which breaks common-universe coercion.
    img := EvaluatePolynomialOnForms(PhiImages[i], oldList);
    target := newList[i];

    prec := (Prec cmpeq false)
        select Min(Precision(img), Precision(target)) else Prec;

    for bb in bbs do
      for nu in FunDomainRepsUpToPrec(M, bb, prec) do
        cimg := Coefficient(img, bb, nu : InFunDomain := true);
        ctgt := Coefficient(target, bb, nu : InFunDomain := true);
        if cimg cmpne ctgt and not IsZero(cimg - ctgt) then
          return false, Sprintf("q-expansion mismatch for new generator %o at (bb=%o, nu=%o)", i, bb, nu);
        end if;
      end for;
    end for;
  end for;

  return true, "";
end intrinsic;


intrinsic VerifyGradedIsomorphism(
  Iold::RngMPol,
  Inew::RngMPol,
  PhiImages::SeqEnum
  ) -> BoolElt, MonStgElt
{
  Check that the ring map phi: R_new -> R_old defined by sending the i-th variable
  of Generic(Inew) to PhiImages[i] (a polynomial in R_old := Generic(Iold))
  descends to a well-defined graded ring homomorphism R_new/Inew -> R_old/Iold,
  i.e. that phi(Inew) is contained in Iold.

  This is the ideal-level companion to ChangeOfPresentation: given the two
  presentations' defining ideals and the images produced by ChangeOfPresentation,
  it certifies that those images realize a map of the presented rings.

  Returns true and "" on success; false and a diagnostic message otherwise.

  NOTE: PhiImages here are the images of the NEW ring's variables in terms of the
  OLD ring's variables (the natural direction when NewGens are expressed in terms
  of OldGens).  Containment phi(Inew) subset Iold then says every new relation
  maps to a relation among the old generators.
}
  Rold := Generic(Iold);
  Rnew := Generic(Inew);
  require #PhiImages eq Rank(Rnew) :
    Sprintf("Expected %o images (one per variable of the new ring), got %o", Rank(Rnew), #PhiImages);
  require &and[Parent(p) cmpeq Rold : p in PhiImages] :
    "Every image must be a polynomial in Generic(Iold)";

  phi := hom< Rnew -> Rold | PhiImages >;

  for f in Basis(Inew) do
    if not (phi(f) in Iold) then
      return false, Sprintf("image of a new-ring relation is not in the old ideal: %o", f);
    end if;
  end for;

  return true, "";
end intrinsic;
