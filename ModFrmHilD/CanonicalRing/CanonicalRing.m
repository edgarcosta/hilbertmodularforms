/////////////////////////////////////////////////////
//////////// Canonical Embeddings Code  /////////////
/////////////////////////////////////////////////////


/////////////////  Helper Functions  //////////////////



///////////   Building the Ring  //////////////////

// Builds weighted monomial ring R.
// Input: Gens: k -> Gens[k] // generators of weight k
// Output: R = Weighted polynomial ring
intrinsic ConstructWeightedPolynomialRing(Gens::Assoc)-> RngMPol
  {Return a weighted polynomial ring with #Gens[k] generators of degree k, for k in the keys of Gens}
  GenWeights := &cat[[w : j in [1..#g]] : w->g in Gens];
  R := PolynomialRing(Rationals(), GenWeights);
  return R;
end intrinsic;

intrinsic ConstructWeightedPolynomialRing(forms::List) -> RngMPol
{Return a weighted polynomial ring whose variables correspond to the given forms.}
    return PolynomialRing(Rationals(), [Weight(f)[1] : f in forms]);
end intrinsic;

intrinsic ConstructWeightedPolynomialRing(forms::SeqEnum) -> RngMPol
{Return a weighted polynomial ring whose variables correspond to the given forms.}
    return ConstructWeightedPolynomialRing([* f : f in forms *]);
end intrinsic;


// Builds The ideal I.
// Input: R = weighted polynomial ring
// Input: Relations = An associative array of relations index by weight
// Output: I
intrinsic ConstructIdeal(R::RngMPol, Relations::Assoc)-> RngMPol
  {Returns the ideal I determined by the relations}

  PolynomialList := [];
  for i in Keys(Relations) do
    PolynomialList cat:= RelationstoPolynomials(R, Relations[i], i);
  end for;
  return ideal<R | PolynomialList>;
end intrinsic;





///////////////   Conversion  /////////////////////

// This is a subfunction to the ConstructIdeal function
// Input: R = a graded polynomial ring with weighted generators
// Input: Relationlist = A list of relations in weight k. The relations are coefficients in terms of basis from MonomialsOfWeightedDegree(R,k).
// Input: k = the weight.
// Output: polynomials in the graded ring representing the relations
intrinsic RelationstoPolynomials(R::RngMPol, Relationlist::SeqEnum, k::RngIntElt) -> Any
  {Contructs polynomials from the relations}

  Monomials := MonomialsOfWeightedDegree(R, k);
  PolynomialList := [];
  for rel in Relationlist do
    RelationPolynomial := 0;
    for j := 1 to #rel do
      RelationPolynomial +:= Monomials[j]*rel[j];
    end for;
    Append(~PolynomialList, RelationPolynomial);
  end for;
  return PolynomialList;
end intrinsic;

// Converts the abstract monomials back into HMFS.
// Input: GenList = the list of HMFS corresponding to the variables of the polynomials
// Input: MonomialGens = the list of abstract polynomial generators
// Input: The space
// Output: The evaluated monomials, so a list of modular forms.
intrinsic EvaluateMonomials(Gens::Assoc, MonomialGens::SeqEnum[RngMPolElt]) -> SeqEnum
  {For a given set of HMF this produces all multiples with weight k}

  // this uses the same order as ConstructWeightedPolynomialRing
  GenList := Sum([* SequenceToList(g): w->g in Gens*] : empty := [* *]);
  return EvaluateMonomials(GenList, MonomialGens);
end intrinsic;

intrinsic EvaluateMonomials(GenList::List, MonomialGens::SeqEnum[RngMPolElt]) -> SeqEnum
{For a given set of HMF this produces all multiples with weight k}

  return [Product([* GenList[k]^exp[k] : k in [1..#GenList] *]) where exp := Exponents(mon) : mon in MonomialGens];
  /*
  for j := 1 to #MonomialGens do
    Exp := Exponents(MonomialGens[j]);
    CurrMonomial := 1;
    for k := 1 to #GenList do
      if Exp[k] ne 0 then
        CurrMonomial *:= GenList[k]^Exp[k];
      end if;
    end for;
    EvalMonomials[j] := CurrMonomial;
  end for;

  return EvalMonomials;
  */
end intrinsic;

intrinsic EvaluateMonomials(GenList::SeqEnum, MonomialGens::SeqEnum[RngMPolElt]) -> Any
  {For a given set of HMF this produces all multiples with weight k}

  return EvaluateMonomials([* f : f in GenList *], MonomialGens);
end intrinsic;

intrinsic Evaluate(F::RngMPolElt, v::SeqEnum[ModFrmHilDElt]) -> ModFrmHilDElt
{Given a multivariate polynomial `F` with `n` variables, and a list `v` of Hilbert Modular
Forms, return `F(v[1], ..., v[n])`. No attempt is made to check whether this is well-defined.}
    return Evaluate(F, [* x : x in v *]);
end intrinsic;

// TODO: Someone, somewhere may override this function because List has no element type
intrinsic Evaluate(F::RngMPolElt, v::List) -> ModFrmHilDElt
{Given a multivariate polynomial `F` with `n` variables, and a list `v`, return
`F(v[1], ..., v[n])`. No attempt is made to check whether this is well-defined.}
    coeffs, mons := CoefficientsAndMonomials(F);
    eviled_mons := EvaluateMonomials([* F *], mons);
    return &+[coeffs[i] * eviled_mons[i] : i in [1..#eviled_mons]];
end intrinsic;


////////// Computing new relations in weight k ///////////////////

// Returns monomials generating the weight k space inside R/I
// Input: MonomialsinR = MonomialsOfWeightedDegree(R,k) for the ring R
// Input: Quo = R/I The polynomial ring with weighted generators
// Input: k weight for monomials
// Output: MonomialGens = List of monomials generating the weight k space inside R/I
intrinsic MonomialGenerators(R::RngMPol, Relations::Assoc, k::RngIntElt) -> SeqEnum
  {Returns generators for the weight k monomials in R/I}
      Ideal := ConstructIdeal(R, Relations);
      return MonomialGenerators(R, Ideal, k);
end intrinsic;


intrinsic MonomialGenerators(R::RngMPol, I::RngMPol, degrees::SeqEnum[RngIntElt]) -> SeqEnum
{}
    leadmonoms := [LeadingMonomial(f) : f in GroebnerBasis(I)];
    result := [];

    for k in degrees do
        monoms := MonomialsOfWeightedDegree(R,k);
        result cat:= [f : f in monoms | &and[not IsDivisibleBy(f, m) : m in leadmonoms]];
    end for;

    return result;
end intrinsic;

intrinsic MonomialGenerators(R::RngMPol, I::RngMPol, k::RngIntElt) -> SeqEnum
{}
    return MonomialGenerators(R, I, [k]);
end intrinsic;

intrinsic MonomialGenerators(I::RngMPol, k::RngIntElt) -> SeqEnum
{}
    return MonomialGenerators(Generic(I), I, [k]);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//
// Main functions
//
//////////////////////////////////////////////////////////////////////


// Iteratively looks for generators up to MaxWeightGens and relations up to a MaxWeightRelations.
// I recommend using ConstructGeneratorsAndRelations at high precision (200-1000) and MaxWeightGens ~ 10
// and MaxWeightRelations as high as you want.
intrinsic ConstructGeneratorsAndRelations(
  M::ModFrmHilDGRng,
  N::RngOrdIdl,
  MaxWeightGens::RngIntElt,
  MaxWeightRelations::RngIntElt
  :
  LowestWeight:=2,
  Alg:="Standard",
  IdealClassesSupport:=false,
  Symmetric:=false,
  ComputeNewGenerators:=true,
  PrecomputedGens:=AssociativeArray()
  ) -> Any
  {
  Find generators and relations in M of level N. Generators will have parallel weight upto MaxWeightGens, and relations will have parallel upto MaxWeightRelations.
  Return a three Associative arrays, indexed by weight, corresponding to generators, relations and the monomials.

  The Parameters control the behaviour of this function as follows:

  'LowestWeight'         :  Specifiy the lowest weight for the generators.
  'Alg'                  :  passed to ComplementBasis.
  'IdealClassesSupport'  :  Restrict the support of the generators to a given set of components.
  'Symmetric'      :  Restrict the generators to be invariant under the automorphisms of the base field F, i.e., invariant under the swap map.
  'PrecomputedGens'      :  An AssociativeArray to provide precomputed generators.
                            It is presumed that PrecomputedGens[k] contains all generators of weight `k`.

  'ComputeNewGenerators' : Determine if the algorithm will search for missing generators, or if it can be assumed
                           that all of the generators have been provided as PrecomputedGens.
  }

  if IdealClassesSupport cmpeq false then
    IdealClassesSupport := NarrowClassGroupReps(M); // the default is all ideals classes
  end if;

  require Type(PrecomputedGens) eq Assoc: "The parameter 'PrecomputedGens' must be an associative array";
  Gens := AssociativeArray();
  Relations := AssociativeArray();
  Monomials := AssociativeArray();
  n := Degree(BaseField(M));
  CoeffCount := NumberOfCoefficients(M);

  have_dim_formula := IdealClassesSupport eq NarrowClassGroupReps(M) and not Symmetric;
  KnownRelations := false;

  /////////////////////
  // Generators of lowest weight.

  ASSUME_PARALLEL_WEIGHT := true; // This may change in the future.
  keys := Keys(PrecomputedGens);

  assert ASSUME_PARALLEL_WEIGHT;
  minimalGenWeight := 2;

  if IsDefined(PrecomputedGens, minimalGenWeight) then
      basis := PrecomputedGens[minimalGenWeight];

  elif ComputeNewGenerators then
      basis := Basis(HMFSpace(M, N, [minimalGenWeight : i in [1..n]]) : IdealClassesSupport := IdealClassesSupport, Symmetric:=Symmetric);
      assert not IsNull(basis);
  else
      msg := "No generators of parallel weight 2 found. Functionality for non-parallel weight "*
             "is currently missing. If you did use the function for the parallel weight case, "*
             "some other error has occured. Finally, if you want to compute Syzygies between "*
             "the given set of Precomputed Generators, use the function `Syzygies`.";
      error msg;
  end if;

  Gens[minimalGenWeight] := basis;
  vprintf HilbertModularForms : "Weight: %o     Generators: %o Relations: %o\n", LowestWeight, #Gens[LowestWeight],  0;

  // NOTE: Kept in case the code below inspires what to do in non-parallel weight.
  //
  /* LowestWeightBasis := []; // IsNull = True */
  /* for k := LowestWeight to MaxWeightGens by 2 do */
  /*   if IsDefined(PrecomputedGens, k) then */
  /*     Gens[k] := PrecomputedGens[k]; */
  /*     assert not IsNull(Gens[k]); */
  /*     break; */

  /*   elif ComputeNewGenerators then // Can't this be improved using the dimension formula, when available? */
  /*     Mk := HMFSpace(M, N, [k : i in [1..n]]); */
  /*     Bk := Basis(Mk : IdealClassesSupport:=IdealClassesSupport, Symmetric:=Symmetric); */

  /*     if not IsNull(Bk) then */
  /*         Gens[k] := Bk; */
  /*         break; */
  /*     end if;        */
  /*   end if; */
  /* end for; */

  /* if #Gens eq 0 then */
  /*   return <Gens, Relations, Monomials>; */
  /* end if; */

  for k := minimalGenWeight + 2 to MaxWeightRelations by 2 do
    vprintf HilbertModularForms : "Weight: %o, Gens = %o\n", k, [<elt, #Gens[elt]> : elt in Keys(Gens)];
    Mk := HMFSpace(M, N, [k : i in [1..n]]);

    if have_dim_formula then
      // Before we evaluate monomials, make sure precision is high enough
      // NOTE: we don't have dimensions per component
      require CoeffCount ge Dimension(Mk): "Precision is too low in comparison to the dimension of the space";
    end if;


    ///////////////////////////////////
    // Finding relations among the old generators in the current degree.

    sordidKeys := Sort(Setseq(Keys(Gens)));
    gens := Sum([* SequenceToList(Gens[k]): k in sordidKeys *] : empty := [* *]);

    KnownRelations, weightedSymBasis := SyzygiesAndKBase(gens, k : KnownRelations:=KnownRelations, IdealClassesSupport:=IdealClassesSupport);
    weightedSymBasis := [x : x in weightedSymBasis]; // Convert to SeqEnum
    fromLowerWeightDim := #weightedSymBasis;

    // Assign relations to the dictionary.
    weight_k_relations := [r : r in Basis(KnownRelations) | Degree(r) eq k];

    if not IsNull(weight_k_relations) then
      MonomialsinR := MonomialsOfWeightedDegree(Generic(KnownRelations), k);
      Relations[k] := [[MonomialCoefficient(rel, m) : m in MonomialsinR] : rel in weight_k_relations];
      Monomials[k] := MonomialGenerators(KnownRelations, k);
    end if;


    ///////////////////////////////////
    // Sanity check.

    if IsDefined(PrecomputedGens, k) then
        //if not IsNull(Gens[k]) then // Gens[k] is never assigned before this, so this condition looks pointless.
        Gens[k] := PrecomputedGens[k];
        shouldBeZero := #LinearDependence(Gens[k] cat weightedSymBasis : IdealClasses:=IdealClassesSupport);
        require shouldBeZero: Sprintf("A subset of PrecomputedGens[%o] can be generated by lower order terms", k);
        //end if;
    end if;

    ///////////////////////////////////
    // Adding new generators.

    if k le MaxWeightGens and not IsDefined(PrecomputedGens, k) and ComputeNewGenerators then

      knownDim := have_dim_formula select Dimension(Mk) else false;

      basisWeightk := ExtendBasis(weightedSymBasis, Mk :
                                  Alg := Alg,
                                  KnownMkDimension := knownDim,
                                  IdealClassesSupport := IdealClassesSupport,
                                  Symmetric := Symmetric);

      newGens := basisWeightk[#weightedSymBasis + 1 .. #basisWeightk];

      // Update the generators of degree k based on the computed weight k forms.
      if #newGens gt 0 then
          Gens[k] := newGens;
      end if;

      vprintf HilbertModularForms : "Weight: %o Dim: %o, fromLowerWeightDim: %o\n", k,  knownDim, fromLowerWeightDim;
    end if;

    ///////////////////////////////////
    // VPRINT INFO.
    newgens := IsDefined(Gens, k) select #Gens[k] else 0;

    // TODO: we don't have dimensions per component
    dim := have_dim_formula select Dimension(Mk) else "??";
    weight_str := Sprintf((k gt MaxWeightGens) select "Weight: %o > MaxWeightGens" else "Weight: %o", k);
    vprintf HilbertModularForms : "%o, Dimension: %o, fromLowerWeightDim: %o, New generators: %o \n", weight_str, dim, fromLowerWeightDim, newgens;
  end for;

  return <Gens, Relations, Monomials>;
end intrinsic;


intrinsic ExtendBasis(forms::SeqEnum[ModFrmHilDElt], Mk :
                      Alg                 := "Standard",
                      KnownMkDimension    := false,
                      IdealClassesSupport := false,
                      Symmetric     := false) -> SeqEnum
{Given a sequence Q of r linearly independent elements of a space M and a subspace V of M
containing the elements of Q, extend the elements of Q to a basis for U; the basis is
returned in the form of a sequence T such that T[i] = Q[i] for i in [ 1 .. r ].
It is assumed that `forms` are linearly independent.}

    if KnownMkDimension cmpne false and KnownMkDimension eq #forms then
        return forms;

    elif KnownMkDimension cmpne false and KnownMkDimension ne #forms then
        // First try our luck with just Eisenstein series. If that fails, use the fallback.

        eisensteinbasis := EisensteinBasis(Mk : IdealClassesSupport:=IdealClassesSupport, Symmetric:=Symmetric);
        moreforms := Basis(forms cat eisensteinbasis);
        coeffs_matrix := CoefficientsMatrix(moreforms : IdealClasses:=IdealClassesSupport);

        // TODO: This double complement call can surely be optimized away.
        if Rank(coeffs_matrix) eq KnownMkDimension then
            return forms cat ComplementBasis(forms, Basis(moreforms) : Alg := Alg);
        end if;
    end if;

    // Apply the fallback strategy.
    Basisweightk := Basis(Mk : IdealClassesSupport:=IdealClassesSupport, Symmetric:=Symmetric);
    return forms cat ComplementBasis(forms, Basisweightk: Alg := Alg);
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//
// Syzygies (Anticipated Interface)
//
/////////////////////////////////////////////////////////////////////////////////////

MAX_RELATION_DEGREE_DEFAULT := -999;

intrinsic Syzygies(forms : MaxRelationDegree := MAX_RELATION_DEGREE_DEFAULT) -> RngMPol
{Return the ideal of Syzygies of the given list of Hilbert Modular Forms. The Syzygies returned as an ideal generated by
the syzygies up to the degree specified by the parameter 'MaxRelationWeight'. }

    MSG := ("Please set the 'MaxRelationDegree' parameter. "
	    * "At this time we cannot determine a "
	    * "suitible bound based on theory/precision by default.");

    require MaxRelationDegree ne -999 : MSG;
    return Syzygies(forms, [2..MaxRelationDegree by 2]);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//
// Syzygies.
//
/////////////////////////////////////////////////////////////////////////////////////

// Might be better to rename this "SyzygiesOfDegree"
intrinsic Syzygies(forms, degree::RngIntElt : KnownRelations:=false) -> RngMPol
{}
    return Syzygies(forms, [degree] : KnownRelations:=KnownRelations);
end intrinsic;

// TODO: Should degree refer to the weight of the Syzygy? The implementation is certainly more complicated.
// It also totally screws up the use-case within ConstructGeneratorsAndRelations Probably should be a parameter.
//
intrinsic Syzygies(forms, degrees::SeqEnum[RngIntElt] :
                   KnownRelations := false,
                   IdealClassesSupport := false) -> RngMPol
{Return the ideal of Syzygies of the given list of Hilbert Modular Forms. The Syzygies returned as an ideal generated by
the syzygies in the degrees specified by the second input. In this case, the degree of a Syzygy refers to its weighted degree as
a polynomial in the provided forms.
Only Parallel weight is supported.}

    require #forms gt 0: "Number of forms must be non-zero.";
    Mothership := Parent(Parent(forms[1]));
    R := ConstructWeightedPolynomialRing(forms);

    // The parent of the ring containing the KnownRelations is assumed to identify with the
    // given forms via the  morphism `UPar -> k[f1, f2, ..., fn]` given by `R.i -> fi`,
    // and the remaining variables are projected away. If the relations contain any of these tail
    // variables, then an error is raised.

    if KnownRelations cmpeq false then
        I := ideal<R|>;
    else
        require Type(KnownRelations) eq RngMPol : "Known relations must be encoded as an ideal.";

        UPar := Generic(KnownRelations);
        inclusionRank := Min(Rank(R), Rank(UPar));

        tailvars := [UPar!0 : i in [1..inclusionRank]] cat [UPar.i : i in [Rank(R) + 1 .. Rank(UPar)]];
        require &and[Degree(Evaluate(rel, tailvars)) le 0 : rel in Basis(KnownRelations)] : "Uncoercible variable in relations.";

        main_part := [R.i : i in [1..inclusionRank]];
        zero_part := [0 : i in [1..Rank(UPar)-Rank(R)]];

        map_eqns :=  main_part cat zero_part;
        mp := hom<UPar->R | map_eqns>;
        I := ideal<R | [mp(f) : f in Basis(KnownRelations)]>;
    end if;

    for k in degrees do

        MonomialsGens := MonomialGenerators(R, I, k);
        EvaluatedMonomials := EvaluateMonomials(forms, MonomialsGens);
        RelationCoeffs := LinearDependence(EvaluatedMonomials : IdealClasses:=IdealClassesSupport);

        for rel in RelationCoeffs do
            p := Polynomial(rel, MonomialsGens);
            I +:= ideal<R|p>;
        end for;
    end for;

    return I;
end intrinsic;


intrinsic SyzygiesAndKBase(forms, degree::RngIntElt :
                   KnownRelations := false,
                   IdealClassesSupport := false) -> RngMPol
{}
    return SyzygiesAndKBase(forms, [degree] : KnownRelations:=KnownRelations, IdealClassesSupport:=IdealClassesSupport);
end intrinsic;

intrinsic SyzygiesAndKBase(forms, degrees::SeqEnum[RngIntElt] :
                   KnownRelations := false,
                   IdealClassesSupport := false) -> RngMPol
{Return the ideal of Syzygies of the given list of Hilbert Modular Forms as well as a basis of
modular forms for the k-vector space  `SUM_(d in degrees) k[f1, ..., fn]_d/Relations` . The degree
refers to the weight of the relation. Only Parallel weight is supported.}

    syz := Syzygies(forms, degrees : KnownRelations:=KnownRelations, IdealClassesSupport:=IdealClassesSupport);
    R := Generic(syz);

    kbase := [* *];
    for k in degrees do
        kbaseMonomials := MonomialGenerators(R, syz, k);
        kbase := kbase cat SequenceToList(EvaluateMonomials(forms, kbaseMonomials));
    end for;

    return syz, kbase;
end intrinsic;


intrinsic SymmetricPower(Mk::ModFrmHilD, m::RngIntElt :
                         KnownRelations := false,
                         IdealClassesSupport := false) -> SeqEnum
{Given a space of Hilbert modular forms (of weight `k`), compute a basis for the `m`-th
symmetric power within the space of Hilbert Modular Forms of weight `km`. }
    k := Weight(Mk)[1];
    assert k eq Weight(Mk)[2];

    return SymmetricPower(Basis(Mk), m :
                          KnownRelations:=KnownRelations,
                          IdealClassesSupport := IdealClassesSupport);
end intrinsic;

intrinsic SymmetricPower(forms::SeqEnum, m::RngIntElt:
                         KnownRelations := false,
                         IdealClassesSupport := false) -> SeqEnum
{Given a sequence of Hilbert modular forms of weight `k`, compute a basis for the `m`-th
symmetric power of the space spanned by these forms.}
    if #forms eq 0 then
        return [];
    end if;

    // TODO: Right now only parallel weight is supported.
    k := Weight(forms[1])[1];
    assert k eq Weight(forms[1])[2];
    return [f : f in WeightedSymmetricPower(forms, m*k :
                                            KnownRelations := KnownRelations,
                                            IdealClassesSupport := IdealClassesSupport)];
end intrinsic;


intrinsic WeightedSymmetricPower(forms, k:
                                 KnownRelations := false,
                                 IdealClassesSupport := false) -> SeqEnum
{Given a list of Hilbert Modular forms, compute the forms of weight `k` obtained by polynomial
combinations of the given ones.}

    _, kbase := SyzygiesAndKBase(forms, k : KnownRelations:=KnownRelations, IdealClassesSupport:=IdealClassesSupport);
    return kbase;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//
// Auxilliary functions
//
/////////////////////////////////////////////////////////////////////////////////////

intrinsic QuadSpace(D::RngIntElt, prec::RngIntElt)-> Any
  {Easy way to produces a quadratic space with Discriminant D and precision prec}

  K := QuadraticField(D);
  OK := Integers(K);
  M := GradedRingOfHMFs(K, prec);
  return M,1*OK;
end intrinsic;

intrinsic MakeScheme(Gens::Assoc, Relations::Assoc)-> Any
  {Returns the Scheme}
  R := ConstructWeightedPolynomialRing(Gens);
  PolynomialList := [];
  for i in Keys(Relations) do
    PolynomialList cat:= RelationstoPolynomials(R,Relations[i],i);
  end for;

  P := ProjectiveSpace(R);
  S := Scheme(P, PolynomialList);
  return S;
end intrinsic;

intrinsic MakeHilbertSeries(Gens::Assoc, Relations::Assoc, n::RngIntElt)-> Any
  {Returns Hilbert series with precision n}

  R := ConstructWeightedPolynomialRing(Gens);

  PolynomialList := [];
  for i in Keys(Relations) do
    PolynomialList cat:= RelationstoPolynomials(R,Relations[i],i);
  end for;

  I := ideal<R | PolynomialList>;

  N := HilbertNumerator(I);
  D := HilbertDenominator(I);
  H := HilbertSeries(I, n);

  //return N,D
  return H;
end intrinsic;

intrinsic CanonicalBasis(Gens::Assoc, Relations::Assoc, f::ModFrmHilDElt) -> Any
{return a basis for the space of modular forms in weight n, in terms of
        monomials of the "canonical" generators}

  Weight := Weight(f);
  R := ConstructWeightedPolynomialRing(Gens);
  MonomialsinR := MonomialsOfWeightedDegree(R,Weight[1]);
  MonomialsGens := MonomialGenerators(R,Relations,Weight[1]);
  EvaluatedMonomials := EvaluateMonomials(Gens, MonomialsGens);

  relations := LinearDependence(EvaluatedMonomials);
  while relations ne [] do
    r := relations[1];
  i := 1;
    while r[i] eq 0 do
      i := i + 1;
    end while;
    Remove(~EvaluatedMonomials,i);
  end while;

  return EvaluatedMonomials, MonomialsGens;
end intrinsic;

intrinsic GeneratorsAndRelations(F::FldNum, N::RngOrdIdl: Precision:=20, MaxRelationWeight:=20, MaxGeneratorWeight:=2, LowestWeight := 2, Alg := "Standard") -> Any
{returns relations up to weight MaxRelationWeight in generators up to MaxGeneratorWeight; only for parallel weight}
  GrRing := GradedRingOfHMFs(F, Precision);
  gens, rels, mons := ConstructGeneratorsAndRelations(GrRing, N, MaxGeneratorWeight, MaxRelationWeight
                                             : LowestWeight := LowestWeight,
                                               Alg := Alg);
  return gens, rels, mons;
end intrinsic;


function testGeneratorsAndRelations(F, N, Precision,
                                    MaxRelationWeight,
                                    MaxGeneratorWeight :
                                    HilbSerPrec:=20,
                                    Alg:="Standard")
  M := GradedRingOfHMFs(F,Precision);
  g, r, m := GeneratorsAndRelations(F, N : Precision := Precision,
                                    MaxRelationWeight:=MaxRelationWeight,
                                    MaxGeneratorWeight:=MaxGeneratorWeight, Alg := Alg);
  hilb := MakeHilbertSeries(g,r,HilbSerPrec);
  max_k := HilbSerPrec-2;
  ZF := Integers(F);
  dim4 := Dimension(HMFSpace(M, N, [4,4]));
  dim_eis := dim4 - Trace(HMFSpace(M, N, [4,4]), 1*ZF);
  for half_k in [2..max_k div 2] do
    k := 2*half_k;
    trace := Trace(HMFSpace(M,N,[k,k]), 1*ZF);
    if (trace + dim_eis ne Coefficient(hilb,k)) then
      vprintf HilbertModularForms : "missing generators in degree %o\n", k;
      return false, k;
    end if;
  end for;
  return true;
end function;

function polyComplexity(g,r)
    X := MakeScheme(g,r);
    polys := DefiningPolynomials(X);
    vecs := [* Vector(Coefficients(p)) : p in polys *];
    // TODO : Replace by height (max (num, denom))
    return &+[(v,v) : v in vecs];
end function;

/////////////////////////////////////////////////////
//
// Construction of schemes
//
/////////////////////////////////////////////////////

// Given a number field F, a level NN, and a bound B on the weight of the generators, return the precision (number of coefficients) required to do linear algebra
intrinsic ComputePrecisionFromHilbertSeries(NN::RngOrdIdl, B::RngIntElt) -> RngIntElt
  {Compute the number of q-expansion coefficients needed from the coefficients of the Hilbert series}
  F := NumberField(Order(NN));
  H := HilbertSeries(F,NN);
  Pow<T> := PowerSeriesRing(Rationals());
  return 10*Integers()!Coefficient(Pow!H, B) + 10;
end intrinsic;

intrinsic HilbertModularVariety(F::FldNum, N::RngOrdIdl, MaxGeneratorWeight::RngIntElt, MaxRelationWeight::RngIntElt
				: Precision := 100,
				  LowestWeight:=2,
				  Alg:="Standard",
				  IdealClassesSupport:=false,
				  Symmetric:=false,
				  ComputeNewGenerators:=true,
				  PrecomputedGens:=AssociativeArray()) -> Srfc
{ Compute a model for the (canonical ring of the) Hilbert modular surface over F of level N.
  Generators will have parallel weight upto MaxWeightGens, and relations will have parallel upto MaxWeightRelations.
  Return a three Associative arrays, indexed by weight, corresponding to generators, relations and the monomials.
  Use the optional parameter 'LowestWeight' to specifiy the lowest weight for the generators.
  The optional parameter 'Alg' is passed to ComplementBasis.
  Use the optional parameter 'IdealClassesSupport' to restrict the support of the generators to a given set of components.
  Use the optional parameter 'Symmetric' to restrict the generators to be invariant under the automorphisms of the base field F, i.e., invariant under the swap map.
  Use the optional parameters 'PrecomputedGens' as an AssociativeArray to provide precomputed generators.
  Use the optional parameters 'ComputeNewGenerators' to determine if new generators will be computed.}

  // check that precision is high enough
  require Precision ge ComputePrecisionFromHilbertSeries(N, MaxGeneratorWeight): "Precision is too low; not enough coefficients for linear algebra";

  R := GradedRingOfHMFs(F, Precision);
  dict := ConstructGeneratorsAndRelations(R, N, MaxGeneratorWeight, MaxRelationWeight:
					  LowestWeight:=LowestWeight,
					  Alg:=Alg,
					  IdealClassesSupport:=IdealClassesSupport,
					  Symmetric:=Symmetric,
					  ComputeNewGenerators:=ComputeNewGenerators,
					  PrecomputedGens:=PrecomputedGens);
  Gens := dict[1];
  Rels := dict[2];
  Mons := dict[3];

  S := MakeScheme(Gens, Rels);
  P_wtd<[x]> := Ambient(S);
  eqns_S := DefiningEquations(S);
  return S;
end intrinsic;

intrinsic HilbertModularSurface(F::FldQuad, N::RngOrdIdl, MaxGeneratorWeight::RngIntElt, MaxRelationWeight::RngIntElt
				: Precision := 100,
				  LowestWeight:=2,
				  Alg:="Standard",
				  IdealClassesSupport:=false,
				  Symmetric:=false,
				  ComputeNewGenerators:=true,
				  PrecomputedGens:=AssociativeArray()) -> Srfc
{
  Compute a model for the (canonical ring of the) Hilbert modular surface over F of level N.
  Generators will have parallel weight upto MaxWeightGens, and relations will have parallel upto MaxWeightRelations.
  Return a three Associative arrays, indexed by weight, corresponding to generators, relations and the monomials.
  Use the optional parameter 'LowestWeight' to specifiy the lowest weight for the generators.
  The optional parameter 'Alg' is passed to ComplementBasis.
  Use the optional parameter 'IdealClassesSupport' to restrict the support of the generators to a given set of components.
  Use the optional parameter 'Symmetric' to restrict the generators to be symmetric under the automorphisms of the base field F, i.e., invariant under the swap map.
  Use the optional parameters 'PrecomputedGens' as an AssociativeArray to provide precomputed generators.
  Use the optional parameters 'ComputeNewGenerators' to determine if new generators will be computed.}
  return HilbertModularVariety(F, N, MaxGeneratorWeight, MaxRelationWeight
			       : Precision:=Precision,
				 LowestWeight:=LowestWeight,
				 Alg:=Alg,
				 IdealClassesSupport:=IdealClassesSupport,
				 Symmetric:=Symmetric,
				 ComputeNewGenerators:=ComputeNewGenerators,
				 PrecomputedGens:=PrecomputedGens);

    // return Surface(P, eqns_S);
end intrinsic;

intrinsic HilbertModularImage(forms::List, maxRelationDegree::RngIntElt) -> Sch
{Given a list (of type List) of Hilbert modular forms, compute the Zariski closure of the image of the rational map
defined by these forms into a weighted projective space (with weights the weight of the forms).
The second argument determines the maximum degree in which Syzygies are searched for.}

    syz := Syzygies(forms : MaxRelationDegree := maxRelationDegree);
    R   := Generic(syz);
    Amb := Proj(R);
    return Scheme(Amb, syz);
end intrinsic;

/////////////////////////////////////////////////////
//
//    Generator bound.
//
/////////////////////////////////////////////////////

intrinsic GeneratorWeightBound(F::FldNum) -> RngIntElt
{}
    return GeneratorWeightBound(F, 1*MaximalOrder(F));
end intrinsic;

intrinsic GeneratorWeightBound(F::FldNum, N::RngOrdIdl) -> RngIntElt
{}
    return GeneratorWeightBound(CongruenceSubgroup(F, N));
end intrinsic;

intrinsic GeneratorWeightBound(G::GrpHilbert) -> RngIntElt
{Determine a bound for the maximum weight of a generator in the graded ring of modular forms.}
    error "Not Implemented.";
    return -9999;
end intrinsic;


// TODO: Eventually, this will be converted into the correct function.
intrinsic GeneratorWeightBound(G::GrpHilbert : experiment:=false) -> Any
{Experiment with the Neves style argument.}

    // The algorithm to compute a degree bound on the generator can be found in the Overleaf
    // document associated to the paper. It proceeds along the following steps.

    // 1. Compute the self-intersection number of the log-canonical sheaf.
    //    NOTE: The Chern numbers of the log canonical are Not Necessarily Integers!
    Lsqed := ChernNumberOfLogCanonical(G, 1);

    // 2. Compute the multiple of the log-canonical sheaf that's an actual line bundle.
    // TODO: Address the special cases after things have been worked out.

    D := Discriminant(BaseField(G));
    if D eq 5 then
	m := 15;
    elif D eq 8 then
	m := 3;
    elif D eq 12 then
	m := 3;
    else
	ell_types := Keys(EllipticPointData(G));
	if <3, 1, 1> in ell_types then
	    m := 3;
	else
	    m := 1;
	end if;
    end if;


    // 3. Compute the genus of a section cut out by `f \in m*L` via adjuction.
    //    NOTE: As is explained in the paper, `L.{Resolution cycles} = 0`.
    deg_can := m * (m+1) * Lsqed;
    g := deg_can/2 + 1;
    degLC := m * Lsqed;

    // 4. Compute the Hilbert series.
    hilb := HilbertSeries(G);
    P<s> := Parent(hilb);
    t := s^2;

    // 5. Use Hilbert series arithmetic to contruct a polynomial measuring the difference
    //    between the Hilbert series and the Hilbert series of the restriction to `Z(f)`.
    hilbI := hilb * t^m;

    Q := 1 + degLC * t/(1-t)^2 + (1-g) * t/(1-t); // Riemann-Roch.
    Q +:= t^m; // The section `f` counts as a generator.


    // 6. The degree of this polynomial reveals the path to victory.
    poly := hilb - hilbI - Q;

    if experiment then
	return g, hilb, hilbI, Q, poly;
    end if;

    assert Denominator(poly) eq 1;

    // The only generators not accounted for in the restriction come from below the weight
    // of the section.
    return Maximum(m, Degree(Numerator(poly)));
end intrinsic;

intrinsic HilbertSeriesSanityCheck(M::ModFrmHilDGRng, NN::RngOrdIdl, Is::SeqEnum[RngMPol]) -> BoolElt
  {Given a sequence Is of ideals defining graded rings, check if the sum of their Hilbert series agrees with the one coming from the trace formula (which includes all components)}
  H_trace := HilbertSeries(M,NN);
  H_test := &+[HilbertSeries(I) : I in Is];
  vprintf HilbertModularForms: "series from trace formula = %o\n", H_trace;
  vprintf HilbertModularForms: "series from computed graded ring= %o\n", H_test;
  return H_test eq H_trace, H_trace, H_test;
end intrinsic;

intrinsic HilbertSeriesSanityCheck(M::ModFrmHilDGRng, NN::RngOrdIdl, Rs::SeqEnum[RngMPolRes]) -> BoolElt
  {Given a sequence Rs of graded rings, check if the sum of their Hilbert series agrees with the one coming from the trace formula (which includes all components)}
  return HilbertSeriesSanityCheck(M, NN, [PreimageIdeal(ideal< R | 0>) : R in Rs]);
end intrinsic;

intrinsic HilbertSeriesSanityCheck(M::ModFrmHilDGRng, NN::RngOrdIdl, Ss::SeqEnum[Sch]) -> BoolElt
  {Given a sequence Ss of surfaces, check if the sum of their Hilbert series agrees with the one coming from the trace formula (which includes all components)}
  return HilbertSeriesSanityCheck(M, NN, [Ideal(S) : S in Ss]);
end intrinsic;
