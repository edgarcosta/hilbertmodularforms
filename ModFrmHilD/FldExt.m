// save fundamental unit
declare attributes FldAlg:
  TotallyPositiveUnits,
  TotallyPositiveUnitsMap,
  TotallyPositiveUnitsGenerators,
  TotallyPositiveUnitsGeneratorsOrients,
  UnitsGenerators,
  ClassGroupReps,
  MarkedEmbedding,
  Extensions,
  Restrictions,
  UnitCharFieldsByWeight,
  MinDistBtwnRoots
  ;


/////////////////////// (Narrow) Class Group Representatives ////////////
// FIXME : Move narrow class group code from graded ring to this section

intrinsic ClassGroupReps(F::FldAlg) -> SeqEnum
  {Return ideal representatives for the class group}
  if not assigned F`ClassGroupReps then 
    C, mC := ClassGroup(F);
    Reps := [ mC(i) : i in C ];
    F`ClassGroupReps := Reps;
  end if;
  return F`ClassGroupReps;
end intrinsic;

intrinsic CoprimeNarrowRepresentative(I::RngOrdIdl, J::RngOrdIdl) -> RngOrdElt
{Find a totally positive field element a such that qI is an integral ideal coprime to J;
 I and J must be defined over the same maximal order.}

    K := NumberField(Order(I));
    q := CoprimeRepresentative(I, J);

    // Nothing to do if K is imaginary or we already chose a good element.
    if Signature(q) eq [1,1] or Discriminant(K) lt 0 then return q; end if;
    if Signature(q) eq [-1,-1] then return -q; end if;

    // Otherwise, we have chosen a bad element, so must correct the signs.
    z := Sqrt(K!Discriminant(Integers(K)));
    require Norm(z) lt 0 : "Chosen generator of quadratic field is totally positive.";
    assert IsIntegral(z);
    
    if Signature(z) ne Signature(q) then
	z := -z;
    end if;

    NJ := Norm(J);
    d := GCD(Integers() ! Norm(z), NJ);

    if d eq 1 then return z*q; end if;
    b := ExactQuotient(NJ, d);
    return (1 + b * z)*q;
end intrinsic;

/////////////////////// Units and totally positive units /////////////////

intrinsic Signature(a::RngOrdElt) -> SeqEnum
  {}
  R := Parent(a);
  return Signature(FieldOfFractions(R)!a);
end intrinsic;

intrinsic TotallyPositiveUnits(F::FldAlg) -> GrpAb, Map
  {return the group of totally positive units of the base as an abstract group and the map from abstract totally positive unit group into F^\times_>0}

  if not assigned F`TotallyPositiveUnits or not assigned F`TotallyPositiveUnitsMap then
    U, mp := UnitGroup(F);
    // Stupid function, the isomorphism mu_2 -> ZZ/2*ZZ
    hiota := function(u);
      if u eq -1 then
        return 1;
      else
        return 0;
      end if;
    end function;

    F := NumberField(F);
    UZd := AbelianGroup([2 : i in [1..Degree(F)]]);
    phi := hom<U -> UZd | [[hiota(Sign(Evaluate(mp(U.i), v))) : v in RealPlaces(F)] : i in [1..#Generators(U)]]>;
    K := Kernel(phi);
    F`TotallyPositiveUnits := K;
    F`TotallyPositiveUnitsMap := mp;
  end if;

  return F`TotallyPositiveUnits, F`TotallyPositiveUnitsMap;
end intrinsic;

intrinsic FundamentalUnit(F::FldNum) -> FldElt
  {The fundamental unit of F}
  K := QuadraticField(Discriminant(Integers(F)));
  b, phi := IsIsomorphic(K, F);
  return phi(FundamentalUnit(K));
end intrinsic;

// The algorithm for producing generators is nondeterministic, so we need to "orient" 
// our chosen generators to avoid randomness. This particular choice remains
// consistent with the existing behavior of FundamentalUnitTotPos
function orient(F, eps)
  v := InfinitePlaces(F)[1];
  return (Abs(Evaluate(eps, v)) lt 1) select eps else eps^-1;
end function;

intrinsic TotallyPositiveUnitsGenerators(F::FldNum) -> SeqEnum[RngOrdElt]
  {
    parameters:
      F: a number field
    returns:
      A sequence of elements of the ring of integers
      which generate the group of totally positive units.
  }

  if Degree(F) eq 1 then
    return [Integers(F)!1];
  end if;

  if not assigned F`TotallyPositiveUnitsGenerators then
    PU, mPU := TotallyPositiveUnits(F);
    tpugs_unorient := [Integers(F)!mPU(gen) : gen in Generators(PU)];

    v := InfinitePlaces(F)[1];
    F`TotallyPositiveUnitsGenerators := [];
    F`TotallyPositiveUnitsGeneratorsOrients := [];

    // The algorithm for producing generators is nondeterministic, so we need to "orient" 
    // our chosen generators to avoid randomness. This particular choice remains
    // consistent with the existing behavior of FundamentalUnitTotPos
    //
    // We keep track of which generators are inverted with respect to the 
    // Generators(F`TotallyPositiveUnits) because we need to solve the word
    // problem in the unit generators code and it solves it there with respect
    // to Generators(F`TotallyPositiveUnits).
    for eps in tpugs_unorient do
      if Evaluate(eps, v) lt 1 then
        Append(~F`TotallyPositiveUnitsGenerators, eps);
        Append(~F`TotallyPositiveUnitsGeneratorsOrients, 1);
      else
        Append(~F`TotallyPositiveUnitsGenerators, eps^-1);
        Append(~F`TotallyPositiveUnitsGeneratorsOrients, -1);
      end if;
    end for;
  end if;
  return F`TotallyPositiveUnitsGenerators;
end intrinsic;

intrinsic TotallyPositiveUnitsGeneratorsOrients(F::FldNum) -> SeqEnum
  {
    Returns a sequence whose ith entry e is such that the 
    ith element of SetToSequence(Generators(TotallyPositiveUnits)) is the
    ith element of F`TotallyPositiveUnitsGenerators raised to the eth power.

    Here, e will either be 1 or -1. 
  }
  _ := TotallyPositiveUnitsGenerators(F);
  return F`TotallyPositiveUnitsGeneratorsOrients;
end intrinsic;

intrinsic UnitsGenerators(F::FldNum : exclude_torsion:=true) -> SeqEnum[RngOrdElt]
  {
    parameters:
      F: a number field
    returns:
      A sequence of elements of the ring of integers
      which generate the group of units.
  }
  if not assigned F`UnitsGenerators then
    U, mU := UnitGroup(F);
    require Order(U.1) gt 0 : "The first generator of the units group seems to no longer\
      be the generator of torsion, so you should update the code to find the generator\
      of torsion.";
    gens := (exclude_torsion) select Exclude(Generators(U), U.1) else Generators(U);
    ugs_unorient := [mU(gen) : gen in gens];
    F`UnitsGenerators := [orient(F, eps) : eps in ugs_unorient];
  end if;
  return F`UnitsGenerators;
end intrinsic;

/////////////////////// MarkedEmbedding and strong coercion ///////////////////////////

intrinsic MarkedEmbedding(K::FldNum) -> PlcNumElt
  {
    input:
      K: a number field
    returns:
      A distinguished infinite place of K.
      By default, this is the first infinite place.

    This function is here so that whenever
    we choose a distinguished place of K,
    we make the same choice. 
  }
  if assigned K`MarkedEmbedding then
    return K`MarkedEmbedding;
  end if;
  K`MarkedEmbedding := InfinitePlaces(K)[1];
  return K`MarkedEmbedding;
end intrinsic;

intrinsic IsStrongCoercible(L::Fld, x::.) -> BoolElt, FldElt
  {
    input:
      L - FldNum, FldQuad, FldCyc, or FldRat
      x - Any, but can return true only on a FldElt or RngElt
    returns:
      false if x cannot be coerced into L. 
      true if x can be coerced into L, along with
        the strong coercion of x into L.
  }

  // strong coercion is possible if and only if
  // regular coercion is possible
  if IsCoercible(L, x) then
    return true, StrongCoerce(L, x);
  else
    return false, _;
  end if;
end intrinsic;

intrinsic StrongCoerce(L::Fld, x::RngElt) -> FldElt
  {
    input: 
      L - FldNum, FldQuad, FldCyc, or FldRat
      x - An element of the ring of integers of one of the above
    returns:
      StrongCoerce applied to x coerced into its field of fractions.
  }

  K := FieldOfFractions(Parent(x));
  return StrongCoerce(L, K!x);
end intrinsic;

intrinsic StrongCoerce(L::Fld, x::FldElt) -> FldElt
  {
    input: 
      L - FldNum, FldQuad, FldCyc, or FldRat
      x - An element of one of the above 
    returns:
      Returns x as an element of L, such that evaluation at 
      the distinguished place of the Parent of x is equal to
      evaluation of StrongCoerce(L, x) at the distinguished place
      of L.

    Write K for the parent number field of x. There are two cases.

    If K is a subfield of L and K_prim is a primitive
    element of K, we fix an inclusion iota of K into L and find an automorphism
    aut of K such that 

    w(L!(aut(K_prim))) = v(K_prim).

    Equivalently, we choose an inclusion of K into L which commutes with evaluation
    under the distinguished places.
    
    If K contains L, then we choose a primitive element L_prim of L and
    find an automorphism aut of K such that

    w(L!aut(K!L_prim)) = v(K!L_prim),

    Equivalently, we choose an automorphism of K so that restriction to L commutes 
    with evaluation under the distinguished places.
  }

  require Type(x) in [FldNumElt, FldRatElt, FldQuadElt, FldCycElt] : "%o is not a valid type for strong coercion", Type(x);

  // If x is rational then all embeddings are the same,
  // We do this case separately because Rationals() 
  // does not have an Extensions attribute.
  if x in Rationals() then
    return L!x;
  end if;

  K := Parent(x);

  // If L = QQ then all restrictions are the same.
  if L eq Rationals() then
    return Rationals()!x;
  end if;

  // We trust Magma's coercion if K and L have the same
  // defining polynomial
  if DefiningPolyCoeffs(K) eq DefiningPolyCoeffs(L) then
    require IsIsomorphic(K, L) : "This should never happen, something is quite wrong";
    return L!x;
  end if;

  if not assigned K`Extensions then
    K`Extensions := AssociativeArray();
  end if;
  if not assigned K`Restrictions then
    K`Restrictions := AssociativeArray();
  end if;

  require IsGalois(K) : "Strong coercion is not yet implemented\
      for non-Galois initial fields";

  // if K = QQ then all embeddings are the same
  if K eq Rationals() then
    K`Extensions[DefiningPolyCoeffs(L)] := Automorphisms(Rationals())[1];
  end if;

  // if L = QQ then all restrictions are the same
  if L eq Rationals() then
    K`Restrictions[DefiningPolyCoeffs(L)] := Automorphisms(K)[1];
  end if;

  if IsDefined(K`Extensions, DefiningPolyCoeffs(L)) then
    phi := K`Extensions[DefiningPolyCoeffs(L)];
    return L!phi(x);
  elif IsDefined(K`Restrictions, DefiningPolyCoeffs(L)) then
    phi := K`Restrictions[DefiningPolyCoeffs(L)];
    return L!phi(x);
  end if;

  v := MarkedEmbedding(K);
  w := MarkedEmbedding(L);

  if IsSubfield(K, L) then
    a := PrimitiveElement(K);
    a_eval := ComplexField()!Evaluate(a, v);
    auts := Automorphisms(K);
    for aut in auts do
      if Abs(ComplexField()!Evaluate(L!aut(a), w) - a_eval) lt 0.5 * MinDistBtwnRoots(K) then
        K`Extensions[DefiningPolyCoeffs(L)] := aut;
        return StrongCoerce(L, x);
      end if;
    end for;
    require 0 eq 1 : "This should not be possible. Something has gone wrong.";
  elif IsSubfield(L, K) then
    auts := Automorphisms(K);
    a := K!PrimitiveElement(L);
    a_eval := ComplexField()!Evaluate(a, v);
    for aut in auts do
      // TODO abhijitm - This currently fails to coerce an element of a cyclotomic
      // field extended from a number field back into that number field 
      // For exmaple, if x is in K and L is a cyclotomic field containing K, then
      // L!x will succeed but K!(L!x) will fail. This case is not important right
      // now so I'm leaving it to future me (or present you!) to fix it. 
      if Abs(ComplexField()!Evaluate(L!aut(a), w) - a_eval) lt 0.5 * MinDistBtwnRoots(K) then
        K`Restrictions[DefiningPolyCoeffs(L)] := aut;
        return StrongCoerce(L, x);
      end if;
    end for;
    require 0 eq 1 : "This should not be possible. Something has gone wrong.";
  else
    require 0 eq 1 : "The parent of x neither contains nor is contained in L", K, L;
  end if;
end intrinsic;

intrinsic ListToStrongCoercedSeq(A::List) -> SeqEnum
  {
    input:
      A - A list of number field elements
    returns:
      A sequence containing the elements of the list, strong coerced
      into a common parent field.
  }
  L := Rationals();
  for a in A do
    // in case a is a RngElt instead of a FldElt
    K := NumberField(Parent(a));
    L := (K eq L) select L else Compositum(L, K);
  end for;

  B := [];
  for a in A do
    Append(~B, StrongCoerce(L, a));
  end for;
  return B;
end intrinsic;

intrinsic StrongMultiply(A::List : K:=false) -> FldElt
  {
    input:
      A - A list of elements (strong) coercible into K, not necessarily
        from the same parent field.
      K - A field of type FldRat, FldCyc, FldNum, or FldQuad
    returns:
      The product of the elements in A, as an element of K.
  }

  // perform normal multiplication if all the objects 
  // are of the same type
  if &and[Parent(x) cmpeq Parent(A[1]) : x in A] then
    return &*[x : x in A];
  end if;
      
  // If K is not assigned, it should be the compositum
  // of all the elements
  if K cmpeq false then
    K := RationalsAsNumberField();
    for x in A do
      K := Compositum(K, NumberField(Parent(x)));
    end for;
  end if;
      
  prod := K!1;
  for x in A do
    y := (Type(x) in [FldRatElt, RngIntElt]) select x else StrongCoerce(K, x);
    prod *:= y;
  end for;
  return prod;
end intrinsic;

intrinsic StrongAdd(A::List : K:=false) -> FldElt
  {
    input:
      A - A list of elements (strong) coercible into K, not necessarily
        from the same parent field.
      K - A field of type FldRat, FldCyc, FldNum, or FldQuad
    returns:
      The sum of the elements in A, as an element of K.
  }

  // perform normal addition if all the objects 
  // are of the same type
  if &and[Parent(x) cmpeq Parent(A[1]) : x in A] then
    return &+[x : x in A];
  end if;

  // If K is not assigned, it should be the compositum
  // of all the elements
  if K cmpeq false then
    K := RationalsAsNumberField();
    for x in A do
      K := Compositum(K, NumberField(Parent(x)));
    end for;
  end if;

  sum := K!0;
  for x in A do
    y := (Type(x) in [FldRatElt, RngIntElt]) select x else StrongCoerce(K, x);
    sum +:= y;
  end for;
  return sum;
end intrinsic;

intrinsic StrongEquality(x::Any, y::Any : K:=false) -> BoolElt
  {
    Given elements x and y of possibly different fields,
    return true if and only if they are equal after
    strong embedding into their compositum.
  }
  if x cmpeq y then
    return true;
  end if;

  if K cmpeq false then
    K := Compositum(NumberField(Parent(x)), NumberField(Parent(y)));
  end if;

  return StrongCoerce(K, x) eq StrongCoerce(K, y);
end intrinsic;

intrinsic MinDistBtwnRoots(K::FldAlg) -> FldReElt
  {
    Returns the minimum absolute value distance between 
    two roots of the defining polynomial of K.
  }
  if not assigned K`MinDistBtwnRoots then
    f := DefiningPolynomial(K);
    roots := [tup[1] : tup in Roots(ChangeRing(f, ComplexField()))];
    require #roots eq Degree(K) : "Something is wrong,\
      the multiplicity of every root should be one";
    require #roots gt 1 : "This shouldn't get called on the rationals";

    min_dist := Abs(roots[1] - roots[2]);
    for i in [1 .. #roots] do
      for j in [i+1 .. #roots] do
        min_dist := Min(Abs(roots[i] - roots[j]), min_dist);
      end for;
    end for;
    K`MinDistBtwnRoots := min_dist;
  end if;
  return K`MinDistBtwnRoots;
end intrinsic;

/////////////////////// coefficient ring ///////////////////////////

intrinsic NonSquareTotPosUnitsGens(F::FldNum) -> SeqEnum[RngOrdElt]
  {
    inputs:
      F: A totally real number field
    returns:
      The subsequence of TotallyPositiveUnitsGenerators(F) which 
      are not squares. These elements generate the group
      of totally positive units modulo the squares.
  }
  R<x> := PolynomialRing(F);
  for eps in TotallyPositiveUnitsGenerators(F) do
    out := [];
    if IsIrreducible(x^2-eps) then
      Append(~out, eps);
    end if;
  end for;
  return out;
end intrinsic;

intrinsic UnitCharField(F::FldNum, k::SeqEnum[RngIntElt]) -> FldNum
  {
    input:
      F: The base number field of the HMF.
      k: The weight of the HMF
    returns:
      The extension in which the output of the unit character lives.
  }
  return UnitCharFieldsByWeight(F, k);
end intrinsic;

intrinsic UnitCharFieldsByWeight(F::FldNum, k::SeqEnum[RngIntElt]) -> FldNum
  {
    input:
      F: The base number field of the HMF.
      k: The weight of the HMF
    returns:
      The extension in which the output of the unit character lives.

      If k is paritious, the output of the unit charactere
      lies in the splitting field of F.
      TODO abhijitm can do a little bit better
      than this (Phi \subseteq Spl(F) as Shimura calls it),
      but this is certainly true.

      If k is non-paritious, we return the compositum
      of the splitting field of F and
      the field generated by the polynomials
      x^2-eps_i for [eps_1, .., eps_(n-1)]
      a set of generators for the group of totally positive
      units of F.

      This is cached by (F, k) pair to reduce compatibility issues.
  }
  if assigned F`UnitCharFieldsByWeight then
    if IsDefined(F`UnitCharFieldsByWeight, k) then
      return F`UnitCharFieldsByWeight[k];
    end if;
  else
    F`UnitCharFieldsByWeight := AssociativeArray();
  end if;

  R<x> := PolynomialRing(F);
  if IsParallel(k) then
    // if the weight is parallel, the unit character is trivial
    L := Rationals();
  elif IsParitious(k) then
    L := SplittingField(F);
  else
    polys := [];
    for eps in NonSquareTotPosUnitsGens(F) do
      Append(~polys, x^2-eps);
    end for;
    K := (#polys eq 0) select F else AbsoluteField(ext<F | polys>);
    L := SplittingField(K);
  end if;
  F`UnitCharFieldsByWeight[k] := L;
  return L;
end intrinsic;

/////////////////////// unit character ///////////////////////////

intrinsic AutsOfKReppingEmbeddingsOfF(F::FldNum, K::FldNum : Precision := 25) -> SeqEnum[Map]
  { 
    inputs:
      F: A number field of degree n
      K: A Galois number field containing the Galois closure of F.
    returns:
      We return a list [sigma_1, ..., sigma_n] 
      of automorphisms of K sorted such that if 
      [v_1, ..., v_n] is a list of embeddings of F, 
      then v_i(x) = v_0(sigma_i(x)) for all x in F. 
      Note that when F is not Galois, this list is
      not unique, but our algorithm is deterministic.
  }
  require IsSubfield(SplittingField(F), K) : "K must contain the Galois closure of F";
  require IsGalois(K) : "K needs to be a Galois field";
  n := Degree(F);
  places := InfinitePlaces(F);

  a := PrimitiveElement(F);
  a_embed_dict := AssociativeArray();
  r, s := Signature(F);
  for i in [1 .. r] do
    z_i := Round(10^Precision*Evaluate(a, places[i]));
    a_embed_dict[z_i] := i;
  end for;

  for i in [r+1 .. r+s] do
    z_i := Round(10^Precision*Evaluate(a, places[i]));
    a_embed_dict[z_i] := i;
    a_embed_dict[Conjugate(z_i)] := i + s;
  end for;

  // a distinguished place of K 
  // if we want to view our HMFs as having coefficients over C,
  // we should apply v_0 to all the coefficients
  v_0 := MarkedEmbedding(K);
  
  aut_dict := AssociativeArray();
  for aut in Automorphisms(K) do
    aut_a_est := Round(10^Precision*Evaluate(aut(a), v_0));
    b, x := IsDefined(a_embed_dict, aut_a_est);
    if b then
      aut_dict[x] := aut;
      Remove(~a_embed_dict, aut_a_est);
      if #a_embed_dict eq 0 then
        break aut;
      end if;
    end if;
  end for;

  require #Keys(aut_dict) eq n : "Something's wrong, there should\
    be at one stored automorphism for each embedding of F";
  return [aut_dict[i] : i in [1 .. n]];
end intrinsic;

intrinsic AutsOfUCFReppingEmbeddingsOfF(F::FldNum, k::SeqEnum[RngIntElt] : Precision := 50) -> SeqEnum[Map]
  { 
    inputs:
      F: A real Galois number field of degree n
      k: A weight, given as a SeqEnum of n natural numbers
    returns:
      AutsOfKReppingEmbeddingsOfF applied with K equal to
      the unit character field associated to F and k.
  }
  K := UnitCharField(F, k);
  return AutsOfKReppingEmbeddingsOfF(F, K);
end intrinsic;

intrinsic ComplexConjugateOfPlace(w::PlcNumElt) -> FldElt
  {
    inputs:
      w: A complex place of a number field K.
    returns:
      An automorphism aut of K such that
      for any x in K, v_0(aut(x)) is the
      complex conjugate of v_0(x).
  }
  K := NumberField(w);
  require IsGalois(K) : "K is not Galois";
  require IsComplex(w) : "w is not a complex place";

  auts := AutsOfKReppingEmbeddingsOfF(K, K);
  w_idx := Index(w, auts);
  s := Integers()!(Degree(K) / 2);
  return auts[w_idx + s];
end intrinsic;

intrinsic EltToShiftedHalfWeight(x::FldElt, k::SeqEnum[RngIntElt]) -> FldElt
  {
    inputs: 
      x: A totally positive element of a number field F. 
         If k is nonparitious, we require x to be a totally
         positive unit. 
         // TODO abhijitm feels weird, will come back to it later,
         // but the point is that we won't actually run this in the
         // eigenvalue -> Fourier coefficient computation for
         // nonparitious (and maybe eventually all) weights,
         // so it only gets used to compute unit characters. 
      k: A weight
    returns:
      We want to compute the element
      y := \prod_i x_i^((k_0-k_i)/2)
      where x_i is the image of eps under the ith real embedding of F,
      k = (k_1, ..., k_n) is the weight, and k_0 = max_i(k_i). 

      This quantity appears in the computation of the unit character 
      as well as the computation of Fourier coefficients from Hecke eigenvalues.

      The element y will lie in the UnitCharField(F,k). 
  }
  assert IsTotallyPositive(x);
  if not IsParitious(k) then
    assert Norm(x) eq 1;
  end if;

  // extra NumberField to deal with when x is FldOrdElt
  F := NumberField(Parent(x));
  K := UnitCharField(F, k);
  k0 := Max(k);

  if IsParallel(k) then
    return K!1;
  end if;

  auts := AutsOfUCFReppingEmbeddingsOfF(F, k);
  if IsParitious(k) then
    // paritious nonparallel weight
    return &*[auts[i](K!x)^(ExactQuotient(k0 - k[i], 2)) : i in [1 .. #auts]];
  else
    // nonparitious weight
    v_0 := MarkedEmbedding(K);
    y := &*[auts[i](Sqrt(K!x))^(k0 - k[i]) : i in [1 .. #auts]];
    return PositiveInPlace(y, v_0);
  end if;
end intrinsic;

intrinsic PositiveInPlace(nu::FldNumElt, v::PlcNumElt) -> FldNumElt
  {
    input: 
      nu: An element of a number field F
      v: A place of F
    return:
      nu if v(nu) > 0 and -nu otherwise.
  }
  return (Evaluate(nu, v) gt 0) select nu else -1*nu;
end intrinsic;

intrinsic PositiveSqrt(nu::FldNumElt, K::FldNum) -> FldNumElt
  {
    input:
      nu: An element of a number field F
      K: A number field containing nu and a square root of nu.
    return:
      mu such that mu^2 = nu and mu is positive in the distinguished
      place of K.
  }
  mu := Sqrt(K!nu);
  v_0 := MarkedEmbedding(K);
  return (Evaluate(mu, v_0) ge 0) select mu else -1*mu;
end intrinsic;

intrinsic NormToHalfWeight(I::RngFracIdl, k0::RngIntElt, K::FldNum) -> FldNumElt
  {
    input:
      I: A fractional ideal
      k0: A nonnegative integer
      K: A number field containing Norm(I)^(k0/2)
    return:
      Norm(I)^(k0/2)
  }
  Nm := K!Norm(I);
  return (k0 mod 2 eq 0) select Nm^(ExactQuotient(k0, 2)) else Nm^(k0/2);
end intrinsic;

intrinsic DefiningPolyCoeffs(K::Fld) -> SeqEnum
  {}
  if K eq Rationals() then
    K := RationalsAsNumberField();
  end if;
  return Coefficients(DefiningPolynomial(K));
end intrinsic;

intrinsic TraceBasis(aa::RngOrdFracIdl) -> SeqEnum
  {Given a fractional ideal aa, returns a basis (a,b) in Smith normal form
   where Trace(a) = n > 0 and Trace(b) = 0}

  // Preliminaries
  B := Basis(aa);
  ZF := Parent(B[2]);
  v := InfinitePlaces(NumberField(ZF))[2];

  // Change of basis
  traces := Matrix([[Integers()!Trace(B[i])] : i in [1..#B]]);
  _, Q := HermiteForm(traces);

  TB := Eltseq(Vector(B)*Transpose(ChangeRing(Q,ZF)));
  assert Trace(TB[1]) gt 0;
  assert &and[Trace(TB[i]) eq 0 : i in [2 .. #TB]];

  // Orienting the basis
  for i in [2 .. #TB] do
    if Evaluate(TB[i], v) lt 0 then
      TB[i] *:= -1;
    end if;
  end for;
  return TB;
end intrinsic;

intrinsic MinkowskiConstant(F::FldAlg) -> FldReElt
  {
    Returns the Minkowski constant of F.
  }
  s := #InfinitePlaces(F) - #RealPlaces(F);
  pi := Pi(RealField());
  D := Discriminant(Integers(F));
  n := Degree(F);
  return Sqrt(Abs(D)) * (4 / pi)^s * n^n / Factorial(n);
end intrinsic;

intrinsic LargestRootOfUnity(K::FldAlg) -> RngIntElt
  {
    Given a number field K, returns the largest d such that 
    zeta_d lies in K.
  }
  n := Degree(K);

  R<x> := PolynomialRing(K);
  p_pows := [];
  for p in PrimesUpTo(n+1) do
    k := Floor(Log(p, n+1));
    root_ct := #Roots(x^(p^k)-1);
    e := Integers()!Log(p, root_ct);
    Append(~p_pows, <p, e>);
  end for;

  m := &*[tup[1]^tup[2] : tup in p_pows];
  require IsSubfield(CyclotomicField(m), K) : "Something's wrong, the field\
      Q(zeta_m) isn't a subfield of K";
  return m;
end intrinsic;

intrinsic IsGalois(F::FldAlg) -> BoolElt
  {
    IsNormal fails if the defining polynomial of F has non-integral coefficients.
  }
  if &and[IsIntegral(a) : a in DefiningPolyCoeffs(F)] then
    return IsNormal(F);
  else
    return #Automorphisms(F) eq Degree(F);
  end if;
end intrinsic;
