// save fundamental unit
declare attributes FldAlg:
  TotallyPositiveUnits,
  TotallyPositiveUnitsMap,
  TotallyPositiveUnitsGenerators,
  TotallyPositiveUnitsGeneratorsOrients,
  FundamentalUnitSquare,
  ClassGroupReps,
  DistinguishedPlace,
  Extensions,
  Restrictions,
  UnitCharFieldsByWeight
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


/////////////////////// Totally positive associate /////////////////

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

intrinsic UnitsGenerators(F::FldNum) -> SeqEnum[RngOrdElt]
  {
    parameters:
      F: a number field
    returns:
      A sequence of elements of the ring of integers
      which generate the group of units.
  }

  U, mU := UnitGroup(F);
  ugs_unorient := [mU(gen) : gen in Exclude(Generators(U), U.1)];
  return [orient(F, eps) : eps in ugs_unorient];
end intrinsic;

intrinsic FundamentalUnitSquare(F::FldNum) -> RngQuadElt
  {return the fundamental unit totally positive}
  assert Degree(F) le 2;
  if Degree(F) eq 1 then
    return Integers(F)!1;
  end if;
  if not assigned F`FundamentalUnitSquare then
    eps := FundamentalUnit(F)^2;
    places := InfinitePlaces(F);
    eps1 := Evaluate(eps, places[1]);
    if eps1 gt 1 then
      // eps1*eps2 = Nm(eps) = 1
      eps := 1/eps;
    end if;
    eps := Integers(F)!eps;
    F`FundamentalUnitSquare := eps;
  end if;
  return F`FundamentalUnitSquare;
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

/////////////////////// DistinguishedPlace and strong coercion ///////////////////////////

intrinsic DistinguishedPlace(K::FldNum) -> PlcNumElt
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
  if assigned K`DistinguishedPlace then
    return K`DistinguishedPlace;
  end if;
  K`DistinguishedPlace := InfinitePlaces(K)[1];
  return K`DistinguishedPlace;
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

  CC_THRESHOLD := 10^-10;
  require Type(x) in [FldNumElt, FldRatElt, FldQuadElt, FldCycElt] : "%o is not a valid type for strong coercion", Type(x);

  K := Parent(x);

  // If K = QQ then all embeddings are the same,
  // We do this case separately because Rationals() 
  // does not have an Extensions attribute.
  if K eq Rationals() then
    return L!x;
  end if;

  // If L = QQ then all restrictions are the same.
  if L eq Rationals() then
    return Rationals()!x;
  end if;

  if not assigned K`Extensions then
    K`Extensions := AssociativeArray(PowerStructure(FldNum));
  end if;
  if not assigned K`Restrictions then
    K`Restrictions := AssociativeArray(PowerStructure(FldNum));
  end if;

  require IsNormal(K) and IsNormal(L) : "Strong coercion is not yet implemented\
      for non-Galois fields";

  // if K = QQ then all embeddings are the same
  if K eq Rationals() then
    K`Extensions[L] := Automorphisms(Rationals())[1];
  end if;

  // if L = QQ then all restrictions are the same
  if L eq Rationals() then
    K`Restrictions[L] := Automorphisms(K)[1];
  end if;

  if IsDefined(K`Extensions, L) then
    phi := K`Extensions[L];
    return L!phi(x);
  elif IsDefined(K`Restrictions, L) then
    phi := K`Restrictions[L];
    return L!phi(x);
  end if;

  v := DistinguishedPlace(K);
  w := DistinguishedPlace(L);

  if IsSubfield(K, L) then
    a := PrimitiveElement(K);
    a_eval := ComplexField()!Evaluate(a, v);
    auts := Automorphisms(K);
    for aut in auts do
      if Abs(ComplexField()!Evaluate(L!aut(a), w) - a_eval) lt CC_THRESHOLD then
        K`Extensions[L] := aut;
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
      if Abs(ComplexField()!Evaluate(L!aut(a), w) - a_eval) lt CC_THRESHOLD then
        K`Restrictions[L] := aut;
        return StrongCoerce(L, x);
      end if;
    end for;
    require 0 eq 1 : "This should not be possible. Something has gone wrong.";
  else
    require 0 eq 1 : "The Parent of K neither contains nor is contained in L";
  end if;
end intrinsic;

intrinsic StrongMultiply(K::Fld, A::List) -> FldElt
  {
    input:
      K - A field of type FldRat, FldCyc, FldNum, or FldQuad
      A - A list of elements (strong) coercible into K, not necessarily
        from the same parent field.
    returns:
      The product of the elements in A, as an element of K.
  }

  // perform normal multiplication if all the objects 
  // are of the same type
  if &and[Parent(x) cmpeq Parent(A[1]) : x in A] then
    return &*[x : x in A];
  end if;
      
  prod := K!1;
  for x in A do
    y := (Type(x) in [FldRatElt, RngIntElt]) select x else StrongCoerce(K, x);
    prod *:= y;
  end for;
  return prod;
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
  if #SequenceToSet(k) eq 1 then
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

intrinsic AutsReppingEmbeddingsOfF(F::FldNum, k::SeqEnum[RngIntElt] : Precision := 50) -> SeqEnum[Map]
  { 
    inputs:
      F: A totally real Galois number field of degree n
      k: A weight, given as a SeqEnum of n natural numbers
    returns:
      Let K be UnitCharField, and v_0 a distinguished real
      place of K (we choose the first one, but this is arbitrary).

      We return a list [sigma_1, ..., sigma_n] 
      of automorphisms of K sorted such that if 
      [v_1, ..., v_n] is a list of real embeddings of F, 
      then v_i(x) = v_0(sigma_i(x)) for all x in F. 
      Note that when F is not Galois, this list is
      not unique, but our algorithm is deterministic.
  }
  K := UnitCharField(F, k);
  n := Degree(F);
  places := RealPlaces(F);

  a := PrimitiveElement(F);
  a_embed_dict := AssociativeArray();
  for i in [1 .. n] do
    a_embed_dict[RealField(Precision)!Evaluate(a, places[i])] := i;
  end for;

  // a distinguished place of K 
  // if we want to view our HMFs as having coefficients over C,
  // we should apply v_0 to all the coefficients
  v_0 := DistinguishedPlace(K);
  
  aut_dict := AssociativeArray();

  // auts is the automorphisms of K
  for aut in Automorphisms(K) do
    aut_a_est := RealField(Precision)!Evaluate(aut(a), v_0);
    b, x := IsDefined(a_embed_dict, aut_a_est);
    if b then
      aut_dict[x] := aut;
      Remove(~a_embed_dict, aut_a_est);
      if #a_embed_dict eq 0 then
        break aut;
      end if;
    end if;
  end for;
  return [aut_dict[i] : i in [1 .. n]];
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

  auts := AutsReppingEmbeddingsOfF(F, k);
  if IsParitious(k) then
    // paritious nonparallel weight
    return &*[auts[i](K!x)^(ExactQuotient(k0 - k[i], 2)) : i in [1 .. #auts]];
  else
    // nonparitious weight
    v_0 := DistinguishedPlace(K);
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
  v_0 := DistinguishedPlace(K);
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
