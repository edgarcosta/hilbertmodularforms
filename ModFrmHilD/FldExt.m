// save fundamental unit
declare attributes FldAlg:
  TotallyPositiveUnits,
  TotallyPositiveUnitsMap,
  FundamentalUnitSquare,
  ClassGroupReps,
  TotallyPositiveUnitsGenerators,
  DistinguishedPlace,
  Extensions,
  Restrictions
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

    if not assigned F`TotallyPositiveUnits or not assigned F`TotallyPositiveUnitsMap then
      _ := TotallyPositiveUnits(F);
    end if;

    F`TotallyPositiveUnitsGenerators := [Integers(F)!F`TotallyPositiveUnitsMap(gen) : gen in Generators(F`TotallyPositiveUnits)];
  end if;
  return F`TotallyPositiveUnitsGenerators;
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
