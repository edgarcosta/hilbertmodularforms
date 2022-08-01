// save fundamental unit
declare attributes FldAlg:
  TotallyPositiveUnits,
  TotallyPositiveUnitsMap,
  FundamentalUnitSquare,
  ClassGroupReps,
  TotallyPositiveUnitsGenerators
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
