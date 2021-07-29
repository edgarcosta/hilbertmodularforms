// save fundamental unit
declare attributes FldAlg:
  FundamentalUnitTotPos,
  FundamentalUnitTotMap
  ;



/////////////////////// Totally positive associate /////////////////

intrinsic Signature(a::RngOrdElt) -> SeqEnum
  {}
  R := Parent(a);
  return Signature(FieldOfFractions(R)!a);
end intrinsic;

intrinsic TotallyPositiveUnits(F::FldAlg) -> GrbAb, Map
  {return the group of totally positive units of the base as an abstract group and the map from abstract totally positive unit group into F^\times_{>0}}
  if not is assigned F`FundamentalUnitTotPos then
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
    F`FundamentalUnitTotPos := K;
    F`FundamentalUnitTotMap := mp;
  end if;
    return F`FundamentalUnitTotPos, F`FundamentalUnitTotMap;
end intrinsic;
