declare type GrpCharUnitTotElt;
declare attributes GrpCharUnitTotElt:
  BaseField,
  trivial,
  cachedvalues,
  vals;

intrinsic ValuesOnGens(omega::GrpCharUnitTotElt) -> SeqEnum[RngElt]
  {return values on gens}
  return omega`vals;
end intrinsic;


intrinsic Evaluate(omega::GrpCharUnitTotElt, x::RngElt) -> RngElt
  {Evaluate the unit character omega on x, a number field element.}

  F := BaseField(omega);
  if IsOne(omega) then
    return F!1;
  else
    b, c := IsDefined(omega`cachedvalues, F!x);
    if not b then
      U, mU := TotallyPositiveUnits(F);
      orients := TotallyPositiveUnitsGeneratorsOrients(F);
      vals := omega`vals;
      c := &*[vals[i]^(a[i]*orients[i]) : i in [1..#vals]] where a := Eltseq(U!(x@@mU));
      omega`cachedvalues[F!x] := c;
    end if;
    return c;
  end if;
end intrinsic;

intrinsic 'eq'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Equality test.}

  return omega`vals cmpeq omegap`vals;
end intrinsic;

intrinsic IsOne(omega::GrpCharUnitTotElt) -> BoolElt
  {return if omega is the trivial character}

  return omega`trivial;
end intrinsic;

intrinsic BaseField(omega::GrpCharUnitTotElt) -> FldAlg
  {Return the base field for which the character is on totally
   positive unit group of the ring of integers.}

  return omega`BaseField;
end intrinsic;

intrinsic '*'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Product of two unit characters.}

  require BaseField(omega) eq BaseField(omegap) : "Must have same base field.";
  return UnitCharacter(BaseField(omega), [omega`vals[i]*omegap`vals[i] : i in [1..#omega`vals]]);
end intrinsic;

intrinsic '/'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Quotient of two unit characters.}

  require BaseField(omega) eq BaseField(omegap) : "Must have same base field.";
  return UnitCharacter(BaseField(omega), [omega`vals[i]/omegap`vals[i] : i in [1..#omega`vals]]);
end intrinsic;

intrinsic '^'(omega::GrpCharUnitTotElt, n::RngIntElt) -> BoolElt
  {Power of a unit character.}

  return UnitCharacter(BaseField(omega), [omega`vals[i]^n : i in [1..#omega`vals]]);
end intrinsic;

intrinsic UnitCharacter(F::FldAlg, vals::SeqEnum[RngElt]) -> GrpCharUnitTotElt
  {Create the unit character on the totally positive unit group
   of the ring of integers of F with values on generators specified by vals.}

  omega := New(GrpCharUnitTotElt);
  omega`BaseField := F;
  omega`vals := vals;
  omega`trivial := &and[IsOne(elt) : elt in omega`vals];
  omega`cachedvalues := AssociativeArray();
  return omega;
end intrinsic;


intrinsic TrivialUnitCharacter(F::FldAlg) -> GrpCharUnitTotElt
  {Create the trivial unit character on the totally positive unit group
   of the ring of integers of F.}

 return UnitCharacter(F, [1: i in [1..#Generators(TotallyPositiveUnits(F))]]);
end intrinsic;

intrinsic WeightUnitCharacter(F::FldAlg, k::SeqEnum[RngIntElt]) -> GrpCharUnitTotElt
  {
    input:
      F: A (totally real) number field
      k: A sequence of (positive) integers
    returns:
      The unit character sending eps to 
      \prod_i eps_i^(k_i/2),
      where eps_i is the image of eps under the ith real embedding of F
      and k is the weight associated to Mk. 

      This is the "standard" unit character. It is trivial for parallel weight
      because (\prod_i eps_i)^k = N(eps)^k = 1, but for nonparallel weight
      it will be nontrivial. 
  }

  // if the weight is parallel then the unit character is trivial
  if IsParallel(k) then
    return TrivialUnitCharacter(F);
  end if;

  n := Degree(F);
  places := RealPlaces(F);
  
  vals := [];
  for eps in TotallyPositiveUnitsGenerators(F) do
    // EltToShiftedHalfWeight computes 
    // \prod_i eps_i^((k_0-k_i)/2),
    // where k_0 = Max(k). However, 
    // prod_i eps_i^(k_0/2) = N(eps)^(k_0/2) = 1
    // since we take positive square roots, so 
    // to get the product we want we just need 
    // to invert the output. 
    Append(~vals, EltToShiftedHalfWeight(F!eps, k)^-1);
  end for;
  return UnitCharacter(F, vals);
end intrinsic;

intrinsic Print(omega::GrpCharUnitTotElt, level::MonStgElt)
  {}

  F := BaseField(omega);
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Character of the totally positive unit group of %o", F;
    printf " defined by values %o on generators", ValuesOnGens(omega);
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

