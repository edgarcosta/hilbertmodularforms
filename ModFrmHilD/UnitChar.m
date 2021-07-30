declare type GrpCharUnitTotElt;
declare attributes GrpCharUnitTotElt:
  BaseField,
  trivial,
  cachedvalues,
  vals;

intrinsic Evaluate(omega::GrpCharUnitTotElt, x::RngElt) -> RngElt
  {Evaluate the unit character omega on x, a number field element.}

  F := BaseField(omega);
  if IsOne(omega) then
    return F!1;
  else
    if not IsDefined(omega`cachedvalues, x) then
      U, mU := TotallyPositiveUnits(F);
      vals := omega`vals;
      omega`cachedvalues[x] := &*[vals[i]^a[i] : i in [1..#vals]] where a := Eltseq(x@@mU);
    end if;
    return omega`cachedvalues[x];
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
