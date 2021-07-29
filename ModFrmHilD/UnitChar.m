declare type GrpCharUnitTotElt;
declare attributes GrpCharUnitTotElt:
  BaseField,
  vals;

intrinsic Evaluate(omega::GrpCharUnitTotElt, x::RngElt) -> RngElt
  {Evaluate the unit character omega on x, a number field element.}

  F := BaseField(omega);
  U, mU := TotallyPositiveUnits(F);
  return &*[vals[i]^a[i] : i in [1..#vals]] where a := Eltseq(x@@mU);
end intrinsic;

intrinsic 'eq'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Equality test.}

  return omega`omega`vals cmpeq omegap`vals;
end intrinsic;

intrinsic BaseField(omega::GrpCharUnitTotElt) -> FldAlg
  {Return the base field for which the character is on totally 
   positive unit group of the ring of integers.}

  return omega`BaseField;
end intrinsic;

intrinsic '*'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Product of two unit characters.}

  require BaseField(omega) eq BaseField(omegap) : "Must have same base field.";

  tau := New(GrpCharUnitTotElt);
  tau`BaseField := BaseField(omega); // just checked they were the same
  tau`vals := [omega`vals[i]*omegap`vals[i] : i in [1..#omega`vals]];
  return tau;
end intrinsic;

intrinsic '/'(omega::GrpCharUnitTotElt, omegap::GrpCharUnitTotElt) -> BoolElt
  {Quotient of two unit characters.}

  require BaseField(omega) eq BaseField(omegap) : "Must have same base field.";

  tau := New(GrpCharUnitTotElt);
  tau`BaseField := BaseField(omega); // just checked they were the same
  tau`vals := [omega`vals[i]/omegap`vals[i] : i in [1..#omega`vals]];
  return tau;
end intrinsic;

intrinsic '^'(omega::GrpCharUnitTotElt, n::RngIntElt) -> BoolElt
  {Power of a unit character.}

  tau := New(GrpCharUnitTotElt);
  tau`BaseField := BaseField(omega); 
  tau`vals := [omega`vals[i]^n : i in [1..#omega`vals]];
  return tau;
end intrinsic;

intrinsic UnitCharacter(F::FldAlg, vals::SeqEnum[RngElt]) -> GrpCharUnitTotElt
  {Create the unit character on the totally positive unit group 
   of the ring of integers of F with values on generators specified by vals.}

  omega := New(GrpCharUnitTotElt);
  omega`BaseField := F;
  omega`vals := vals;
  return omega;
end intrinsic;
