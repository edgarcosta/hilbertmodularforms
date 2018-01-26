declare type HMF;
declare attributes HMF:
  HMFPrecision, // RngIntElt : precision for the expansion
  HMFBaseField, // FldNum : totally real field
  HMFCoefficientRing, // Integers() or RngOrd : Integers of a number field
  HMFCoefficients; // Assoc : all ideals of HMFBaseField with norm less than or equal to HMFPrecision

intrinsic HMFInitialize() -> HMF
  {Create an empty HMF object.}
  f := New(HMV);
  return f;
end intrinsic;

// TODO printing for levels "Default", "Minimal", "Maximal", "Magma"
intrinsic Print(f::HMF) // this is a procedure, so no return
  {Print HMF.}
  printf "Hilbert modular form over %o up to precision %o.\n", f`HMFBaseField, f`HMFPrecision;
end intrinsic;

intrinsic HMFZero(F::FldNum, prec::RngIntElt) -> HMF
  {Generates the zero HMF over F with precision prec.}
  // basic assertions
  assert IsTotallyReal(F);
  assert prec gt 0;
  // initialize the object
  f := HMFInitialize();
  f`HMFBaseField := F;
  f`HMFPrecision := prec;
  f`HMFCoefficientRing := Integers();
  // create associative array called coeffs
  Is := IdealsUpTo(prec, F);
  coeffs := AssociativeArray(); // empty Assoc
  for I in Is do
    coeffs[I] := 0;
  end for;
  f`HMFCoefficients := coeffs;
  return f;
end intrinsic;

intrinsic HMFCopy(f::HMF) -> HMF
  {Copy HMF.}
  F := f`HMFBaseField;
  prec := f`HMFPrecision;
  g := HMFZero(F, prec);
  for attr in GetAttributes(Type(f)) do
    if assigned f``attr then
      g``attr := f``attr;
    end if;
  end for;
  return g;
end intrinsic;

intrinsic '*'(c::RngIntElt, f::HMF) -> HMF
  {scale f by integer c.}
  g := HMFCopy(f); // new instance of f
  for i in Keys(g`HMFCoefficients) do
    g`HMFCoefficients[i] := c * g`HMFCoefficients[i];
  end for;
  return g;
end intrinsic;

// TODO
intrinsic '*'(c::RngOrdElt, f::HMF) -> HMF
  {scale f by integral element c.}
  g := HMFCopy(f); // new instance of f
  for i in Keys(g`HMFCoefficients) do
    g`HMFCoefficients[i] := c * g`HMFCoefficients[i];
  end for;
  return g;
end intrinsic;

/*
// TODO
intrinsic '+'(f::HMF, g::HMF) -> HMF
  {return f+g}
end intrinsic;

// TODO
intrinsic '*'(f::HMF, g::HMF) -> HMF
  {return f*g}
end intrinsic;

// TODO
intrinsic 'eq'(s::HMF, t::HMF) -> BoolElt
  {}
  isSame := true;
  for attr in GetAttributes(Type(s)) do
    if Type(s``attr) ne Type(t``attr) then
      isSame := false;
    elif s``attr ne t``attr then
      isSame := false;
    end if;
  end for;
  return isSame;
end intrinsic;

// TODO Parent?
// TODO IsCoercible?
*/
