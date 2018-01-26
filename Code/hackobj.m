/*****
BASIC IMPLEMENTATION OF HMF OBJECT
*****/

declare type HMF;
declare attributes HMF:
  HMFPrecision, // RngIntElt : precision for the expansion
  HMFWeights, // SeqEnum[RngIntElt] : a sequence of [HMFBaseField : QQ] integers
  HMFLevel, // RngOrdIdl : ideal of Integers(HMFBaseField)
  HMFBaseField, // FldNum : totally real field
  HMFCoefficientRing, // Integers() or RngOrd : Integers of a number field
  HMFCoefficients; // Assoc : all ideals of HMFBaseField with norm less than or equal to HMFPrecision

intrinsic HMFInitialize() -> HMF
  {Create an empty HMF object.}
  f := New(HMF);
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

// TODO printing for levels "Default", "Minimal", "Maximal", "Magma"
// TODO printing of coefficients?
intrinsic Print(f::HMF) // this is a procedure, so no return
  {Print HMF.}
  printf "Hilbert modular form over %o.\n", f`HMFBaseField;
  printf "Weights: %o\n", f`HMFWeights;
  printf "Level: %o\n", f`HMFLevel;
  printf "Coefficient ring: %o\n", f`HMFCoefficientRing;
  printf "Precision: %o\n", f`HMFPrecision;
end intrinsic;

// TODO
intrinsic HMFIsAdmissibleWeight(F::FldNum, k::SeqEnum[RngIntElt]) -> BoolElt
  {Decide if the sequence of weights k is admissible.}
  return true; // TODO
end intrinsic;

intrinsic HMFZero(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], prec::RngIntElt) -> HMF
  {Generates the zero HMF over F with level N, weights k, with precision prec with integer coefficients.}
  // basic assertions
  assert IsTotallyReal(F);
  assert NumberFiedl(N) eq F;
  assert HMFIsAdmissibleWeight(F, k);
  assert prec gt 0;
  // initialize the object
  f := HMFInitialize();
  f`HMFBaseField := F;
  f`HMFLevel := N;
  f`HMFWeights := k;
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

/*
// TODO
intrinsic HMFZero(F::FldNum, K::FldRat, prec::RngIntElt) -> HMF
  {Generates the zero HMF over F with precision prec with integer coefficients.}
  return HMFZero(F, prec);
end intrinsic;

intrinsic HMFZero(F::FldNum, N::RngOrdIdl, K::FldNum, prec::RngIntElt) -> HMF
  {Generates the zero HMF over F with precision prec with coefficients in ZK.}
  // basic assertions
  assert IsTotallyReal(F);
  assert prec gt 0;
  // initialize the object
  f := HMFInitialize();
  f`HMFBaseField := F;
  f`HMFPrecision := prec;
  f`HMFCoefficientRing := Integers(K);
  ZK := f`HMFCoefficientRing;
  // create associative array called coeffs
  Is := IdealsUpTo(prec, F);
  coeffs := AssociativeArray(); // empty Assoc
  for I in Is do
    coeffs[I] := ZK!0;
  end for;
  f`HMFCoefficients := coeffs;
  return f;
end intrinsic;
*/



// TODO Parent?
// TODO IsCoercible?

/*
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
*/

/*****
ARITHMETIC
*****/

intrinsic '*'(c::RngIntElt, f::HMF) -> HMF
  {scale f by integer c.}
  g := HMFCopy(f); // new instance of f
  coeffs := g`HMFCoefficients;
  for i in Keys(coeffs) do
    coeffs[i] := c * coeffs[i];
  end for;
  return g;
end intrinsic;

intrinsic '*'(c::RngOrdElt, f::HMF) -> HMF
  {scale f by integral element c.}
  ZK := f`HMFCoefficientRing;
  assert Parent(c) eq ZK;
  g := HMFCopy(f); // new instance of f
  coeffs := g`HMFCoefficients;
  for I in Keys(coeffs) do // I an ideal of ZF
    coeffs[I] *:= ZK!(c); // multiplication in ZK, coercion just to be safe
  end for;
  return g;
end intrinsic;

/*
intrinsic '+'(f::HMF, g::HMF) -> HMF
  {return f+g}
  Ff := f`HMFBaseField;
  ZKf := f`HMFCoefficientRing;
  Fg := g`HMFBaseField;
  ZKg := g`HMFCoefficientRing;
  assert Ff eq Fg;
  assert ZKf eq ZKg;
end intrinsic;
*/

/*
// TODO
intrinsic '*'(f::HMF, g::HMF) -> HMF
  {return f*g}
end intrinsic;
*/

/*****
USER CONVENIENCE
*****/
// TODO Coefficients(f)
