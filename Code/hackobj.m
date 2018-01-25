declare type HMF;
declare attributes HMF:
  HMFPrecision, // RngIntElt : precision for the expansion
  HMFBaseField, // FldNum : totally real field
  HMFCoefficientRing, // Integers() or RngOrd : Integers of a number field
  HMFCoefficients; // Assoc : all ideals of HMFBaseField with norm less than or equal to HMFPrecision

intrinsic HMFInitialize() -> HMF
  {Create an empty HMF object.}
  s := New(HMV);
  return s;
end intrinsic;

intrinsic HMFCreate(F::FldNum, prec::RngIntElt) -> HMF
  {Generates the zero HMF over F with precision prec.}
  // basic assertions
  assert IsTotallyReal(F);
  assert prec gt 0;
  // initialize the object
  s := HMFInitialize();
  s`HMFBaseField := F;
  s`HMFPrecision := prec;
  s`HMFCoefficientRing := Integers();
  // create associative array called coeffs
  Is := IdealsUpTo(prec, F);
  coeffs := AssociativeArray(); // empty Assoc
  for I in Is do
    coeffs[I] := 0;
  end for;
  s`HMFCoefficients := coeffs;
  return s;
end intrinsic;

// TODO Parent
// TODO IsCoercible

// TODO
intrinsic HMFCopy(f::HMF) -> HMF
  {Copy f}
end intrinsic;

// TODO
intrinsic '*'(c::RngOrdElt, f::HMF) -> HMF
  {scale f by integral element c.}
end intrinsic;

// TODO
intrinsic '*'(c::RngIntElt, f::HMF) -> HMF
  {scale f by integer c.}
  for i in Keys(f`HMFCoefficients) do
    f`HMFCoefficients[i] := c * f`HMFCoefficients[i];
  end for;
  return f;
end intrinsic;

// TODO
intrinsic '+'(f::HMF, g::HMF) -> HMF
  {return f+g}
end intrinsic;

// TODO
intrinsic '*'(f::HMF, g::HMF) -> HMF
  {return f*g}
end intrinsic;

// TODO
intrinsic Print(s::HMF)
  {Print HMF}
  /*
  printf "SolvableDBObject %o:\n", s`SolvableDBName;
  printf "Degree %o\n", s`SolvableDBDegree;
  printf "Genus %o\n", s`SolvableDBGenus;
  printf "%o\n", s`SolvableDBType;
  printf "Galois Orbit Size %o\n", s`SolvableDBGaloisOrbitSize;
  printf "Passport Size %o\n", s`SolvableDBPassportSize;
  printf "Pointed Passport Size %o\n", s`SolvableDBPointedPassportSize;
  printf "Children:\n";
  if assigned s`SolvableDBChildren and #s`SolvableDBChildren gt 0 then
    for i in [1..#s`SolvableDBChildren] do
      printf "  %o\n", s`SolvableDBChildren[i];
    end for;
  else
    printf "  Children not computed yet :(\n";
  end if;
  */
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
