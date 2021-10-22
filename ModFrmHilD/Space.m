/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Parent, // ModFrmHilDGRng
  Weight, // SeqEnum[RngIntElt]
  Level, // RngOrdIdl
  Basis, // = EisensteinBasis cat CuspFormBasis SeqEnum[ModFrmHilDElt]
  EisensteinBasis, // SeqEnum[ModFrmHilDElt]
  CuspFormBasis, // SeqEnum[ModFrmHilDElt]
  Dimension, // RngIntElt
  Character; // GrpHeckeElt, JV: why aren't we using Dirichlet?


////////// ModFrmHilD fundamental intrinsics //////////

intrinsic Print(Mk::ModFrmHilD, level::MonStgElt)
  {}
  M := Parent(Mk);
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Space of Hilbert modular forms over %o\n", BaseField(M);
    printf "Precision: %o\n", Precision(M);
    printf "Weight: %o\n", Weight(Mk);
    printf "Character: %o\n", Character(Mk);
    printf "Level: %o", IdealOneLine(Level(Mk));
  elif level eq "Magma" then
    error "not implemented!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic 'in'(f::., M::ModFrmHilD) -> BoolElt
  {}
  if Type(f) ne ModFrmHilDElt then
    return false, "The first argument should be a ModFrmHilDElt";
  else
    return Parent(f) eq M;
  end if;
end intrinsic;

intrinsic 'eq'(M1::ModFrmHilD, M2::ModFrmHilD) -> BoolElt
  {True iff the two spaces of Hilbert modular forms are identically the same}
return Parent(M1) eq Parent(M2) and Weight(M1) eq Weight(M2) and
Level(M1) eq Level(M2) and Character(M1) eq Character(M2);
end intrinsic;

////////// ModFrmHilD access to attributes //////////

intrinsic Parent(Mk::ModFrmHilD) -> ModFrmHilDGRng
  {}
  return Mk`Parent;
end intrinsic;

intrinsic Weight(Mk::ModFrmHilD) -> SeqEnum[RngIntElt]
  {}
  return Mk`Weight;
end intrinsic;

intrinsic Level(Mk::ModFrmHilD) -> RngOrdIdl
  {}
  return Mk`Level;
end intrinsic;

intrinsic Character(Mk::ModFrmHilD) -> GrpHeckeElt
  {}
  return Mk`Character;
end intrinsic;

intrinsic Dim(Mk::ModFrmHilD) -> RngIntElt
{}
  if not assigned Mk`Dimension then
    ComputeDimension(Mk);
  end if;
  return Mk`Dimension;
end intrinsic;

/* attributes of the parent */

intrinsic BaseField(Mk::ModFrmHilD) -> Any
  {}
  return BaseField(Parent(Mk));
end intrinsic;

intrinsic Integers(Mk::ModFrmHilD) -> Any
  {}
  return Integers(Parent(Mk));
end intrinsic;

////////// ModFrmHilD creation and multiplication functions //////////

intrinsic ModFrmHilDInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilD object.}
  M := New(ModFrmHilD);
  return M;
end intrinsic;

// TODO: some checks here? or leave it up to the user?
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt], chi::GrpHeckeElt) -> ModFrmHilD
  {}
  spaces := Spaces(M);
  if N in Keys(spaces) then
    if <k, chi> in Keys(spaces[N]) then
      return spaces[N][<k, chi>];
    end if;
  end if;
  Mk := ModFrmHilDInitialize();
  Mk`Parent := M;
  Mk`Weight := k;
  Mk`Level := N;
  Mk`Character := chi;
  AddToSpaces(M, Mk, N, k, chi);
  return Mk;
end intrinsic;

// overloaded for trivial level and character
intrinsic HMFSpace(M::ModFrmHilDGRng, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  N := ideal<ZF|1>;
  X := HeckeCharacterGroup(N);
  chi := X!1;
  return HMFSpace(M, N, k, chi);
end intrinsic;

// overloaded for trivial character
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  X := HeckeCharacterGroup(N);
  chi := X!1;
  return HMFSpace(M, N, k, chi);
end intrinsic;

intrinsic ModFrmHilDCopy(Mk::ModFrmHilD) -> ModFrmHilD
  {new instance of ModFrmHilD.}
  M1k := ModFrmHilDInitialize();
  for attr in GetAttributes(Type(Mk)) do
    if assigned Mk``attr then
      M1k``attr := Mk``attr;
    end if;
  end for;
  return M1k;
end intrinsic;


intrinsic NumberOfCusps(Mk::ModFrmHilD) -> RngIntElt
  {Returns the number of cusps for Gamma_0(N)}
  M := Parent(Mk);
  N := Level(Mk);
  ZF := Integers(M);
  U := UnitGroup(M);
  mU := UnitGroupMap(M);
  h := NarrowClassNumber(M);
  require h eq 1: "Not verified for Cl^+(F) > 1";
  // Helper function
  phi_u := function(aa)
    Q, mQ := quo<ZF | aa>;
    U1,mU1 := UnitGroup(Q);
    S := sub<U1 | [(mQ(mU(e)))@@mU1 : e in Generators(U)]>;
    return Integers()!(#U1/#S);
  end function;
  return h*(&+[phi_u(dd + N/dd) : dd in Divisors(N)]);
end intrinsic;



intrinsic Dimension(Mk::ModFrmHilD) -> RngIntElt
  {Returns the number of cusps for Gamma_0(N)}
  M := Parent(Mk);
  ZF := Integers(M);
  k := Weight(Mk);
  if SequenceToSet(k) eq Set([2]) then
    print "Not using trace formula, might be slow (parallel weight 2). Talk to Ben";
    EB := EisensteinBasis(Mk);
    cuspDim := HilbertCuspForms(BaseField(Parent(Mk)),Level(Mk),Weight(Mk));
    dim := #EB + Dimension(cuspDim);
    return dim;
  else
    return NumberOfCusps(Mk) + Trace(Mk,1*ZF);
  end if;
end intrinsic;


// We eventually want to replace this with the Dimension intrinsic (above). However we need to wait for Trace to work.
intrinsic ComputeDimension(Mk::ModFrmHilD)
  {compute the dimension of Mk and store it in Mk}
  // we rely on HilbertCuspForms, which only works for trivial character
  assert Character(Mk) eq HeckeCharacterGroup(Level(Mk))!1;
  EB := EisensteinBasis(Mk);
  cuspDim := HilbertCuspForms(BaseField(Parent(Mk)),Level(Mk),Weight(Mk));
  dim := #EB + Dimension(cuspDim);
  Mk`Dimension := dim;
end intrinsic;
