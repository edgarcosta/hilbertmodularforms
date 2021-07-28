/*****
ModFrmHilDElt
*****/

////////// ModFrmHilDEltComp attributes //////////

declare type ModFrmHilDEltComp;
declare attributes ModFrmHilDEltComp:
  Parent, // ModFrmHilD
  Precision, // RngIntElt
  Coefficients, // Assoc:  coeffs_bb[nu] := a_(bb,nu) = a_(nu bb'^-1), where nu in Shintani cone
  BaseRing, // Rng: where the coefficients live (does this depend on bb?)
  UnitChar, // Hom: TotallyPositiveUnitGroup(Parent(Parent)) -> BaseRing
  ComponentIdeal; // RngOrdIdl, representative of the narrow class element

declare type ModFrmHilDElt;
declare attributes ModFrmHilDElt:
  Parent,
  Components; // Assoc: bb --> f_bb, each f_bb of type ModFrmHilDEltComp



////////// ModFrmHilDEltComp fundamental intrinsics //////////

intrinsic Print(f::ModFrmHilDEltComp, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    k := Weight(Mk);
    working_prec := Precision(f);
    coeffs := Coefficients(f);
    N := Level(Mk);
    if level ne "Minimal" then
      printf "Component of Hilbert modular form expansion with precision %o.\n", working_prec;
      printf "Parent: %o\n", Mk;
    end if;
    bb := ComponentIdeal(f);
    printf "Coefficients for component ideal class bb = %o\n", bb;
    coeffs_bb := Coefficients(f);
    printf "\n\t(Trace, nu)  |--->   a_nu";
    count := 0;
    for nu in ShintaniReps(M)[bb] do
      t := Trace(nu);
      printf "\n\t(%o, %o)  |--->   %o", t,  nu, coeffs[nu];
      count +:= 1;
      if count ge num_coeffs then
        printf "\n...";
        break;
      end if;
    end for;
    printf "\n\n";
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic Print(f::ModFrmHilDElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    bbs := NarrowClassGroupReps(M);
    k := Weight(Mk);
    N := Level(Mk);
    if level ne "Minimal" then
      printf "Hilbert modular form expansion: ";
      printf "Parent: %o\n", Mk;
    end if;
    for bb in bbs do
      Print(Components(f)[bb], level  : num_coeffs := num_coeffs);
    end for;
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;


////////// ModFrmHilDElt and ModFrmHilDEltComp access to attributes //////////

intrinsic Parent(f::ModFrmHilDEltComp) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Precision(f::ModFrmHilDEltComp) -> RngIntElt
  {}
  return f`Precision;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic Weight(f::ModFrmHilDEltComp) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic GradedRing(f::ModFrmHilDElt) -> ModFrmHilDGRng
  {return parent of parent of f}
  Mk := Parent(f);
  return Parent(Mk);
end intrinsic;

intrinsic UnitChar(f::ModFrmHilDEltComp) -> Map
  {return the unit character of f}
  return f`UnitChar;
end intrinsic;


intrinsic Field(f::ModFrmHilDEltComp) -> FldNum
  {return base field of parent of f.}
  return GradedRing(f)`Field;
end intrinsic;

intrinsic Field(f::ModFrmHilDElt) -> FldNum
  {return base field of parent of f.}
  return GradedRing(f)`Field;
end intrinsic;

intrinsic Level(f::ModFrmHilDEltComp) -> RngOrdIdl
  {return level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {return level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic ComponentIdeal(f::ModFrmHilDEltComp) -> RngOrdIdl
  {return the component of f}
  return f`ComponentIdeal;
end intrinsic;

intrinsic Components(f::ModFrmHilDElt) -> Assoc
  {return the components of f}
  return f`Components;
end intrinsic;

intrinsic MPairs(f::ModFrmHilDElt) -> RngOrdIdl
  {returns the MPairs of parent of f.}
  return MPairs(GradedRing(f));
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, bb::RngOrdIdl, nu::RngElt) -> Any
  {}
  return Coefficients(Components(f)[bb])[nu];
end intrinsic;


intrinsic Coefficient(f::ModFrmHilDEltComp, nu::RngElt) -> Any
  {}
  return Coefficients(f)[nu];
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDEltComp) -> Any
  {}
  return f`Coefficients;
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> Any
  {}

  coeffs := AssociativeArray();
  for bb in Keys(Components(f)) do
    coeffs[bb] := Coefficients(Components(f)[bb]);
  end for;
  return coeffs;
end intrinsic;

intrinsic CoefficientField(f::ModFrmHilDElt) -> Any
  {}
  print("Elements.m CoefficientField: DEPRECATED, use BaseRing");
  return BaseRing(f);
end intrinsic;

intrinsic BaseRing(f::ModFrmHilDEltComp) -> Any
  {}
  return f`BaseRing;
end intrinsic;

intrinsic BaseRing(f::ModFrmHilDElt) -> Any
  {}

  ZF := Integers(GradedRing(f));
  R := BaseRing(Components(f)[1*ZF]);
  for fbb in Components(f) do
    require BaseRing(fbb) eq R : "Need all base rings of all components to be equal";
  end for;
  return R;
end intrinsic;

intrinsic NumberOfCoefficients(f::ModFrmHilDElt) -> Any
{}
//TODO: What is the point of this?
    keys := SetToSequence(Keys(Coefficients(f)));
    if IsNull(keys) then return 0;
    end if;
    coeffsperkey := #Keys(Coefficients(f)[keys[1]]);
    return #keys*coeffsperkey;
end intrinsic;


////////// ModFrmHilDElt and ModFrmHilDEltComp creation functions //////////


intrinsic ModFrmHilDEltCompInitialize() -> ModFrmHilDElt
  {Create an empty ModFrmHilDEltComp object.}
  f := New(ModFrmHilDEltComp);
  return f;
end intrinsic;

intrinsic ModFrmHilDEltInitialize() -> ModFrmHilDElt
  {Create an empty ModFrmHilDElt object.}
  f := New(ModFrmHilDElt);
  return f;
end intrinsic;

intrinsic ModFrmHilDEltCompCopy(f::ModFrmHilDEltComp) -> ModFrmHilDElt
  {new instance of ModFrmHilDEltComp.}
  g := ModFrmHilDEltCompInitialize();
  for attr in GetAttributes(Type(f)) do
    if assigned f``attr then
      g``attr := f``attr;
    end if;
  end for;
  return g;
end intrinsic;

intrinsic ModFrmHilDEltCopy(f::ModFrmHilDElt) -> ModFrmHilDElt
  {new instance of ModFrmHilDElt.}
  g := ModFrmHilDEltInitialize();
  for attr in GetAttributes(Type(f)) do
    if assigned f``attr then
      g``attr := f``attr;
    end if;
  end for;
  return g;
end intrinsic;


//FIXME: change this to EmbeddComponent?
// ModFrmHilDEltComp -> ModFrmHilDElt
intrinsic CompleteCoeffsZeros(M::ModFrmHilDGRng, coeffs::Assoc) -> Assoc
 {given an associative array with coefficients on one component, set all other coefficients to be zero}
 print("DEPRECATED: first create the f an ModFrmHilDEltComp and then HMF(f) to get a ModFrmHilDElt");
  reps:= NarrowClassGroupReps(M);
  for bb in reps do
    if not bb in Keys(coeffs) then
      coeffs[bb] := AssociativeArray();
      for nn in IdealsByNarrowClassGroup(M)[bb] do
        coeffs[bb][nn] := 0;
      end for;
    end if;
  end for;
  return coeffs;
end intrinsic;

intrinsic HMFComp(Mk::ModFrmHilD,
                  bb::RngOrdIdl,
                  coeffs::Assoc
                  :
                  unitchar:=[],
                  CoeffsByIdeal:=false,
                  prec := 0) -> ModFrmHilDEltComp
  {
    Return the ModFrmHilDEltComp with parent Mk, component ideal bb, the fourier coefficients
    in the Shintani cone, and unit character.
    Explicitly, coeffs is an associative array where
    coeffs[nu] = a_(bb, nu) = a_nn
        where nn = nu*(bb')^-1 and bb' = bb^(-1)*dd_F
    for all nu in the Shintani cone, unless CoeffsByIdeal is true
    (to allow backwards compatibility), in which case
    coeffs[nn] = a_nn as above (and we assign according to Shintani rep).
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  CoefficientSequence := []; // to assert all coefficients have the same parent
  require bb in bbs: "bb should be among the chosen representatives of the narrow class group";

  // make the HMF
  f := ModFrmHilDEltCompInitialize();

  if prec eq 0 then
    f`Precision := Precision(M);
  else
    assert prec gt 0;
    f`Precision := prec;
  end if;

  f`Parent := Mk;
  f`ComponentIdeal := bb;

  if CoeffsByIdeal then
    // first convert according to
    //   nn = nu*(bb')^-1 where bb' = dd_F*bb^(-1)
    idlEltPairs := IdealElementPairs(M);
        // consists of a sequence of [* nn, nu *]
    coeffsnu := AssociativeArray();
    for pair in IdealElementPairs(M)[bb] do
      coeffsnu[pair[2]] := coeffs[pair[1]];
    end for;

    coeffs := coeffsnu;  // goodbye old data!
  end if;

  newcoeffs := AssociativeArray();
  for nu in ShintaniRepsUpToTrace(M, bb, f`Precision) do
    require IsDefined(coeffs, nu): "Coefficients should be defined for each representative in the Shintani cone";
    Append(~CoefficientSequence, coeffs[nu]); // if value of coeffs[nu] differs then error here trying to append
    newcoeffs[nu] := coeffs[nu];
  end for;

  f`Coefficients := newcoeffs;
  R := Parent(CoefficientSequence[1]);
  f`BaseRing := R;
  A := TotallyPositiveUnitGroup(M);
  if Type(unitchar) eq Map then
    f`UnitChar := unitchar;
  else
    if IsZero(unitchar) then // IsZero([]) is true
      unitchar := [1 : i in Generators(A)];
    end if;
    f`UnitChar := map<A -> R | a :-> &*[unitchar[i]^a[i] : i in [1..#unitchar]]>;
  end if;
  return f;
end intrinsic;


intrinsic HMFSumComponents(Mk::ModFrmHilD, components::Assoc) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk and Components components.
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(components) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";
  // make the HMF
  f := ModFrmHilDEltInitialize();
  f`Parent := Mk;
  f`Components := AssociativeArray();
  for bb in bbs do
    f_bb := components[bb];
    require ComponentIdeal(f_bb) eq bb: "Components mismatch";
    require Type(f_bb) eq ModFrmHilDEltComp: "The values of components need to be ModFrmHilDEltComp";
    require Mk eq Parent(f_bb): "The parents of the components should be all the same";
    f`Components[bb] := ModFrmHilDEltCompCopy(f_bb);
  end for;
  return f;
end intrinsic;


intrinsic HMF(Mk::ModFrmHilD,
              coeffs::Assoc
              :
              unitchar := [],
              CoeffsByIdeal:=false,
              prec := 0
              ) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk, with the fourier coefficients given via a
    a double associative array coeffs
    and the unit characters are also given via an associative array indexed on the
    narrow class group representatives.
    Explicitly, coeffs is an double associative array
    coeffs[bb][nu] = a_(bb, nu) = a_(nu)*(bb')^-1
    for all nu in the Shintani cone.
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(coeffs) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";
  // make the HMF
  f := ModFrmHilDEltInitialize();
  f`Parent := Mk;
  f`Components := AssociativeArray();
  if Type(unitchar) ne Assoc then
    require unitchar eq []: "unitchar must be an associative array indexed over by representatives of Narrow class group";
    unitchar := AssociativeArray();
    for bb in bbs do
      unitchar[bb] := [1 : i in Generators(TotallyPositiveUnitGroup(M))];
    end for;
  end if;
  require Keys(unitchar) eq SequenceToSet(bbs): "Unit character array should be indexed by representatives of Narrow class group";
  for bb in bbs do
  f`Components[bb] := HMFComp(Mk, bb, coeffs[bb]: unitchar:=unitchar[bb], CoeffsByIdeal:=CoeffsByIdeal, prec:=prec);
  end for;
  return f;
end intrinsic;

intrinsic HMF(fbb::ModFrmHilDEltComp) -> ModFrmHilDElt
  {f = fbb}
  f := HMFZero(Parent(fbb));
  f`Components[ComponentIdeal(fbb)] := ModFrmHilDEltCompCopy(fbb);
  return f;
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD, bb::RngOrdIdl) -> ModFrmHilDEltComp
  {create zero ModFrmHilDEltComp of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for nu in ShintaniRepsUpToTrace(M)[bb] do
    coeffs[nu] := 0;
  end for;
  return HMF(Mk, bb, coeffs);
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := HMFZero(Mk, bb);
  end for;
  return HMFSumComponents(Mk, coeffs);
end intrinsic;

intrinsic IsZero(f::ModFrmHilDEltComp) -> BoolElt
  {check if form is identically zero}
  return IsZero([c : c in Coefficients(f)]);
end intrinsic;

intrinsic IsZero(f::ModFrmHilDElt) -> BoolElt
  {check if form is identically zero}
  return &and[IsZero(Components(f)[bb]) : bb in Keys(Components(f))];
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD, bb::RngIdl) -> ModFrmHilDEltComp
  {create one ModHilFrmDElt of weight zero.}
  M := Parent(Mk); chi := Character(Mk); N := Level(Mk); k := [0 : i in Weight(Mk)];
  M0 := HMFSpace(M, N, k, chi);
  coeffs := AssociativeArray();
  for nu in ShintaniReps(M)[bb] do
    if IsZero(nu) then
      coeffs[nu] := 1;
    else
      coeffs[nu] := 0;
    end if;
  end for;
  return HMFComp(Mk, bb, coeffs);
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD) -> ModFrmHilDElt
  {create one ModHilFrmDElt of weight zero.}
  M := Parent(Mk);
  C := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    C[bb] := HMFIdentity(Mk, bb);
  end for;
  return HMFSumComponents(Mk, C);
end intrinsic;


////////////// ModFrmHilDElt: Coercion /////////////////////////

// Coerces HMF coefficients a_n in a ring R
intrinsic ChangeBaseRing(R::Rng, f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {returns f such that a_nu := R!a_nu}
  bb := ComponentIdeal(f);
  coeffs := Coefficients(f);
  new_coeffs := AssociativeArray(Universe(coeffs));
  for nn in Keys(coeffs) do
    new_coeffs[nn] := R!coeffs[nn];
  end for;
  return HMFComp(Parent(f), new_coeffs: unitchar:= UnitChar(f), prec := Precision(f));
end intrinsic;


intrinsic ChangeBaseRing(R::Rng, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f such that a_nu := R!a_nu}
  M := GradedRing(f);
  bbs := NarrowClassGroupReps(M);
  // first make a copy
  f := ModFrmHilDEltCopy(f);
  // then change ring
  components := Components(f);
  for bb in components do
    components[bb] := ChangeBaseRing(components[bb]);
  end for;
  return f;
end intrinsic;

intrinsic IsCoercible(Mk::ModFrmHilD, f::.) -> BoolElt, .
  {}

  print "Checking coercibility of", Mk, f;

  if Type(f) notin [ModFrmHilDElt, ModFrmHilDEltComp] then
    return false, "f not of type ModFrmHilDElt or ModFrmHilDEltComp";
  else // f is an HMF so has a chance to be coercible
    M := Parent(Mk); // graded ring associated to Mk
    Mkf := Parent(f); // space of HMFs associated to f
    Mf := Parent(Mkf); // graded ring associated to f
    if M ne Mf then
      return false, "f does not belong to the same graded ring as Mk";
    else // at least the graded rings match up
      test1 := Weight(Mk) eq Weight(Mkf);
      test2 := Level(Mk) eq Level(Mkf);
      test3 := Character(Mk) eq Character(Mkf);
      if test1 and test2 and test3 then // all tests must be true to coerce
        if Type(f) eq ModFrmHilDEltComp then
          A := TotallyPositiveUnitGroup(M);
          return true, HMFComp(Mk, Coefficients(f): unitchar:=UnitChar(f), prec:=Precision(f));
        end if;
        components := AssociativeArray();
        for bb in Keys(Components(f)) do
          fbb := Components(f)[bb];
          components[bb] := HMFComp(Mk, bb, Coefficients(fbb): unitchar:=UnitChar(fbb), prec:=Precision(fbb));
        end for;
        return true, HMFSumComponents(Mk, components);
      else
        return false, "I tried and failed to coerce";
      end if;
    end if;
  end if;
end intrinsic;

/* Why do we need this?
intrinsic '!'(Mk::ModFrmHilD, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f with parent M}
  return HMF(Mk, Components(f));
end intrinsic;
*/

intrinsic 'in'(x::., y::ModFrmHilDElt) -> BoolElt
  {}
  return false;
end intrinsic;

intrinsic IsCoercible(x::ModFrmHilDElt, y::.) -> BoolElt, .
  {}
  return false;
end intrinsic;
//TODO:
// make a function ModFrmHilDEltComp -> ModFrmHilDElt

//////////  ModFrmHilDElt: Galois action on Coefficients //////////

//TODO:
//Tests:
// - Apply Hecke on a Galois Orbit, and see that it doesn't move
// - Apply Hecke to a Eisensten series, and check that is a multiple
// - Apply Hecke to a Theta series, and see if we get the whole space
intrinsic MapCoefficients(m::Map, f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return the ModFrmHilDEltComp where the map acts on the coefficients}
  coeffs := Coefficients(f);
  new_coeffs := AssociativeArray();
  for nu in Keys(coeffs) do
    new_coeffs[nu] := m(coeffs[nu]);
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), new_coeffs : unitchar:=UnitChar(f), prec:=Precision(f));
end intrinsic;

intrinsic MapCoefficients(m::Map, f::ModFrmHilDElt) -> ModFrmHilDElt
  {return the ModFrmHilDElt where the map acts on the coefficients}
  components := Components(f);
  for bb in Keys(components) do
    components[bb] := MapCoefficients(m, components[bb]);
  end for;
  return HMFSumComponents(Parent(f), components);
end intrinsic;

intrinsic GaloisOrbit(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form}
  k := Weight(f);
  M := GradedRing(f);
  R := BaseRing(f);
  if IsField(R) then
    K := R;
  else
    K := NumberField(R);
    f := K!f; // HERE
  end if;
  G, Pmap, Gmap := AutomorphismGroup(K);
  result := [];
  for g in G do
    if K eq R then
      Append(~result, MapCoefficients(Gmap(g), f));
    else
      Append(~result, ChangeBaseRing(R, MapCoefficients(Gmap(g), f)));
    end if;
  end for;
  return result;
end intrinsic;


intrinsic Trace(f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return Trace(f)}
  new_coeffs := AssociativeArray();
  coeffs := Coefficients(f);
  for nu in Keys(Coefficients(f)) do
    new_coeffs[nu] := Trace(coeffs[nu]);
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), coeffs: unitchar:=UnitChar(f), prec:=Precision(f));
end intrinsic;

intrinsic Trace(f::ModFrmHilDElt) -> ModFrmHilDElt
  {return Trace(f)}
  C := Components(f);
  nC := AssociativeArray();
  for bb in Keys(C) do
    nC[bb] := Trace(C[bb]);
  end for;
  return HMFSumComponents(Parent(f), nC);
end intrinsic;


intrinsic GaloisOrbitDescent(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form over Q}

  result := [Parent(f) | ];
  for b in Basis(BaseRing(f)) do
    Append(~result, Trace(b * f));
  end for;
  return result;
end intrinsic;



////////// ModFrmHilDElt: Arithmetic //////////

//TODO make zero HMF universal so it can be added/multiplied to any HMF
//ask JV

intrinsic 'eq'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> BoolElt
{compares Parent, Weight, Component, Precision, UnitChar, and Coefficients.}
  if not &and[a(f) eq a(g): a in [Parent, Component, UnitChar, Precision]] then
    return false;
  end if;
  if Keys(Coefficients(f)) ne Keys(Coefficients(g)) then
    return false;
  end if;
  for nu in Keys(Coefficients(f)) do
   if Coefficients(f)[nu] ne Coefficients(g)[nu] then
     return false;
   end if;
  end for;
  return true;
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
{compares Parent and Components.}
  return &and[a(f) eq a(g): a in [Parent, Components]];
end intrinsic;

intrinsic '*'(c::Any, f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {scale f by a scalar c.}
  require IsCoercible(BaseRing(f), c): "the scalar must be coercible into the base ring";
  F := BaseRing(f);
  new_coeffs := AssociativeArray();
  coeffs := Coefficients(f);
  for nu in Keys(coeffs) do
    coeffs[nu] := F!(c * coeffs[nu]);
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), coeffs: unitchar:=UnitChar(f), prec:=Precision(f));
end intrinsic;

intrinsic '*'(f::ModFrmHilDEltComp, c::Any) -> ModFrmHilDEltComp
  {scale f by scalar c.}
  return c*f;
end intrinsic;

intrinsic '*'(c::Any, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by scalar c.}
  new_comp := AssociativeArray();
  comp := Components(f);
  for bb in Keys(comp) do
    new_comp[bb] := c * comp[bb];
  end for;
  return HMFSumComponents(Parent(f), new_comp);
end intrinsic;

intrinsic '*'(f::ModFrmHilDElt, c::Any) -> ModFrmHilDElt
  {scale f by scalar c.}
  return c*f;
end intrinsic;

intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g.}
  // Currently returns the lowest precision of the forms
  assert Parent(f) eq Parent(g);
  Mk := Parent(f);
  M := Parent(Mk);
  assert GradedRing(g) eq M;
  k := Weight(f);
  new_coeffs := AssociativeArray();
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
    new_coeffs[bb] := AssociativeArray();
    New_keys := Keys(Coefficients(f)[bb]) meet Keys(Coefficients(g)[bb]); // Adding drops the precision to the intersection of the precision of the forms
    for nn in New_keys do
      new_coeffs[bb][nn] := Coefficients(f)[bb][nn] + Coefficients(g)[bb][nn];
    end for;
  end for;
  // update precision to be the minimum of the two precisions?
  prec_f := Precision(f);
  prec_g := Precision(g);
  return HMFSumComponents(Mk, new_coeffs : prec := Minimum(prec_f, prec_g));
end intrinsic;

intrinsic '-'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f-g.}
  return f + (-1)*g;
end intrinsic;

intrinsic '*'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return f*g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  require ComponentIdeal(f) eq ComponentIdeal(g): "we only support multiplication with the same component";

  char_f := UnitChar(f);
  char_g := UnitChar(g);

  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  coeffs_h := AssociativeArray(); // h := f*g
  // Compute the new BaseRing
  Ff := BaseRing(f);
  Fg := BaseRing(g);
  if Ff eq Fg then
    F := Ff;
  else
    F := Compositum(NumberField(Ff), NumberField(Fg));
  end if;
  table := MPairs(f)[ComponentIdeal(f)];

  // TODO: improve precision?
  // use relative precision to gain something here instead of minimum?
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Minimum(prec_f, prec_g);

  for nu in ShintaniRepsUpToTrace(GradedRing(f), ComponentIdeal(f), prec) do
    c := F!0;
    for pair in table[nu] do // [[<s(mu1), epsilon1>, <s(mu2), epsilon2>] :  mu = epsilon s(mu), mu' = epsilon' s(mu'), mu + mu' = nu]
      xpair, ypair := Explode(pair); // pair := [<s(mu1), epsilon1>, <s(mu2), epsilon2>]
      smu1, epsilon1 := Explode(xpair); // <s(mu1), epsilon1>
      smu2, epsilon2 := Explode(ypair); // <s(mu2), epsilon2>
      c +:= F!char_f(epsilon1) * F!coeffs_f[smu1] *  F!char_f(epsilon2) * F!coeffs_g[smu2];
    end for;
    coeffs_h[nu] := c;
  end for;
  A := Domain(char_f);
  unitchar := [char_f(A.i)*char_g(A.i) : i in [1..Generators(A)]];
  Space := HMFSpace(GradedRing(f),
                    Level(f),
                    [Weight(f)[i] + Weight(g)[i] : i in [1..#Weight(f)] ],
                    Character(f)*Character(g));
  return HMFComp(Space, ComponentIdeal(f), coeffs_h : unitchar:=unitchar, prec:=prec);
end intrinsic;

intrinsic '*'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f*g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  comp_f := Components(f);
  comp_g := Components(g);
  comp := AssociativeArray();
  for bb in Keys(comp_f) do
    comp[bb] := comp_f[bb] * comp_g[bb];
  end for;
  Space := HMFSpace(GradedRing(f),
                    Level(f),
                    [Weight(f)[i] + Weight(g)[i] : i in [1..#Weight(f)]],
                    Character(f)*Character(g));
  return HMFSumComponents(Space, comp);
end intrinsic;


intrinsic '/'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return f/g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support division inside the same graded ring";
  require Level(f) eq Level(g): "we only support division with the same level";
  require ComponentIdeal(f) eq ComponentIdeal(g): "we only support division with the same component";

  char_f := UnitChar(f);
  char_g := UnitChar(g);

  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  coeffs_h := AssociativeArray(); // h := f/g
  // Compute the new BaseRing
  Ff := BaseRing(f);
  Fg := BaseRing(g);
  if Ff eq Fg then
    F := Ff;
    if not IsField(F) and not IsInvertible(coeffs_g)[0] then
      F := NumberField(F);
    end if;
  else
    F := Compositum(NumberField(Ff), NumberField(Fg));
  end if;
  table := MPairs(f)[ComponentIdeal(f)];

  // TODO: improve precision?
  // use relative precision to gain something here instead of minimum?
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Minimum(prec_f, prec_g);

  for nu in ShintaniRepsUpToTrace(GradedRing(f), ComponentIdeal(f), prec)  do
    sum := F!0; // will record sum_{mu + mu' = nu, mu != 0} a(g)_mu a(h)_mu'
    count := 0;
    for pair in table[nu] do // [[<s(mu1), epsilon1>, <s(mu2), epsilon2>] :  mu = epsilon s(mu), mu' = epsilon' s(mu'), mu + mu' = nu]
      xpair, ypair := Explode(pair); // pair := [<s(mu1), epsilon1>, <s(mu2), epsilon2>]
      smu1, epsilon1 := Explode(xpair); // <s(mu1), epsilon1>
      smu2, epsilon2 := Explode(ypair); // <s(mu2), epsilon2>
      if IsZero(smu1) then // smu1 = 0 => => mu1 = 0 => s(mu2) = mu2 = nu
        //FIXME: these asserts should be moved to the creation of MPairs
        assert smu2 eq nu;
        assert IsOne(epsilon1);
        assert IsOne(epsilon2);
        count +:= 1;
      else
        sum +:= F!char_f(epsilon1) * F!coeffs_g[smu1] *  F!char_f(epsilon2) * F!coeffs_h[smu2];
      end if;
    end for;
    //FIXME: this asserts should be moved to the creation of MPairs
    assert count eq 1;
    coeffs_h[nu] := (F!coeffs_f[nu] - sum)/F!coeffs_g[0];
  end for;


  A := Domain(char_f);
  unitchar := [char_f(A.i)/char_g(A.i) : i in [1..Generators(A)]];
  Space := HMFSpace(GradedRing(f),
                    Level(f),
                    [Weight(f)[i] - Weight(g)[i] : i in [1..#Weight(f)] ],
                    Character(f)/Character(g));
  return HMFComp(Space, ComponentIdeal(f), coeffs_h : unitchar:=unitchar, prec:=prec);
end intrinsic;

intrinsic '/'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f/g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  comp_f := Components(f);
  comp_g := Components(g);
  comp := AssociativeArray();
  for bb in Keys(comp_f) do
    comp[bb] := comp_f[bb] / comp_g[bb];
  end for;
  Space := HMFSpace(GradedRing(f),
                    Level(f),
                    [Weight(f)[i] - Weight(g)[i] : i in [1..#Weight(f)]],
                    Character(f)/Character(g));
  return HMFSumComponents(Space, comp);
end intrinsic;

intrinsic Inverse(f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
 {return 1/f}
 return HMFIdentity(Parent(f), ComponentIdeal(f))/f;
end intrinsic;

intrinsic Inverse(f::ModFrmHilDElt) -> ModFrmHilDElt
 {return 1/f}
 return HMFIdentity(Parent(f))/f;
end intrinsic;


intrinsic '^'(f::ModFrmHilDElt, n::RngIntElt) -> ModFrmHilDElt
  {return f^n}
  if n lt 0 then
    f := Inverse(f);
  end if;
  g := HMFIdentity(Parent(f));
  if n eq 0 then
    return g;
  end if;
  if n eq 1 then
   return f;
   end if;
  while n gt 1 do
    if n mod 2 eq 0 then
      f := f * f;
      n := Integers() ! (n/2);
    else
      g := f * g;
      f := f * f;
      n := Integers() ! ((n - 1)/2);
    end if;
  end while;
  return f * g;
end intrinsic;

////////// ModFrmHilDElt: Linear Algebra  //////////

//TODO add optional flag to limit the number of coefficients
/*
intrinsic CoefficientsMatrix(list::SeqEnum[ModFrmHilDElt]) -> AlgMatElt
  {returns a matrix with the coefficients of each modular form in each row}
  return Matrix( [ Coefficients(elt) : elt in list] );
end intrinsic;
*/


intrinsic LinearDependence(list::SeqEnum[SeqEnum] ) -> SeqEnum[RngIntElt]
  {
    finds a small non-trivial integral linear combination between components of v.
    If none can be found return 0.
  }
  if IsNull(list) then return list; end if;
  M := Matrix( [ elt : elt in list] );
  // in case M is defined over the rationals
  M := ChangeRing(Denominator(M)*M, Integers());
  B := Basis(Kernel(M));
  if #B ne 0 then return [Eltseq(i) : i in Rows(Matrix(LLL(B)))]; else return []; end if;
end intrinsic;

//TODO add optional flag to limit the number of coefficients
//TODO make outputs to be of the same type
//TODO take working precision
intrinsic LinearDependence(List::SeqEnum[ModFrmHilDElt] : IdealClasses := false ) -> SeqEnum[RngIntElt]
  {Finds any linear relations between the forms (returns 0 if none are found).  The optional parameter NarrowIdealClass can be specified to look at a single narrow ideal class }
  M := GradedRing(List[1]);
  // The ideal classes from which we are taking the coefficients.
  if IdealClasses cmpeq false then
    bbs := NarrowClassGroupReps(M); // Default is all ideals classes
  else
    bbs := IdealClasses; // Optionally we may specify a single ideal class
  end if;
  // List of coefficients for the forms
  L := [];
  maxprec:=Min([f`Precision: f in List]);
  // Loop over forms
  for i in List do
    CoefficientsOfForm := [];
    for bb in bbs do
      CoefficientsOfForm cat:= [Coefficients(Components(i)[bb])[nu] : nu in ShintaniRepsUpToTrace(M, bb, maxprec)];
    end for;
    Append(~L, CoefficientsOfForm);
  end for;
  return LinearDependence(L);
end intrinsic;

////////// ModFrmHilDElt: M_k(N1) -> M_k(N2) //////////

intrinsic Inclusion(f::ModFrmHilDEltComp, Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDEltComp]
  {Takes a form f(z) and produces f(mm*z) in Mk (of level NN) with component ideal class [mm*bb]}

  coeff_f := Coefficients(f);
  Mk_f := Parent(f);
  M_f := Parent(Mk_f);
  M := Parent(Mk);
  N1 := Level(Mk_f);
  N2 := Level(Mk);
  ZF := Integers(M);

  require Weight(Mk_f) eq Weight(Mk): "Weight(f) is not equal to Weight(Mk)";
  require N2 subset N1: "Level of f does not divide level of Mk";
  require N2 subset mm: "Ideal does not divide level of Mk";

  coeff := AssociativeArray();
  bb := ComponentIdeal(f);
  mmbb := NarrowClassRepresentative(M,mm*bb);

  mminv := mm^-1;
  idlEltPairs := IdealElementPairs(M)[bb];
  for nn in IdealsByNarrowClassGroup(M)[mmbb] do
    if IsIntegral(nn*mminv) then
      coeff[nn] := coeff_f[IdealToShintaniRepresentative(M, bb, ZF!!(nn*mminv))];
    else
      coeff[nn] := 0;
    end if;
  end for;

  return HMFComp(Mk, mmbb, coeff : CoeffsByIdeals := true, unitchar := UnitChar(f), Precision := Precision(f));
end intrinsic;

intrinsic Inclusion(f::ModFrmHilDElt, Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f(z) and produces f(mm*z) in the space Mk}

  iotamf := AssociativeArray();
  mminv := mm^-1;
  for bb in Keys(Components(f)) do
    iotamf[bb*mminv] := Inclusion(Components(f)[bb], Mk, mm);
  end for;
  return HMFSumComponents(Mk, iotamf);
end intrinsic;

intrinsic Inclusion(f::ModFrmHilDElt, Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f(z) and produces list of all inclusions of f(dd*z) into Mk}
  N1 := Level(Parent(f));
  N2 := Level(Mk);

  IncludedForms := [];
  for dd in Divisors(N2/N1) do
    Append(~IncludedForms, Inclusion(f,Mk,dd));
  end for;
  return IncludedForms;
end intrinsic;

intrinsic TraceBoundInclusion(Mk_f, Mk) -> RngIntElt
  {Gives absolute initial trace precision bound to be able to include f(dd*z) into Mk}
  M:=Parent(Mk);
  F:=BaseField(Mk);
  ZF:=Integers(F);
  N1 := Level(Mk_f);
  N2 := Level(Mk);
  absTraceBound:=Precision(Parent(Mk));
  for dd in Divisors(N2/N1) do
    for nn in AllIdeals(M) do
      if (not nn/dd in AllIdeals(M)) and IsIntegral(nn/dd) then
        nu:=IdealToShintaniRepresentative(M, nn/dd);
        tnu:=Trace(nu);
        if tnu gt absTraceBound then
          absTraceBound:=tnu;
        end if;
      end if;
    end for;
  end for;
  return absTraceBound;
end intrinsic;



/*
    end for;
    for nn in Idealsbb do
      if nn*dd in IdealsRep then
        coeff[Rep][nn*dd] := coeff_f[bb][nn]; // Change non-zero coefficients
      end if;
    end for;
  end for;
*/



/*
//Todo: Verify Correctness. Reference?
intrinsic Inclusion(f::ModFrmHilDElt, Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f of level N1 and produces list of all inclusions of f into the space of level N2}
  coeff_f := Coefficients(f);
  Mk_f := Parent(f);
  M := Parent(Mk_f);
  N1 := Level(Mk_f);
  N2 := Level(Mk);
  require Weight(Mk_f) eq Weight(Mk): "Weight(f) is not equal to Weight(Mk)";
  require N2 subset N1: "Level of f does not divide level of Mk";
  bbs := NarrowClassGroupReps(M);
  mp := NarrowClassGroupMap(M);
  IncludedForms := [];
  for dd in Divisors(N2/N1) do
    if IsTrivial(dd@@mp) then // 1 new form for each divisor dd
      coeff := AssociativeArray(); // 1 new form for each divisor dd
      for bb in bbs do
        coeff[bb] := AssociativeArray();
        // Rep := [rep : rep in bbs | (rep)@@mp eq (bb*dd)@@mp][1]; // Representative for class [ bb*dd ]
        for nn in IdealsByNarrowClassGroup(M)[bb] do
        if nn*dd in Keys(coeff_f[Rep]) then
          coeff[Rep][nn*dd] := coeff_f[bb][nn];
        else
          coeff[Rep][nn*dd] := 0;
        end if;
      end for;
    end for;
    Append(~IncludedForms, HMFSumComponents(Mk, coeff));
  end for;
  return IncludedForms;
end intrinsic;

*/

////////// ModFrmHilDElt: swap map //////////

intrinsic Swap(f::ModFrmHilDElt) -> ModFrmHilDElt
   {given a hilbert modular form f(z_1, z_2), returns the swapped form f(z_2,z_1)}
   Mk := Parent(f);
   M :=Parent(Mk);
   F:=BaseField(M);
   ZF:=Integers(F);
   bbs := NarrowClassGroupReps(M);
   coeff := AssociativeArray();
   for bb in bbs do
    coeff[bb]:=AssociativeArray();
    Ideals := IdealsByNarrowClassGroup(M)[bb];
    for I in Ideals do
      if I eq 0*ZF then
        x:=Coefficients(f)[bb][I];
        else x:=Coefficient(f, Conjugate(I));
        end if;
      coeff[bb][I]:=x;
      end for;
     end for;
   g:=HMFSumComponents(Mk, coeff);
   return g;
 end intrinsic;
