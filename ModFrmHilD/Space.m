/*****
ModFrmHilD
*****/

import "../ModFrmHil/copypastefunctions.m" : TopAmbient;
import "../ModFrmHil/diamond.m" : HeckeCharacterSubspace;

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Parent, // ModFrmHilDGRng
  Weight, // SeqEnum[RngIntElt]
  Level, // RngOrdIdl
  Basis, // = EisensteinBasis cat CuspFormBasis SeqEnum[ModFrmHilDElt]
  Character, // GrpHeckeElt, JV: why aren't we using Dirichlet?
  EisensteinBasis, // SeqEnum[ModFrmHilDElt]
  CuspFormBasis, // SeqEnum[ModFrmHilDElt]
  EllipticBasis, // SeqEnum[ModFrmHilDElt]
  Dimension, // RngIntElt
  CuspDimension, //RngIntElt
  EisensteinDimension, //RngIntElt
  EisensteinAdmissableCharacterPairs, // List of pairs of primitive characters
  MagmaSpace, //ModFrmHil
  MagmaNewCuspForms; // SeqEnum[ModFrmHilElt]


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

intrinsic IsCompatibleWeight(chi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> BoolElt, RngIntElt
{Check if the character chi is compatible with the weight k, i.e. the parity
is the same at all infinite places. If it fails, returns the index of the first infinite
place where they do not match.}
  comps := Components(chi);
  level, places := Modulus(chi);
  F := NumberField(Order(level));
  require places eq [1..Degree(F)] : "Chi is not a narrow class group character.";
  require (Degree(F) eq #InfinitePlaces(F)) : "The field is not totally real.";
  for i->v in InfinitePlaces(F) do
    chiv := comps[v];
    if (chiv(-1) ne (-1)^k[i]) then
	return false, i;
    end if;
  end for;
  return true, _;
end intrinsic;

intrinsic IsCompatibleWeight(chi::GrpHeckeElt, k::RngIntElt) -> BoolElt, RngIntElt
{Check if the character chi is compatible with the weight k, i.e. the parity
is the same at all infinite places. If it fails, returns the index of the first infinite
place where they do not match.}
  F := NumberField(Order(Modulus(chi)));
  weight := [k : v in InfinitePlaces(F)];
  is_compat, idx := IsCompatibleWeight(chi, weight);
  if is_compat then return true, _; end if;
  return is_compat, idx;
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
  require Parent(chi) eq HeckeCharacterGroup(N, [1..Degree(BaseField(M))]) : "The parent of chi should be HeckeCharacterGroup(N, [1..Degree(BaseField(M))])";
  is_compat, i := IsCompatibleWeight(chi, k);
  require is_compat : Sprintf("The parity of the character at the infinite place %o doesn not match the parity of the weight", i);
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
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi);
end intrinsic;

// overloaded for trivial character
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
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

// !! TODO - this currently only cuts out the magma space of newforms,
// and throws out the Eisenstein series
// and if there are other properties that we care about.

intrinsic NewSubspace(M::ModFrmHilD, N::RngOrdIdl) -> ModFrmHilD
{Returns the subspace of forms which are N-new.}

  Mk := ModFrmHilDInitialize();
  Mk`Parent := M`Parent;
  Mk`Weight := M`Weight;
  Mk`Level := M`Level;
  Mk`Character := M`Character;
  Mk`MagmaSpace := HeckeCharacterSubspace(NewSubspace(HilbertCuspForms(M), N), M`Character);
  Mk`EisensteinDimension := 0;
  return Mk;
end intrinsic;


intrinsic NumberOfCusps(Mk::ModFrmHilD) -> RngIntElt
  {Returns the number of cusps for Gamma_0(N)}
  // at the moment Corollary 5.1.27 in the paper
  M := Parent(Mk);
  N := Level(Mk);
  ZF := Integers(M);
  U := UnitGroup(M);
  mU := UnitGroupMap(M);
  hplus := NarrowClassNumber(M);
  h := ClassNumber(ZF);
  // Eran: I'm adding in these lines so that we will
  // quotient out by the totally positive units
  gens := [U.i : i in [1..Ngens(U)]];
  // this matrix is the signature of the generators over Z/2Z
  mat := Matrix([[GF(2)!((1-Sign(x)) div 2) : x in RealEmbeddings(mU(u))]
                 : u in gens]);
  // The kernel recovers the subspace of U/U^2 of totally positive units
  ker := Kernel(mat);
  tot_pos := [&+[(Integers()!b[i])*gens[i] : i in [1..#gens]] : b in Basis(ker)];
  assert &and[IsTotallyPositive(mU(u)) : u in tot_pos];
  U_pos := sub<U | tot_pos cat [2*g : g in gens]>;
  // Helper function
  // This is from corollary 5.1.27 in our paper
  // phi is the size of (Z_F / aa)^{\times} modded out by the totally
  // positive units.
  phi_u := function(aa)
    Q, mQ := quo<ZF | aa>;
    U1,mU1 := UnitGroup(Q);
    // This is wrong, we need to divide only by the totally positive ones
    // S := sub<U1 | [(mQ(mU(e)))@@mU1 : e in Generators(U)]>;
    S := sub<U1 | [(mQ(mU(e)))@@mU1 : e in Generators(U_pos)]>;
    return Integers()!(#U1/#S);
  end function;
  return hplus*h*(&+[phi_u(dd + N/dd) : dd in Divisors(N)]);
end intrinsic;

intrinsic HilbertCuspForms(Mk::ModFrmHilD) -> ModFrmHil
  {return the Magma's builtin object}
  if not assigned Mk`MagmaSpace then
    require IsTrivial(DirichletRestriction(Character(Mk))): "Magma's builtin tools only supports characters which restrict to trivial Dirichlet characters.";
    Mk`MagmaSpace := HilbertCuspForms(BaseField(Mk), Level(Mk), Weight(Mk));
    Mk`MagmaSpace := HeckeCharacterSubspace(Mk`MagmaSpace, Character(Mk));
  end if;
  return Mk`MagmaSpace;
end intrinsic;

// TODO: could one implement optional parameters without computing a basis
intrinsic Dimension(Mk::ModFrmHilD) -> RngIntElt
  {return the dimension of Mk}
  if not assigned Mk`Dimension then
    Mk`Dimension := EisensteinDimension(Mk) + CuspDimension(Mk);
  end if;
  return Mk`Dimension;
end intrinsic;

intrinsic Dim(Mk::ModFrmHilD) -> RngIntElt
{}
  return Dimension(Mk);
end intrinsic;

// TODO swap the default
intrinsic CuspDimension(Mk::ModFrmHilD : version:="builtin") -> RngIntElt
  {return dimension of S(Mk)}
  require version in ["builtin", "trace"] : "the options for trace are either \"builtin\" or \"trace formula\"";
  if not assigned Mk`CuspDimension then
    k := Weight(Mk);
    if SequenceToSet(k) eq Set([2]) and version eq "trace" then
      print "Juanita: Not using trace formula, might be slow (parallel weight 2). Talk to Ben";
      version := "builtin";
    end if;

    if version eq "builtin" then
      require IsTrivial(DirichletRestriction(Character(Mk))): "we rely on magma built-in functions, which only works for characters whose associated Dirichlet character is trivial";
      Mk`CuspDimension := Dimension(HilbertCuspForms(Mk));
    else
      M := Parent(Mk);
      ZF := Integers(M);
      // Edgar: Ben, should one use Strace?
      Mk`CuspDimension := Trace(Mk,1*ZF);
    end if;
  end if;
  return Mk`CuspDimension;
end intrinsic;



intrinsic EisensteinDimension(Mk::ModFrmHilD) -> RngIntElt
  {return the dimension of E(Mk)}
  if not assigned Mk`EisensteinDimension then
    N := Level(Mk);
    newforms_levels := {* Conductor(pair[1]) * Conductor(pair[2]) : pair in EisensteinAdmissableCharacterPairs(Mk) *};
    Mk`EisensteinDimension := &+[Integers()| #Divisors(N/mm)*mult : mm->mult in newforms_levels];
  end if;
  return Mk`EisensteinDimension;
end intrinsic;


intrinsic EisensteinAdmissableCharacterPairs(Mk::ModFrmHilD) -> SeqEnum
  {returns a list of all the primitive pairs <chi1, chi2> such that
  chi1*chi2 = Character(Mk) and Conductor(chi1)*Conductor(chi2) | Leve;(Mk)
  If the weight is 1, we only return pairs up to permutation}
  if not assigned Mk`EisensteinAdmissableCharacterPairs then
    N := Level(Mk);
    k := Weight(Mk);
    if #SequenceToSet(k) ne 1 then
      // there are no Eisenstein series in nonparallel weight
      Mk`EisensteinAdmissableCharacterPairs := [* *];
      return Mk`EisensteinAdmissableCharacterPairs;
    end if;
    k := k[1];
    chi := Character(Mk);
    M := Parent(Mk);
    X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
    assert X eq Parent(chi);
    chis := Elements(X);
    chiscond := [Conductor(c) : c in chis];
    chisdict := AssociativeArray();
    for i->c in chis do
      chisdict[c] := i;
    end for;
    // [i, j] pairs st chis[i]*chis[j] = chi
    pairs := [ [i, chisdict[chi*c^-1]] : i->c in chis ];
    // filter based on conductor
    pairs := [ p : p in pairs | N subset chiscond[p[1]] * chiscond[p[2]] ];
    if k eq 1 then
      // only keep one of the pairs [i, j], [j, i]
      // we E(chi, psi) = E(psi, chi)
      newpairs := [];
      for k0->p in pairs do
        i, j := Explode(p);
        k1 := Index(pairs, [j, i]);
        assert k1 gt 0;
        if k1 ge k0 then
          Append(~newpairs, p);
        end if;
      end for;
      pairs := newpairs;
    end if;
    prims := AssociativeArray();
    for i in SequenceToSet(&cat pairs) do
      prims[i] := AssociatedPrimitiveCharacter(chis[i]);
    end for;
    Mk`EisensteinAdmissableCharacterPairs := [* <prims[p[1]], prims[p[2]]> : p in pairs *];
  end if;
  return Mk`EisensteinAdmissableCharacterPairs;
end intrinsic;
