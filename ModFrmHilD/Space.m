/*****
ModFrmHilD
*****/

import "../ModFrmHil/diamond.m" : HeckeCharacterSubspace;

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Parent, // ModFrmHilDGRng
  Weight, // SeqEnum[RngIntElt]
  Level, // RngOrdIdl
  Basis, // = EisensteinBasis cat CuspFormBasis SeqEnum[ModFrmHilDElt]
  Character, // GrpHeckeElt, JV: why aren't we using Dirichlet?
  UnitCharacters, // Assoc: unit[bb] = omega
                 // Type(omega) = GrpCharUnitTotElt: TotallyPositiveUnits(Parent(Parent)) -> CoefficientRing
  EisensteinBasis, // SeqEnum[ModFrmHilDElt]
  CuspFormBasis, // SeqEnum[ModFrmHilDElt]
  EllipticBasis, // SeqEnum[ModFrmHilDElt]
  NewCuspFormBasis, // SeqEnum[ModFrmHilDElt] - basis for new cusp forms
  OldCuspFormBasis, // SeqEnum[ModFrmHilDElt] - basis for old cusp forms
  Dimension, // RngIntElt
  CuspDimension, //RngIntElt
  EisensteinDimension, //RngIntElt
  EisensteinAdmissibleCharacterPairs, // List of pairs of primitive characters
  Ambient, // BoolElt
  IsCuspidal, // BoolElt
  IsNew, // BoolElt
  MagmaSpace, //ModFrmHil
  MagmaNewformDecomposition, // List
  MagmaNewCuspForms, // SeqEnum[ModFrmHilElt]
  CoprimeClassGroupRepresentatives, // Assoc
  TraceCorrectionFactorFlag; // boo


////////// ModFrmHilD fundamental intrinsics //////////

intrinsic Print(Mk::ModFrmHilD, level::MonStgElt)
  {}
  M := Parent(Mk);
  if level in ["Default", "Minimal", "Maximal"] then
    if Mk`IsCuspidal then
	printf "Cuspidal subspace of ";
    end if;
    printf "Space of Hilbert modular forms over %o\n", BaseField(M);
    printf "Precision: %o\n", Precision(M);
    printf "Weight: %o\n", Weight(Mk);
    printf "Character: %o\n", Character(Mk);
    printf "Level: %o\n", IdealOneLine(Level(Mk));
    printf "UnitCharacters: %o", JoinString([Sprint(ValuesOnGens(UnitCharacters(Mk)[bb])) : bb in NarrowClassGroupReps(M)], ", ");
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
  return Parent(M1) eq Parent(M2) and
  Weight(M1) eq Weight(M2) and
  Level(M1) eq Level(M2) and
  Character(M1) eq Character(M2) and
  UnitCharacters(M1) eq UnitCharacters(M2);
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

intrinsic IsCuspidal(Mk::ModFrmHilD) -> BoolElt
{}
  return Mk`IsCuspidal;
end intrinsic;

intrinsic IsNew(Mk::ModFrmHilD) -> BoolElt
{}
  return Mk`IsNew;
end intrinsic;

intrinsic UnitCharacters(Mk::ModFrmHilD) -> Assoc
  {}
  return Mk`UnitCharacters;
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

intrinsic IsGamma1EisensteinWeight(chi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> BoolElt, RngIntElt
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

intrinsic IsCompatibleWeight(chi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> BoolElt, RngQuadElt
  {
    input: 
      chi: A ray class character chi
      k: A weight k
    returns:
      true if chi is compatible with the weight k, i.e. psi(e) = sign(e)^k for all units e.

      false, e if chi is incompatible with the weight k, where is an unit such that 
        psi(e) != sign(e)^k. 

      To elaborate, let K be the base field of chi and let m_fin and m_inf 
      denote the finite and infinite parts of the modulus of chi.
      The Dirichlet restriction of chi is the restriction of chi to the ray residue ring
      K^m/K^(m,1), where K^m is the multiplicative group of elements of K coprime to the
      finite part of the modulus of chi and K^(m,1) is the corresponding ray. 
      A character of the ray residue ring is a product of a character on (O_K/m)*,
      where O_K is the ring of integers of the field of definition of chi, and 
      the product of sign(v(eps)) for every (infinite real) v in m_inf. 

      For a fixed Hecke character chi, we denote the character on (O_K/m)* by psi.

      Nebentypus characters arise as characters of Gamma_0(m, bb)/Gamma_1(m, bb),
      i.e. of (O_K/m)*. If we consider the action of the matrix (e 0 \\ 0 e)
      on a HMF, we obtain the compatibility condition that psi(e) = sign(e)^k. 
  }

  comps := Components(chi);
  level, places := Modulus(chi);
   
  F := NumberField(Order(level)); 
  ZF := Integers(F);
  require places eq [1..Degree(F)] : "Chi is not a narrow class group character.";
  require (Degree(F) eq #InfinitePlaces(F)) : "The field is not totally real.";

  // implementing the character psi which is described above
  // as the product of the components of chi on the finite places
  psi := function(x); // x is a FldNumElt
    return (level eq 1*ZF) select 1 else &*[comps[v[1]](x) : v in Factorization(level)];
  end function;

  U, mU := UnitGroup(F);
  for eps in Generators(U) do
      sign_eps := 1;
      for i->v in InfinitePlaces(F) do
	  sign_eps *:= Sign(Evaluate(mU(eps),v))^k[i];
      end for;
      if (psi(mU(eps)) ne sign_eps) then
	  return false, mU(eps);
      end if;
  end for;
  return true, _;
end intrinsic;

intrinsic IsCompatibleWeight(chi::GrpHeckeElt, k::RngIntElt) -> BoolElt, RngQuadElt
{Check if the character chi is compatible with the weight k, i.e. psi_0(e) = sign(e)^k for all units e. If it fails, returns a unit e where they do not match.}
  F := NumberField(Order(Modulus(chi)));
  weight := [k : v in InfinitePlaces(F)];
  is_compat, idx := IsCompatibleWeight(chi, weight);
  if is_compat then return true, _; end if;
  return is_compat, idx;
end intrinsic;

intrinsic IsGamma1EisensteinWeight(chi::GrpHeckeElt, k::RngIntElt) -> BoolElt, RngIntElt
{Check if the character chi is compatible with the weight k, i.e. the parity
is the same at all infinite places. If it fails, returns the index of the first infinite
place where they do not match.}
  F := NumberField(Order(Modulus(chi)));
  weight := [k : v in InfinitePlaces(F)];
  is_compat, idx := IsGamma1EisensteinWeight(chi, weight);
  if is_compat then return true, _; end if;
  return is_compat, idx;
end intrinsic;

// TODO: some checks here? or leave it up to the user?
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt], chi::GrpHeckeElt : unitcharacters:=false) -> ModFrmHilD
  {}
  spaces := Spaces(M);
  if unitcharacters cmpeq false then
    unitcharacters := AssociativeArray();
    for bb in NarrowClassGroupReps(M) do
      unitcharacters[bb] := TrivialUnitCharacter(BaseField(M));
    end for;
  end if;

  uc_values := &cat[ValuesOnGens(unitcharacters[bb]) : bb in NarrowClassGroupReps(M)];

  if IsDefined(spaces, N) then
    if IsDefined(spaces[N], <k, chi, uc_values>) then
      return spaces[N][<k, chi, uc_values>];
    end if;
  else
    M`Spaces[N] := AssociativeArray();
  end if;
  Mk := ModFrmHilDInitialize();
  Mk`Parent := M;
  Mk`Weight := k;
  Mk`Level := N;
  Mk`Ambient := true;
  Mk`IsCuspidal := false;
  Mk`IsNew := false;
  require Parent(chi) eq HeckeCharacterGroup(N, [1..Degree(BaseField(M))]) : "The parent of chi should be HeckeCharacterGroup(N, [1..Degree(BaseField(M))])";
  // Right now when k[i] = 1, we don't want to restrict to compatible weights.
  if 1 notin k then
      is_compat, i := IsCompatibleWeight(chi, k);
      // require is_compat : Sprintf("The parity of the character at the infinite place %o does not match the parity of the weight", i);
      require is_compat : Sprintf("The parity of the character at the infinite places does not match the parity of the weight at the unit %o", i);
  end if;
  Mk`Character := chi;
  Mk`UnitCharacters := unitcharacters;
  require Type(Mk`UnitCharacters) eq Assoc: "we expect the unitcharacters keyword to be an associative array";
  require Keys(Mk`UnitCharacters) eq SequenceToSet(NarrowClassGroupReps(M)) :"we expect the keys of the associative array to be narrow class group reprsentatives";
  require {Type(v): k->v in Mk`UnitCharacters} eq { GrpCharUnitTotElt } : "we expect the values of the associative array to be of type GrpCharUnitTotElt";
  require &and[BaseField(v) eq BaseField(M): k->v in Mk`UnitCharacters]: "we expect all the unit characters to have the same base field";
  M`Spaces[N][<k, chi, uc_values>] := Mk;
  return Mk;
end intrinsic;


// overloaded for trivial level and character
intrinsic HMFSpace(M::ModFrmHilDGRng, k::SeqEnum[RngIntElt]: unitcharacters:=false) -> ModFrmHilD
  {}
  ZF := Integers(M);
  N := ideal<ZF|1>;
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi: unitcharacters:=unitcharacters);
end intrinsic;

// overloaded for trivial character
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt]: unitcharacters:=false) -> ModFrmHilD
  {}
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi: unitcharacters:=unitcharacters);
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
  Mk`Ambient := false;
  Mk`IsCuspidal := true;
  Mk`IsNew := true;
  return Mk;
end intrinsic;

intrinsic '*'(M1::ModFrmHilD, M2::ModFrmHilD) ->ModFrmHilD
  {return M1*M2 with the same level}
  require Parent(M1) eq Parent(M2): "we only support multiplication inside the same graded ring";
  require Level(M1) eq Level(M2) : "we only support multiplication with the same level";
  unitcharacters := AssociativeArray();
  for bb in Keys(UnitCharacters(M1)) do
    unitcharacters[bb] := UnitCharacters(M1)[bb] * UnitCharacters(M2)[bb];
  end for;
  return HMFSpace(Parent(M1),
                    Level(M1),
                    [Weight(M1)[i] + Weight(M2)[i] : i in [1..#Weight(M1)] ],
                    Character(M1)*Character(M2)
                    : unitcharacters:=unitcharacters);
end intrinsic;

intrinsic '/'(M1::ModFrmHilD, M2::ModFrmHilD) ->ModFrmHilD
  {return M1/M2 with the same level}
  require Parent(M1) eq Parent(M2): "we only support multiplication inside the same graded ring";
  require Level(M1) eq Level(M2) : "we only support multiplication with the same level";
  unitcharacters := AssociativeArray();
  for bb in Keys(UnitCharacters(M1)) do
    unitcharacters[bb] := UnitCharacters(M1)[bb]/UnitCharacters(M2)[bb];
  end for;
  return HMFSpace(Parent(M1),
                    Level(M1),
                    [Weight(M1)[i] - Weight(M2)[i] : i in [1..#Weight(M1)] ],
                    Character(M1)/Character(M2)
                    : unitcharacters:=unitcharacters);
end intrinsic;

intrinsic '^'(M::ModFrmHilD, n::RngIntElt) -> ModFrmHilD
  {return M^n with the same level}
  unitcharacters := AssociativeArray();
  for bb in Keys(UnitCharacters(M)) do
    unitcharacters[bb] := UnitCharacters(M)[bb]^n;
  end for;
  return HMFSpace(Parent(M),
                    Level(M),
                    [n * Weight(M)[i] : i in [1..#Weight(M)] ],
                    Character(M)^n
                    : unitcharacters:=unitcharacters);
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
  // see also eqn (22) in proof of Cor 3.12 in Dasgupta-Kakde
  // also Theorem 7 in Aranes-Cremona
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
	 //    require IsTrivial(DirichletRestriction(Character(Mk))): "Magma's builtin tools only supports characters which restrict to trivial Dirichlet characters.";
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
intrinsic CuspDimension(Mk::ModFrmHilD : version:="trace") -> RngIntElt
  {return dimension of S(Mk)}
  require version in ["builtin", "trace"] : "the options for trace are either \"builtin\" or \"trace formula\"";
  // FIXME: Ben will fix this eventually...
  if not Mk`Ambient then
    version := "builtin";
  end if;
  /*
  if NarrowClassNumber(Parent(Mk)) ne 1 and not IsTrivial(Character(Mk)) then
    version := "builtin";
  end if;
  */
  if not assigned Mk`CuspDimension then
    k := Weight(Mk);
    if version eq "builtin" then
	       //      require IsTrivial(DirichletRestriction(Character(Mk))): "we rely on magma built-in functions, which only works for characters whose associated Dirichlet character is trivial";
      Mk`CuspDimension := Dimension(HilbertCuspForms(Mk));
    else
      M := Parent(Mk);
      ZF := Integers(M);
      Mk`CuspDimension := Integers()!Trace(Mk,1*ZF);
    end if;
  end if;
  return Mk`CuspDimension;
end intrinsic;

intrinsic EisensteinDimension(Mk::ModFrmHilD) -> RngIntElt
  {return the dimension of E(Mk)}
  if not assigned Mk`EisensteinDimension then
    N := Level(Mk);
    newforms_levels := AssociativeArray();
    for pair in EisensteinAdmissibleCharacterPairs(Mk) do
      lvl := Conductor(pair[1]) * Conductor(pair[2]);
      if not IsDefined(newforms_levels, lvl) then
        newforms_levels[lvl] := 0;
      end if;
      newforms_levels[lvl] +:= EulerPhi(LCM([Order(e) : e in pair]));
    end for;
    Mk`EisensteinDimension := &+[Integers()| #Divisors(N/mm)*rel_dim : mm->rel_dim in newforms_levels];
  end if;
  return Mk`EisensteinDimension;
end intrinsic;

// copy pasted from ModSym/dirichlet.m
intrinsic GaloisConjugacyRepresentatives(S::[GrpHeckeElt]) -> SeqEnum
{Representatives for the Gal(Qbar/Q)-conjugacy classes of Dirichlet characters 
 contained in the given sequence S}  
   
   G := Universe(S);

if #S eq 0 then
//   or Type(BaseRing(G)) eq FldRat then 
     return S;
   end if;

  // require ISA(Type(BaseRing(G)), FldAlg) :
    //      "The base ring of argument 1 must be a number field.";

   n := Exponent(AbelianGroup(G));     
if n eq 1 then return S; end if;
   i := 1;
   U := [k : k in [1..n-1] | GCD(k,n) eq 1]; // Steve changed this, was [2..n-1]
   while i lt #S do
      x := S[i];
      for m in U do
         y := x^m;
         R := [j : j in [i+1..#S] | S[j]`Element eq y`Element];
         for j in Reverse(R) do    // important to reverse.
            Remove(~S,j);
         end for;
      end for;
      i +:= 1;
   end while;
   return S;
end intrinsic;

intrinsic EisensteinAdmissibleCharacterPairs(Mk::ModFrmHilD) -> SeqEnum
  {returns a list of all the primitive pairs <chi1, chi2> such that
  chi1*chi2 = Character(Mk) and Conductor(chi1)*Conductor(chi2) | Level(Mk)
  If the weight is 1, we only return pairs up to permutation}
  if not assigned Mk`EisensteinAdmissibleCharacterPairs then
    N := Level(Mk);
    k := Weight(Mk);
    if not IsParallel(k) then
      // there are no Eisenstein series in nonparallel weight
      Mk`EisensteinAdmissibleCharacterPairs := [* *];
      return Mk`EisensteinAdmissibleCharacterPairs;
    end if;
    k := k[1];
    chi := Character(Mk);
    M := Parent(Mk);
    X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
    assert X eq Parent(chi);
    chis := Elements(X);
    chis_reps := Set(GaloisConjugacyRepresentatives(chis));
    chis_reps_index := {i : i->c in chis | c in chis_reps};
    chiscond := [Conductor(c) : c in chis];
    chisdict := AssociativeArray();
    for i->c in chis do
      chisdict[c] := i;
    end for;
    // [i, j] pairs st chis[i]*chis[j] = chi
    pairs := [ [i, chisdict[chi*c^-1]] : i->c in chis | i in chis_reps_index ];
    // filter based on conductor
    pairs := [ p : p in pairs | N subset chiscond[p[1]] * chiscond[p[2]] ];
    if k eq 1 then
      // only keep one of the pairs [i, j], [j, i]
      // we E(chi, psi) = E(psi, chi)
      newpairs := [];
      for k0->p in pairs do
	i, j := Explode(p);
	// this might be zero, as we forced i to be galois representative 
        k1 := Index(pairs, [j, i]);
        if k1 le k0 then // nonetheless, k0 > 0
          Append(~newpairs, p);
        end if;
      end for;
      pairs := newpairs;
    end if;
    prims := AssociativeArray();
    for i in SequenceToSet(&cat pairs) do
      prims[i] := AssociatedPrimitiveCharacter(chis[i]);
    end for;
    Mk`EisensteinAdmissibleCharacterPairs := [* <prims[p[1]], prims[p[2]]> : p in pairs *];
  end if;
  return Mk`EisensteinAdmissibleCharacterPairs;
end intrinsic;

// Coprime class group representatives
intrinsic CoprimeClassGroupRepresentatives(Mk::ModFrmHilD) -> Assoc
  {Returns an associative array which converts the standard class group representatives (stored as aa in ClassGroupReps(F))
  to class group representatives bb that are coprime to NN i.e. H[aa] = bb where [aa] = [bb] in Cl(F) and (bb,NN) = 1.}
  if not assigned Mk`CoprimeClassGroupRepresentatives then
    NN := Level(Mk);
    F := BaseField(Mk);
    ZF := Integers(F);
    C := ClassGroupReps(F); // class group representatives
    H := AssociativeArray(); // Hash: Standard class group representative { aa } -> Class group representatives coprime to NN { bb }
    for aa in C do 
      q := CoprimeRepresentative(aa,NN);
      bb := ideal < ZF | q * aa >;
      H[aa] := bb;
    end for;
    Mk`CoprimeClassGroupRepresentatives := H;
  end if;
  return Mk`CoprimeClassGroupRepresentatives;
end intrinsic;


// Trace flag for correction factor
intrinsic TraceCorrectionFactorFlag(Mk::ModFrmHilD) -> Assoc
  {Checks if Mk has parallel weight 2 and if the character chi factors through the map a -> a^2 from Cl(F) -> Cl+(F) }
  if not assigned Mk`TraceCorrectionFactorFlag then
    
    // Initialize
    k := Weight(Mk);
    chi := Character(Mk);
    F := BaseField(Mk);
    H := CoprimeClassGroupRepresentatives(Mk);
    C := [ H[aa] : aa in ClassGroupReps(F) ];
    ker := [ i : i in C | IsNarrowlyPrincipal(i^2) ]; // kernel of map a |-> a^2 from Cl(F) -> Cl+(F)
    
    /* Requirements
    (a) k = (2,...,2) is parallel weight 2
    (b) chi factors through the homomorphism C -> NC given by a |-> a^2. */
    
    // Check Requirements
    a := Set(k) eq {2}; 
    b := {chi(a) : a in ker} eq {1}; 
    Mk`TraceCorrectionFactorFlag := a and b;
  end if;
  return Mk`TraceCorrectionFactorFlag;
end intrinsic;

// I found it useful to have this function when we want to restrict to cuspidal subspaces

intrinsic CuspidalSubspace(M::ModFrmHilD) -> ModFrmHilD
{The cuspidal subspace of M.}

  Mk := ModFrmHilDInitialize();
  Mk`Parent := M`Parent;
  Mk`Weight := M`Weight;
  Mk`Level := M`Level;
  Mk`Character := M`Character;
  Mk`MagmaSpace := HeckeCharacterSubspace(HilbertCuspForms(M), M`Character);
  Mk`EisensteinDimension := 0;
  Mk`Ambient := false;
  Mk`UnitCharacters := M`UnitCharacters;
  Mk`IsCuspidal := true;
  Mk`IsNew := false;
  return Mk;  
end intrinsic;

intrinsic IsParitious(k::SeqEnum[RngIntElt]) -> BoolElt
  {
    input: 
      k: The weight of the HMF
    returns:
      true when k is paritious (all components have the same parity)
      false otherwise
  }
  k_1 := k[1];
  return &and[((k_i - k[1]) mod 2 eq 0) : k_i in k];
end intrinsic;

intrinsic IsParallel(k::SeqEnum[RngIntElt]) -> BoolElt
  {
    input: 
      k: The weight of the HMF
    returns:
      true when k is parallel (all components are equal)
      false otherwise
  }
  return #SequenceToSet(k) eq 1;
end intrinsic;
