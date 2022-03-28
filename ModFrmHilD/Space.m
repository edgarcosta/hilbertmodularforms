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
  Dimension, // RngIntElt
  CuspDimension, //RngIntElt
  EisensteinDimension, //RngIntElt
  EisensteinAdmissibleCharacterPairs, // List of pairs of primitive characters
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
  require Parent(chi) eq HeckeCharacterGroup(N, [1..Degree(BaseField(M))]) : "The parent of chi should be HeckeCharacterGroup(N, [1..Degree(BaseField(M))])";
  is_compat, i := IsCompatibleWeight(chi, k);
  require is_compat : Sprintf("The parity of the character at the infinite place %o does not match the parity of the weight", i);
  Mk`Character := chi;
  Mk`UnitCharacters := unitcharacters;
  require Type(Mk`UnitCharacters) eq Assoc: "we expect the unitcharacters keyword to be an associative array";
  require Keys(Mk`UnitCharacters) eq SequenceToSet(NarrowClassGroupReps(M)) :"we expect the keys of the associative array to be narrow class group reprsentatives";
  require {Type(v): v in Mk`UnitCharacters} eq { GrpCharUnitTotElt } : "we expect the values of the associative array to be of type GrpCharUnitTotElt";
  require &and[BaseField(v) eq BaseField(M): v in Mk`UnitCharacters]: "we expect all the unit characters to have the same base field";
  M`Spaces[N][<k, chi, uc_values>] := Mk;
  return Mk;
end intrinsic;


// overloaded for trivial level and character
intrinsic HMFSpace(M::ModFrmHilDGRng, k::SeqEnum[RngIntElt]: unitcharacters:=false) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  N := ideal<ZF|1>;
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi: unitcharacters:=unitcharacters);
end intrinsic;

// overloaded for trivial character
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt]: unitcharacters:=false) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
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

// moving from RngOrdFracIdl to ModDed and back
intrinsic IdealToModule(a::FldElt, ss::RngOrdFracIdl) -> ModDedElt 
  {Map an element a of a fractional ideal ss to ss thought of as a module}
  assert a in ss;
  ss_mod := Module([ss]);
  return ss_mod!(a*ss_mod.1);
end intrinsic;

intrinsic ModuleToIdeal(a::ModDedElt) -> RngElt
  {Map an element a of a fractional ideal thought of a module to an element of the fractional ideal}
  b := Eltseq(a)[1];
  F := Parent(b);
  ZF := Integers(F);
  if IsIntegral(b) then
    return ZF!b;
  else
    return b;
  end if;
end intrinsic;

intrinsic IdealToModule(a::RngOrdElt, ss::RngOrdFracIdl) -> ModDedElt
  {}
  R := Parent(a);
  F := NumberField(R);
  return IdealToModule(F!a,ss);
end intrinsic;

//intrinsic ReduceModuloIdeal(a::FldElt, I::RngOrdFracIdl, J::RngOrdFracIdl) -> FldElt
intrinsic ReduceModuloIdeal(a::RngElt, I::RngOrdFracIdl, J::RngOrdFracIdl) -> FldElt
  {Take an element a of I, reduce it mod J, and then lift it back to an element of I.}
  assert J subset I;
  I_mod := Module([I]);
  J_mod := Module([J]);
  ImodJ , mp := quo< I_mod | J_mod >;
  a_mod := IdealToModule(a, I);
  a_modJ := mp(a_mod);
  return ModuleToIdeal(a_modJ @@ mp);
end intrinsic;

// see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4
intrinsic GeneratorOfQuotientModuleCRT(ss::RngOrdFracIdl, MM::RngOrdIdl) -> RngElt 
  {}
  ZF := Order(ss);
  if ss*MM eq ss then
    return ZF!1;
  end if;
  facts := Factorization(ss*MM);
  //printf "factors of ss*MM: %o\n", facts;
  facts_num := [];
  facts_den := [];
  ss_vals_num := [];
  ss_vals_den := [];
  for fact in facts do
    if fact[2] gt 0 then // primes with positive valuation
      Append(~facts_num, fact);
      Append(~ss_vals_num, Valuation(ss,fact[1]));
    else // primes with negative valuation
      Append(~facts_den, fact);
      Append(~ss_vals_den, Valuation(ss,fact[1]));
    end if;
  end for;
  //printf "ss_vals num = %o\n", ss_vals_num;
  //printf "ss_vals den = %o\n", ss_vals_den;
  residues_num := [];
  residues_den := [];
  moduli_num := [];
  moduli_den := [];
  for i := 1 to #facts_num do
    fact := facts_num[i];
    P := fact[1];
    //v := fact[2];
    v := ss_vals_num[i];
    t := UniformizingElement(P);
    residues_num cat:= [0, (t^v mod P^(v+1))]; // might be a problem if v=0
    moduli_num cat:= [P^v, P^(v+1)];
  end for;
  for i := 1 to #facts_den do
    fact := facts_den[i];
    P := fact[1];
    //v := -fact[2]; // want positive valuation
    v := -ss_vals_den[i]; // want positive valuation
    t := UniformizingElement(P);
    residues_den cat:= [0, (t^v mod P^(v+1))];
    moduli_den cat:= [P^v, P^(v+1)];
  end for;
  if #moduli_num eq 0 then // if list of moduli is empty
    a_num := ZF!1;
  else
    //printf "residues for num = %o\n", residues_num;
    //printf "moduli for num = %o\n", moduli_num;
    a_num := CRT(residues_num, moduli_num);
  end if;
  if #moduli_den eq 0 then
    a_den := ZF!1;
  else
    //printf "residues for den = %o\n", residues_den;
    //printf "moduli for den = %o\n", moduli_den;
    a_den := CRT(residues_den, moduli_den);
  end if;
  //printf "a_num = %o\n", a_num;
  //printf "a_den = %o\n", a_den;
  // verify it generates
  a := a_num/a_den;
  assert a*ZF + ss*MM eq ss;
  return a;
end intrinsic;

// see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4
intrinsic GeneratorsOfQuotientModuleBruteForce(ss::RngOrdFracIdl, MM::RngOrdIdl) -> SeqEnum
  {Return the sequence of generators of ss/(ss*MM) as a ZF/MM-module by looping over all elements of ss/(ss*MM).}
  ZF := Order(ss);
  F := NumberField(ZF);
  ZFMM, mpMM := quo< ZF | MM>;
  // loop over all elts of ss/(ss*MM)
  ss_gens := Generators(ss);
  ss_ngens := #ss_gens;
  quotient_gens := [];
  for el in CartesianPower(ZFMM, ss_ngens) do
    t := ZF!0;
    for i := 1 to ss_ngens do
      t +:= (el[i] @@ mpMM)*ss_gens[i];
    end for;
    // check if new mod ss*MM
    /*
      new_bool := true;
      for q in quotient_gens do
        if (t - q) in ss*MM then
          new_bool := false;
        end if;
      end for;
    */
    //if (t*ZF + ss*MM eq ss) and new_bool then
    if (t*ZF + ss*MM eq ss) then
      Append(~quotient_gens, ReduceModuloIdeal(t, ss, ss*MM));
    end if;
  end for;
  quotient_gens := SetToSequence(SequenceToSet(quotient_gens));
  //printf "# of quotient gens = %o\n", #quotient_gens;
  //printf "number of units in ZF/ideal = %o\n", #UnitGroup(ZFMM);
  assert #quotient_gens eq #UnitGroup(ZFMM);
  return quotient_gens;
end intrinsic;

intrinsic GeneratorsOfQuotientModule(ss::RngOrdFracIdl, MM::RngOrdIdl) -> SeqEnum
  {Return the sequence of generators of ss/(ss*MM) as a ZF/MM-module using CRT.}
  ZF := Order(ss);
  F := NumberField(ZF);
  ZFMM, mpMM := quo< ZF | MM>;
  U, mpU := UnitGroup(ZFMM);
  U_seq := [mpU(el) : el in U];
  a := GeneratorOfQuotientModuleCRT(ss,MM);
  return [a*(el @@ mpMM) : el in U_seq];
end intrinsic;

// see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4
intrinsic GeneratorsOfQuotientModuleModuloTotallyPositiveUnitsBruteForce(ss::RngOrdFracIdl, MM::RngOrdIdl) -> SeqEnum
  {Return the sequence of generators of ss/(ss*MM) as a ZF/MM-module modulo totally positive units in ZF.}

  quotient_gens := GeneratorsOfQuotientModule(ss,MM);
  F := Parent(quotient_gens[1]);
  F := NumberField(F);
  eps := FundamentalUnitTotPos(F);

  // compute orbits of the elements of quotient_gens under totally positive units
  // by repeatedly Shintani-reducing and reducing mod ss*MM (using ReduceModuloIdeal)
  remaining := [1..#quotient_gens];
  orbits := [];
  while #remaining ne 0 do
    ind0 := remaining[1];
    a := quotient_gens[ind0];
    orb := [ind0];
    rep_bool := false;
    while not rep_bool do
      a := ReduceModuloIdeal(eps*a, ss, ss*MM);
      ind := Index(quotient_gens, a);
      if ind eq ind0 then
        rep_bool := true;
        break;
      end if;
      Append(~orb, ind);
    end while;
    Append(~orbits, orb);
    printf "orbit found = %o\n", orb;
    remaining := [el : el in remaining | not el in orb];
    printf "remaining indices = %o\n", remaining;
  end while;
  printf "orbits = %o\n", orbits;
  // return one element from each orbit
  return [orb[1] : orb in orbits];
end intrinsic;

// see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4
// Use transversal for <eps> < (ZF/MM)^* to get one representative from each of the orbits of (ss/(ss*MM))^* under the action of epsilon
intrinsic GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss::RngOrdFracIdl, MM::RngOrdIdl) -> SeqEnum
  {Return the sequence of generators of ss/(ss*MM) as a ZF/MM-module modulo totally positive units in ZF.}

  a := GeneratorOfQuotientModuleCRT(ss,MM);
  F := Parent(a);
  F := NumberField(F);
  ZF := Integers(F);
  eps := FundamentalUnitTotPos(F);

  ZFMM, mp := quo<ZF |MM>;
  UQ, mpQ := UnitGroup(ZFMM);
  eps_bar := mp(eps) @@ mpQ;
  eps_gp := sub< UQ | eps_bar>;
  T := [mpQ(el) : el in Transversal(UQ, eps_gp)];
  reps := [a*(el @@ mp) : el in T];
  return [ReduceModuloIdeal(el, ss, ss*MM) : el in reps];
end intrinsic;

intrinsic ReducePairModuloUnits(NN::RngOrdIdl, bb::RngOrdIdl, ss::RngOrdFracIdl, MM::RngOrdIdl, a::RngElt, c::RngElt) -> SeqEnum
  {}

  F := Parent(a);
  F := NumberField(F);
  ZF := Integers(F);
  eps_p := FundamentalUnitTotPos(F);
  eps := FundamentalUnit(F);

  ZFMM, mpMM := quo<ZF |MM>;
  ZFNNMM, mpNNMM := quo<ZF | (NN div MM) >;
  UQMM, mpQMM := UnitGroup(ZFMM);
  UQNNMM, mpQNNMM := UnitGroup(ZFNNMM);

  eps_barMM := mpMM(eps) @@ mpQMM;
  eps_barNNMM := mpNNMM(eps) @@ mpQNNMM;

  D, i1, i2, p1, p2 := DirectSum(UQMM, UQNNMM);
  print D;
  eps_gp := sub< D | [i1(mpMM(eps) @@ mpQMM) + i2(mpNNMM(eps) @@ mpQNNMM), i1(mpMM(-1) @@ mpQMM) + i2(mpNNMM(-1) @@ mpQNNMM), i1(eps_barMM), i2(eps_barNNMM)] >;
  T := [];
  for el in Transversal(D, eps_gp) do
    Append(~T, [* mpQMM(p1(el)) @@ mpMM, mpQNNMM(p2(el)) @@ mpNNMM *]);
  end for;
  reps := [ [* a*(el[1] @@ mpMM), c*(el[2] @@ mpNNMM) *] : el in T];
  for i := 1 to #reps do
    rep := reps[i];
    if rep[2] eq 0 then
      print Transversal(D, eps_gp)[i];
    end if;
  end for;
  final := [];
  for el in reps do
    a0, c0 := Explode(el);
    a_new := ReduceModuloIdeal(a0, ss, ss*MM);
    c_new := ReduceModuloIdeal(c0, ss*bb*MM, ss*bb*NN);
    Append(~final, [a_new, c_new]);
  end for;
  return final;
end intrinsic;

// P_1(NN)_bb in eqn 5.1.6 in paper, or Lemma 3.6 of Dasgupta-Kakde
intrinsic Gamma1Quadruples(NN::RngOrdIdl, bb::RngOrdIdl) -> SeqEnum
  {Return list of quadruples given in Lemma 3.6 of Dasgupta-Kakde, which is in bijection with cusps of Gamma1(NN)_bb.}
  ZF := Order(NN);
  F := NumberField(ZF);
  Cl, mpCl := ClassGroup(ZF);
  Cl_seq := [mpCl(el) : el in Cl];
 
  quads := [];
  for ss in Cl_seq do
    for MM in Divisors(NN) do
      a := GeneratorOfQuotientModuleCRT(ss,MM);
      c := GeneratorOfQuotientModuleCRT(ss*bb*MM,(NN/MM));
      //RssMM := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss,MM);
      //RssMM_comp := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss*bb*MM,(NN/MM));
      pairs := ReducePairModuloUnits(NN, bb, ss, MM, a, c);
      for el in pairs do
        Append(~quads, [* ss, MM, el *]);
      end for;
    end for;
  end for;
  return quads;
end intrinsic;

// see Lemma 5.1.10 in paper, or Lemma 3.6 of Dasgupta-Kakde
intrinsic CuspLiftSecondCoordinate(c_bar::RngElt, ss::RngOrdFracIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
  {With the notation as in section 5 of the paper, given c_bar in P_1(NN)_bb, lift c_bar to a c satisfying GCD(c*bb^-1,NN) = MM.}

  ZF := Order(ss);
  facts := Factorization(ss*bb*NN);
  //printf "factors of ss*bb*NN: %o\n", facts;
  Ps_num := [fact[1] : fact in facts | fact[2] gt 0];
  mults_num := [fact[2] : fact in facts | fact[2] gt 0];
  Ps_den := [fact[1] : fact in facts | fact[2] lt 0];
  mults_den := [fact[2] : fact in facts | fact[2] lt 0];

  residues_num := [];
  residues_den := [];
  moduli_num := [];
  moduli_den := [];
  // numerator residues and moduli
  print "making numerator";
  for i := 1 to #Ps_num do
    P := Ps_num[i];
    //v := mults_num[i];
    v := Valuation(ss*bb*MM,P);
    if v gt 0 then
      printf "nonzero valuation; P = %o, v = %o\n", P, v;
      residues_num cat:= [0, (c_bar mod P^(v+1))]; // might be a problem if v=0
      moduli_num cat:= [P^v, P^(v+1)];
    else
      residues_num cat:= [(c_bar mod P^mults_num[i])]; // might be a problem if v=0
      moduli_num cat:= [P^mults_num[i]];
    end if;
  end for;
  // denominator residues and moduli
  print "making denominator";
  for i := 1 to #Ps_den do
    P := Ps_den[i];
    //v := -mults_den[i];
    v := -Valuation(ss*bb*MM,P);
    if v gt 0 then
      print "nonzero valuation; P = %o, v = %o\n", P, v;
      residues_den cat:= [0, (c_bar mod P^(v+1))]; // might be a problem if v=0
      moduli_den cat:= [P^v, P^(v+1)];
    else
      residues_den cat:= [(c_bar mod P^mults_den[i])]; // might be a problem if v=0
      moduli_den cat:= [P^mults_den[i]];
    end if;
  end for;

  printf "residues for num = %o\n", residues_num;
  printf "moduli for num = %o\n", moduli_num;
  printf "residues for den = %o\n", residues_den;
  printf "moduli for den = %o\n", moduli_den;

  if #moduli_num eq 0 then // if list of moduli is empty
    c_num := ZF!1;
  else
    c_num := CRT(residues_num, moduli_num);
  end if;
  if #moduli_den eq 0 then
    c_den := ZF!1;
  else
    c_den := CRT(residues_den, moduli_den);
  end if;
  c := c_num/c_den;
  assert GCD(c*(bb^-1),NN) eq MM;
  assert c - c_bar in ss*bb*NN;
  return c;
end intrinsic;

// see Lemma 5.1.10 in paper, or Lemma 3.6 of Dasgupta-Kakde
intrinsic CuspLiftFirstCoordinate(a_bar::RngElt, c::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
  {}
  ZF := Order(ss);
  //facts := Factorization(ss*MM);
  // if c=0, then ss should be principal
  if c eq 0 then
    pbool, a := IsPrincipal(ss);
    assert pbool;
    facts := Factorization(ss*MM);
    Ps_num := [fact[1] : fact in facts | fact[2] gt 0];
    //mults_num := [fact[2] : fact in facts | fact[2] gt 0];
    mults_num := [Valuation((ss*MM), P) : P in Ps_num];
    Ps_den := [fact[1] : fact in facts | fact[2] lt 0];
    //mults_den := [fact[2] : fact in facts | fact[2] lt 0];
    mults_den := [Valuation((ss*MM), P) : P in Ps_den];
  else
    facts := Factorization(c*(bb^-1));
    Ps_num := [fact[1] : fact in facts | fact[2] gt 0];
    mults_num := [Valuation((c*bb^-1), P) : P in Ps_num];
    Ps_den := [fact[1] : fact in facts | fact[2] lt 0];
    mults_den := [Valuation((c*bb^-1), P) : P in Ps_den];
  end if;

  residues_num := [];
  residues_den := [];
  moduli_num := [];
  moduli_den := [];
  // numerator residues and moduli
  print "making numerator";
  for i := 1 to #Ps_num do
    P := Ps_num[i];
    //v := mults_num[i];
    v := Valuation(ss,P);
    if v gt 0 then
      printf "nonzero valuation; P = %o, v = %o\n", P, v;
      residues_num cat:= [0, (a_bar mod P^(v+1))]; // might be a problem if v=0
      moduli_num cat:= [P^v, P^(v+1)];
    else
      residues_num cat:= [(a_bar mod P^mults_num[i])]; // might be a problem if v=0
      moduli_num cat:= [P^mults_num[i]];
    end if;
  end for;
  // denominator residues and moduli
  print "making denominator";
  for i := 1 to #Ps_den do
    P := Ps_den[i];
    //v := -mults_den[i];
    v := -Valuation(ss,P);
    if v gt 0 then
      print "nonzero valuation; P = %o, v = %o\n", P, v;
      residues_den cat:= [0, (a_bar mod P^(v+1))]; // might be a problem if v=0
      moduli_den cat:= [P^v, P^(v+1)];
    else
      residues_den cat:= [(a_bar mod P^mults_den[i])]; // might be a problem if v=0
      moduli_den cat:= [P^mults_den[i]];
    end if;
  end for;

  printf "residues for num = %o\n", residues_num;
  printf "moduli for num = %o\n", moduli_num;
  printf "residues for den = %o\n", residues_den;
  printf "moduli for den = %o\n", moduli_den;

  if #moduli_num eq 0 then // if list of moduli is empty
    a_num := ZF!1;
  else
    a_num := CRT(residues_num, moduli_num);
  end if;
  if #moduli_den eq 0 then
    a_den := ZF!1;
  else
    a_den := CRT(residues_den, moduli_den);
  end if;
  a := a_num/a_den;
  assert GCD(a*ZF,c*(bb^-1)) eq ss;
  assert a - a_bar in ss*MM;
  return a;
end intrinsic;

// see Lemma 5.1.10 in paper, or Lemma 3.6 of Dasgupta-Kakde
/*
intrinsic CuspLiftFirstCoordinate(a_bar::RngElt, c::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
  {}
  ZF := Order(ss);
  if c eq 0 then
    pbool, a := IsPrincipal(ss);
    assert pbool;
  else
    a := ZF!GeneratorOfQuotientModuleCRT(ss, ideal< ZF | c*(bb^-1) >);
  end if;
  printf "generator for ss/(c*(bb^-1)) = %o\n", a;
  if not (a-a_bar) in ss*MM then
    Q, mpQ := quo< ZF | c*(bb^-1) >; // breaks if c=0
    lambda_bar := mpQ(a)^-1*mpQ(a_bar);
    printf "lambda_bar = %o\n", lambda_bar;
    a *:= (lambda_bar @@ mpQ);
  end if;
  assert a*ZF + c*(bb^-1) eq ss;
  assert a - a_bar in ss*MM;
  return a;
end intrinsic;
*/

// Need to lift the [a,c] in the quadruples in a special way that respects certain congruences
intrinsic Gamma1Cusps(NN::RngOrdIdl, bb::RngOrdIdl) -> SeqEnum
  {}
  ZF := Order(NN);
  F := NumberField(ZF);
  quads := Gamma1Quadruples(NN, bb);
  cusps_seq := [];
  for i := 1 to #quads do
    printf "i = %o\n", i;
    quad := quads[i];
    printf "quad = %o\n", quad;
    ss, MM, ac_bar := Explode(quad);
    a_bar, c_bar := Explode(ac_bar);
    c := CuspLiftSecondCoordinate(c_bar, ss, MM, NN, bb);
    a := CuspLiftFirstCoordinate(a_bar, c, ss, MM, NN, bb);
    Append(~cusps_seq, [a,c]);
  end for;
  PP1 := ProjectiveSpace(F,1);
  cusps := [PP1!el : el in cusps_seq];
  return cusps;
end intrinsic;

// P_0(NN)_bb in eqn 5.1.9 in paper
// TODO: figure out how to mod out by (ZF/NN)^*
intrinsic Gamma0Quadruples(NN::RngOrdIdl, bb::RngOrdIdl) -> SeqEnum
  {}
  ZF := Ring(Parent(NN));
  F := NumberField(ZF);
  Cl, mpCl := ClassGroup(ZF);
  Cl_seq := [mpCl(el) : el in Cl];
 
  quads := [];
  for ss in Cl_seq do
    for MM in Divisors(NN) do
      RssMM := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss,MM);
      RssMM_comp := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss*bb*MM,(NN/MM));
      // TODO: mod out by (ZF/NN)^*
      for a in RssMM do
        for c in RssMM_comp do
          Append(~quads, [* ss, MM, a, c*]);
        end for;
      end for;
    end for;
  end for;
  return quads;
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


intrinsic EisensteinAdmissibleCharacterPairs(Mk::ModFrmHilD) -> SeqEnum
  {returns a list of all the primitive pairs <chi1, chi2> such that
  chi1*chi2 = Character(Mk) and Conductor(chi1)*Conductor(chi2) | Level(Mk)
  If the weight is 1, we only return pairs up to permutation}
  if not assigned Mk`EisensteinAdmissibleCharacterPairs then
    N := Level(Mk);
    k := Weight(Mk);
    if #SequenceToSet(k) ne 1 then
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
    Mk`EisensteinAdmissibleCharacterPairs := [* <prims[p[1]], prims[p[2]]> : p in pairs *];
  end if;
  return Mk`EisensteinAdmissibleCharacterPairs;
end intrinsic;
