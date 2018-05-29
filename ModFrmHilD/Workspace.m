/* object to index Assoc array to cache eigenforms to space M */

declare type LevelAndWeight;
declare attributes LevelAndWeight:
  Level,
  Weight;

intrinsic LevelAndWeightInitialize() -> LevelAndWeight
  {Create an empty LevelAndWeight object.}
  NNk := New(LevelAndWeight);
  return NNk;
end intrinsic;

intrinsic LevelAndWeightInitialize(NN::RngOrdIdl, k::SeqEnum[RngIntElt]) -> LevelAndWeight
  {}
  NNk := LevelAndWeightInitialize();
  NNk`Level := NN;
  NNk`Weight := k;
  return NNk;
end intrinsic;

intrinsic Level(NNk::LevelAndWeight) -> RngOrdIdl
  {}
  return NNk`Level;
end intrinsic;

intrinsic Weight(NNk::LevelAndWeight) -> SeqEnum[RngIntElt]
  {}
  return NNk`Weight;
end intrinsic;

intrinsic 'eq'(NNk1::LevelAndWeight, NNk2::LevelAndWeight) -> BoolElt
  {}
  if Level(NNk1) eq Level(NNk2) then
    if Weight(NNk1) eq Weight(NNk2) then
      return true;
    else
      return false;
    end if;
  else
    return false;
  end if;
end intrinsic;

intrinsic Print(NNk::LevelAndWeight)
  {}
  if assigned NNk`Level then
    printf "Level:\n%o\n", Level(NNk);
  end if;
  if assigned NNk`Weight then
    printf "Weight:\n%o", Weight(NNk);
  end if;
end intrinsic;

/* Compute */

// TODO move level from space to form
intrinsic CacheHeckeEigenvalues(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {Computes and caches the eigenvalues to the space M and returns M.}
  F := BaseField(M);
  N := Level(M); // TODO change this to an input
  prec := Precision(M);
  key := LevelAndWeightInitialize(N, k);
  if assigned M`HeckeEigenvalues then
    if key in Keys(M`HeckeEigenvalues) then
      printf "Hecke eigenvalues already computed for\nLevel:\n%o\nWeight\n%o", N, k;
      return M;
    else
      MF := HilbertCuspForms(F, N, k);
      S := NewSubspace(MF);
      newspaces  := NewformDecomposition(S);
      newforms := [* Eigenform(U) : U in newspaces *];
      primes := Primes(M);
      EVnewforms := [* *];
      for newform in newforms do
        eigenvalues := [];
        for i in [1..#primes] do
          eigenvalues[i] := HeckeEigenvalue(newform, primes[i]);
        end for;
        Append(~EVnewforms, eigenvalues);
      end for;
      M`HeckeEigenvalues[key] := EVnewforms;
      return M;
    end if;
  else
    // need to make Assoc M`HeckeEigenvalues in this case
    MF := HilbertCuspForms(F, N, k);
    S := NewSubspace(MF);
    newspaces  := NewformDecomposition(S);
    newforms := [* Eigenform(U) : U in newspaces *];
    primes := Primes(M);
    EVnewforms := [];
    for newform in newforms do
      eigenvalues := [];
      for i in [1..#primes] do
        eigenvalues[i] := HeckeEigenvalue(newform, primes[i]);
      end for;
      Append(~EVnewforms, eigenvalues);
    end for;
    // M`HeckeEigenvalues not assigned so make new Assoc
    M`HeckeEigenvalues := AssociativeArray();
    M`HeckeEigenvalues[key] := EVnewforms;
    return M;
  end if;
end intrinsic;

/* Save */

intrinsic SaveText(M::ModFrmHilD) -> MonStgElt
  {}
  str := "";
  str *:= Sprintf("M := %m;\n", M);
  if assigned M`HeckeEigenvalues then
    hecke := HeckeEigenvalues(M);
    ZF<w> := BaseField(M);
    str *:= Sprintf("F<w> := BaseField(M);\n");
    str *:= Sprintf("ZF := Integers(F);\n");
    str *:= Sprintf("primesArray := %o;\n", [Generators(pp):  pp in Primes(M)]);
    str *:= Sprintf("M`Primes := [ideal<ZF | {F!x : x in I}> : I in primesArray];\n\n");

    str *:= Sprintf("M`HeckeEigenvalues := AssociativeArray();\n");
    for key in Keys(hecke) do
      NN := Level(key);
      k := Weight(key);
      str *:= Sprintf("NN := ideal<ZF|%o>;\n", Basis(NN));
      str *:= Sprintf("k := %m;\n", k);
      str *:= Sprintf("key := LevelAndWeightInitialize(NN, k);\n");
      str *:= Sprintf("EVlist := [* *];\n");
      for i := 1 to #hecke[key] do
        str *:= Sprintf("l := %m;\n", hecke[key][i]);
        str *:= Sprintf("Append(~EVlist, l);\n");
      end for;
      str *:= Sprintf("M`HeckeEigenvalues[key] := EVlist;\n");
    end for;
  end if;
  return str;
end intrinsic;

intrinsic Save(M::ModFrmHilD, filename::MonStgElt) -> MonStgElt
  {}
  str := SaveText(M);
  str *:= Sprintf("\nreturn M;\n");
  Write(filename, str : Overwrite := true);
  return Sprintf("%o written to file\n", filename);
end intrinsic;

/* Load */

intrinsic Load(filename::MonStgElt) -> MonStgElt
  {}
  str := Read(filename);
  M := eval str;
  return M;
end intrinsic;

/*
declare type ModFrmHilDWorkspace [ModFrmHilD];
declare attributes ModFrmHilDWorkspace:
  // stuff asocieted to the base filed field
  Field, // FldNum : totally real field
  Integers, // RngOrd : ZF
  NarrowClassGroup, // GrpAb
  NarrowClassNumber, // RngIntElt
  NarrowClassGroupMap, // Map : GrpAb -> Set of fractional ideals of ZF
  NarrowClassGroupRepresentatives, // SeqEnum[RngOrdElt/RngFracElt]
  DictionaryNarrowClassGroupRepresentatives, // Assoc maps NarrowClassGroupRepresentatives[i] to i

  Precision, // RngIntElt : precision for all expansions with this parent
  Ideals, // SeqEnum[RngOrdIdl]
  Dictionary, // Assoc maps Ideals[i] to i
  MultiplicationTable, // SeqEnum[pairs of integers]
  Representatives, // SeqEnum[nu]
  DictionaryRepresentatives, // Assoc maps Representatives[i] to i

  EigenForms, // an Associative Array (character, weight) --> list of eigenforms spanning eigenspace
  NewForms, // an Associative Array (character, weight) --> list of basis for the NewForms
  OldForms; // an Associative Array (character, weight) --> list of basis for the NewForms
////////// ModFrmHilDWorkspace creation functions //////////

intrinsic ModFrmHilDWorkspaceInitialize() -> ModFrmHilDWorkspace
  {Create an empty ModFrmHilDWorkspace object.}
  M := New(ModFrmHilDWorkspace);
  return M;
end intrinsic;

intrinsic HMFWorkSpace(F::FldNum,, prec::RngIntElt) -> ModFrmHilD
{Generates the space ModFrmHilDWorkspace over F with prec p.}
  assert IsTotallyReal(F);
  assert NumberField(Order(N)) eq F;
  M := ModFrmHilDWorkspaceInitialize();
  // field
  M`Field := F;
  // narrow class group
  Cl, mp := NarrowClassGroup(F);
  M`NarrowClassGroup := Cl;
  M`NarrowClassNumber := #Cl;
  M`NarrowClassGroupMap := mp;
  M`NarrowClassGroupRepresentatives := [ mp(g) : g in Cl ];
  // prec
  M`Precision := prec;

  // ideals
  zero_ideal := ideal<Integers(F)|0>;
  Is := [zero_ideal] cat IdealsUpTo(prec, F);
  M`Ideals := Is;
  dictionary := AssociativeArray();
  for i := 1 to #Is do
    dictionary[Is[i]] := i;
  end for;
  M`Dictionary := dictionary;


  M`EigenForms := AssociativeArray();
  M`NewForms := AssociativeArray();
  M`OldForms := AssociativeArray();

  //TODO equip with multiplication from the gun?
  return M;
end intrinsic;


intrinsic GetEigenforms(W::ModFrmHilDWorkspace, chi::GrpHeckeElt, k::SeqEnum[RngIntElt], ) -> SeqEnum[ModFrmHilDElt]
  {returns the EigenForms for character chi and weight k}
  if not IsDefinedDouble(A, chi, k) then
    ComputeEigenforms(W, chi, k);
  end if;
  return A[chi][k];
end intrinsic;


//auxiliar function to test if A[x][y] is defined
intrinsic IsDefinedDouble(A::Assoc, x::Any, y::Any) -> BoolElt
  {returns if A[x][y] is defined}
  if IsDefined(A,x) then
    if IsDefined(A[x], y) then
      return True;
    end if;
  end if;
  return False;
end intrinsic;
*/
