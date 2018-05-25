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


