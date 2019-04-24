/*****
ModFrmHilDElt
*****/

////////// ModFrmHilDElt attributes //////////

declare type ModFrmHilDElt;
declare attributes ModFrmHilDElt:
  Parent, // ModFrmHilD
  Coefficients, // Coefficients[bb] = coeffs_bb where coeffs_bb[nu] = a_(bb,nu) = a_(nu)*bb^-1
  CoefficientField; // CoefficientField = where the coefficients live (does this depend on bb?)

////////// ModFrmHilDElt fundamental intrinsics //////////

//By Norm 
intrinsic Print(f::ModFrmHilDElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    bbs := NarrowClassGroupReps(M);
    k := Weight(Mk);
    prec := Precision(M);
    coeffs := Coefficients(f);
    N := Level(Mk);
    printf "Hilbert modular form expansion with precision %o.\n", prec;
    printf "Level: (Norm, Ideal) = (%o, %o)\n", Norm(N),  Generators(N);
    printf "Weight: %o\n", k;
    printf "Parent: %o\n", Mk;
    for bb in bbs do
      coeffs_bb := coeffs[bb];
      printf "Coefficients for ideal class bb = %o\n", bb;
      printf "\n\t(Ideal)  |--->   a_nn = a_(nu)*bb^-1";
      for nn in IdealsByNarrowClassGroup(M)[bb] do
        printf "\n\t(%o)  |--->   %o", IdealOneLine(nn), coeffs_bb[nn];
      end for;
      printf "\n\n";
    end for;
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

/*
//By Trace
intrinsic Print(f::ModFrmHilDElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    M := Parent(f);
    bbs := NarrowClassGroupReps(M);
    k := Weight(f);
    prec := Precision(f);
    coeffs := Coefficients(f);
    N := Level(f);
    printf "Hilbert modular form expansion with precision %o.\n", prec;
    printf "Level: (Norm, Ideal) = (%o, %o)\n", Norm(N),  Generators(N);
    printf "Weight: %o\n", k;
    printf "Parent: %o\n", M;
    for bb in bbs do
      coeffs_bb := coeffs[bb];
      printf "Coefficients for ideal class bb = %o\n", bb;
      printf "\n\t(Trace, nu)  |--->   a_nu = a_(nu)*bb^-1";
      for t in Keys(ShintaniReps(M)[bb]) do
        for nu in ShintaniReps(M)[bb][t] do
          assert Trace(nu) eq t;
          printf "\n\t(%o, %o)  |--->   %o", t,  nu, coeffs_bb[nu];
        end for;
      end for;
      printf "\n\n";
    end for;
  elif level eq "Magma" then
    printf "%o", PercentM(f);
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

*/

////////// ModFrmHilDElt access to attributes //////////

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic BaseField(f::ModFrmHilDElt) -> FldNum
  {returns base field of parent of f.}
  return BaseField(Parent(Parent(f)));
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {returns level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic Precision(f::ModFrmHilDElt) -> RngIntElt
  {returns precision of parent of f.}
  return Precision(Parent(Parent(f)));
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, nn::RngOrdIdl) -> Any
  {}
  mp := NarrowClassGroupMap(Parent(Parent(f)));
  rep := mp(nn@@mp);
  return Coefficients(f)[rep][nn];
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> Any
  {}
  return f`Coefficients;
end intrinsic;

intrinsic CoefficientField(f::ModFrmHilDElt) -> Any
  {}
  return f`CoefficientField;
end intrinsic;

////////// ModFrmHilDElt creation functions //////////

intrinsic ModFrmHilDEltInitialize() -> ModFrmHilDElt
  {Create an empty ModFrmHilDElt object.}
  f := New(ModFrmHilDElt);
  return f;
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

intrinsic HMF(Mk::ModFrmHilD, coeffs::Assoc) -> ModFrmHilDElt
  {WARNING: user is responsible for coefficients besides some basic structural assertions. Note: coeffs[bb][nu] = a_(bb, nu) = a_(nu)*(bb)^-1}
  M := Parent(Mk);
  N := Level(Mk);
  k := Weight(Mk);
  // check coeffs[bb] defined for each ideal class bb
  if #Keys(coeffs) ne #NarrowClassGroupReps(M) then
    error "Associative array of coefficients should be indexed by ideal classes";
  end if;
  bbs := NarrowClassGroupReps(M);
  coeffs_as_sequence := []; // to assert all coefficients have the same parent
  for bb in bbs do
    // check coeffs[bb] has keys equal IdealsByNarrowClassGroup(M)[bb]
    assert Set(IdealsByNarrowClassGroup(M)[bb]) eq Keys(coeffs[bb]);
    // check coeffs[bb][n] has a value for every n in IdealsByNarrowClassGroup(M)[bb]
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      assert IsDefined(coeffs[bb], nn);
    end for;
    key := Random(Keys(coeffs[bb]));
    Append(~coeffs_as_sequence, coeffs[bb][key]); // if value of coeffs[bb][key] differs then error here trying to append
  end for;
  // make the HMF
  f := ModFrmHilDEltInitialize();
  f`Parent := Mk;
  f`Coefficients := coeffs;
  f`CoefficientField := FieldOfFractions(Parent(coeffs_as_sequence[1]));
  return f;
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs_bb := AssociativeArray();
    for nu in IdealsByNarrowClassGroup(M)[bb] do
      coeffs_bb[nu] := 0;
    end for;
    coeffs[bb] := coeffs_bb;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;

intrinsic HMFIdentity(M::ModFrmHilDGRng) -> ModFrmHilDElt
  {create one ModHilFrmDElt of weight zero.}
  n := Degree(BaseField(M));
  Mk := HMFSpace(M, [0 : i in [1..n]]);
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs_bb := AssociativeArray();
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      if IsZero(nn) then
        coeffs_bb[nn] := 1;
      else
        coeffs_bb[nn] := 0;
      end if;
    end for;
    coeffs[bb] := coeffs_bb;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;

////////// ModFrmHilDElt accessing and setting coefficients //////////

/* intrinsic GetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl) -> RngElt */
/*   {returns a_I} */
/*   return Coefficients(f)[Dictionary(f)[I]]; */
/* end intrinsic; */

/* intrinsic SetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl, c::RngElt) */
/*   {sets a_I to c} */
/*   f`Coefficients[Dictionary(f)[I]] := c; */
/* end intrinsic; */

/* intrinsic GetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt) -> RngElt */
/*   {returns a_nu} */
/*   if not assigned Parent(f)`Representatives then */
/*     error "You must first equip the space with a multiplication table"; */
/*   end if; */
/*   return Coefficients(f)[DictionaryRepresentatives(f)[nu]]; */
/* end intrinsic; */

/* intrinsic SetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt, c::RngElt) */
/*   {sets a_nu to c} */
/*   if not assigned Parent(f)`Representatives then */
/*     error "You must first equip the space with a multiplication table"; */
/*   end if; */
/*   f`Coefficients[DictionaryRepresentatives(f)[nu]] := c; */
/* end intrinsic; */

/* intrinsic GetCoefficientsIdeal(f::ModFrmHilDElt) -> Assoc */
/*   {given a ModFrmHilDElt, return associative array of coefficients on the ideals.} */
/*   coeffs := Coefficients(f); */
/*   ideals := Ideals(f); */
/*   result := AssociativeArray(); */
/*   for i := 1 to #ideals do */
/*     result[ideals[i]] := coeffs[i]; */
/*   end for; */
/*   return result; */
/* end intrinsic; */

/* intrinsic GetCoefficientsRepresentatives(f::ModFrmHilDElt) -> Assoc */
/*   {given a ModFrmHilDElt, return associative array of coefficients on the representatives.} */
/*   if not assigned Parent(f)`Representatives then */
/*     error "You must first equip the space with a multiplication table"; */
/*   end if; */
/*   coeffs := Coefficients(f); */
/*   reps := Representatives(f); */
/*   result := AssociativeArray(); */
/*   for i := 1 to #reps do */
/*     result[reps[i]] := coeffs[i]; */
/*   end for; */
/*   return result; */
/* end intrinsic; */


////////////// ModFrmHilDElt: Coercion /////////////////////////

// ChangeRing?
// Coerces HMF coefficients a_n in a ring R
intrinsic '!'(R::Rng, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f such that a_I := R!a_I}
  M := Parent(f);
  bbs := NarrowClassGroupReps(M);
  coeffs := Coefficients(f);
  new_coeffs := AssociativeArray();
  for bb in bbs do
    for nn in Keys(coeffs[bb]) do
      new_coeffs[bb][nn] := R!coeffs[bb][nn];
    end for;
  end for;
  return HMF(Parent(f), Level(f), Weight(f), new_coeffs);
end intrinsic;

//FIXME NarrowClassNumber >1 - Ben
intrinsic IsCoercible(M::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if ISA(Type(f), RngElt) then
    P := Parent(f);
    N := 1*Integers(M); // FIXME only level 1 for now
    coeffs := AssociativeArray();
    for bb in NarrowClassGroupReps(M) do
      coeffs_bb := AssociativeArray();
      for nu in IdealsByNarrowClassGroup(M)[bb] do
        if IsZero(nu) then
          coeffs_bb[nu] := f;
        else
          coeffs_bb[nu] := 0;
        end if;
      end for;
      coeffs[bb] := coeffs_bb;
    end for;
    h := #NarrowClassGroupReps(M);
    k := [0 : c in [1..h]];
    return true, HMF(M, N, k, coeffs);
  end if;
  if Type(f) ne ModFrmHilDElt then
    return false;
  end if;
  if Parent(f) eq M then
    return true, f;
  elif (BaseField(M) eq BaseField(f)) and (Precision(M) eq Precision(f)) then
    return true, HMF(M, Level(f), Weight(f) , Coefficients(f));
  else
    return false;
  end if;
end intrinsic;

/*
intrinsic '!'(M::ModFrmHilD, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f with parent M}
  nn := Level(M);
  nnf := Level(f);
  assert nn subset nnf; // nnf divides nn
  coeffs := Coefficients(f);
  return HMF(M, Weight(f) , coeffs);
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

//////////  ModFrmHilDElt: Galois action on Coefficients ////////// 

//TODO:
//Tests:
// - Apply Hecke on a Galois Orbit, and see that it doesn't move
// - Apply Hecke to a Eisensten series, and check that is a multiple
// - Apply Hecke to a Theta series, and see if we get the whole space

intrinsic GaloisOrbit(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt] 
  {returns the full Galois orbit of a modular form} 
  M := Parent(f); 
  k := Weight(f); 
  K := CoefficientField(f);
  G, Pmap, Gmap := AutomorphismGroup(K); 
  bbs := NarrowClassGroupReps(M);
  result := []; 
  for g in G do 
    coeff := Coefficients(f); 
    for bb in bbs do
      for nn in Keys(Coefficients(f)[bb]) do
        coeff[bb][nn] := Gmap(g)(coeff[bb][nn]);
      end for;
    end for;
    Append(~result, HMF(M, Level(f), k, coeff)); 
  end for; 
  return result; 
end intrinsic; 


intrinsic GaloisOrbitDescent(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt] 
  {returns the full Galois orbit of a modular form over Q} 
  M := Parent(f); 
  k := Weight(f); 
  result := [];
  bbs := NarrowClassGroupReps(M);
  CoefficientsField := CoefficientField(f);
  for b in Basis(CoefficientsField) do
    coeff := Coefficients(f);
    for bb in bbs do
      for nn in Keys(Coefficients(f)[bb]) do 
        coeff[bb][nn] := Trace(b * coeff[bb][nn]);
      end for;
    end for;
    Append(~result, HMF(M, Level(f), k, coeff)); 
  end for;
  return result; 
end intrinsic; 



///////////// ModFrmHilDElt: Hecke Operators ////////////////


// TODO: narrow>1
/* intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl : Basis:=[]) -> ModFrmHilDElt */
/*   {returns T(n)(f) for the trivial character} */
/*   return HeckeOperator(f, nn, HeckeCharacterGroup(Level(f))! 1 : Basis:=Basis); */
/* end intrinsic; */


// TODO: narrow>1
/* intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl, chi::GrpHeckeElt : Basis:= []) -> ModFrmHilDElt */
/*   {returns T(n)(f) with loss of precision. If a basis for the space is provided, returns T(n)(f) without loss of precision} */
/*   M := Parent(f); */
/*   fcoeffs := Coefficients(f); */
/*   ideals := Ideals(f); */
/*   dict := Dictionary(f); */
/*   ZC := Parent(fcoeffs[1]); */
/*   k0 := Max(Weight(f)); */
/*   prec:=Precision(M); */
/*   //We work in smaller precision and obtain a function the space of precision Prec/Norm(nn) */
/*   idealssmallprec:=[ideals[1]]; */
/*   for x:=2 to #ideals do */
/*     if Norm(ideals[x]) le prec/Norm(nn) then */
/*       idealssmallprec:= idealssmallprec cat [ideals[x]]; */
/*     end if; */
/*   end for; */
/*   coeffssmallprec := [ZC!0 : i in [1..#idealssmallprec]]; */
/*   for i:=1 to #idealssmallprec do */
/*     c := 0; */
/*     // loop over divisors */
/*     // Formula 2.23 in Shimura - The Special Values of the zeta functions associated with Hilbert Modular Forms */
/*     for aa in Divisors(ideals[i] + nn) do */
/*       c +:= chi(aa) * Norm(aa)^(k0 - 1) * fcoeffs[ dict[ aa^(-2) * (ideals[i] * nn)]]; */
/*       end for; */
/*     coeffssmallprec[i] := c; */
/*     end for; */
/*   if #Basis ne 0 then //if provided a basis, we reconstruct the form to the same precision */
/*     smallprecbasis:=[]; */
/*     for g in Basis do */
/*       Append(~smallprecbasis, [Coefficients(g)[i] : i in [1..#idealssmallprec]]); */
/*     end for; */
/*     LinComb:=LinearDependence([coeffssmallprec] cat smallprecbasis); */
/*     if ISA(Type(LinComb), RngIntElt) or #Rows(LinComb) ne 1 then */
/*       return "Error: either precision is too small, or the sequence provided is not a basis"; */
/*     end if; */
/*     g:=0*f; */
/*     for i:=2 to #Basis+1 do */
/*       g:=g-LinComb[1][i]*Basis[i-1]; */
/*     end for; */
/*     return g; */
/*   end if; */
/*   if #Basis eq 0 then */
/*     M1:=HMFSpace(BaseField(M), Floor(prec/Norm(nn))); */
/*     print "Warning: the Hecke operator calculation decreases precision to ", */
/*     Floor(prec/Norm(nn)); */
/*     return HMF(M1, Level(f), Weight(f), coeffssmallprec); */
/*   end if; */
/* end intrinsic; */

////////// ModFrmHilDElt: Arithmetic //////////

//TODO make zero HMF universal so it can be added/multiplied to any HMF

intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
  {compares Parent, Weight, and Coefficients.}
  M := Parent(f);
if Parent(f) ne Parent(g) then return false; end if;
  if Weight(f) ne Weight(g) then return false; end if;
if Keys(Coefficients(f)) ne Keys(Coefficients(g)) then return false; end if; 
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
	   if Keys(Coefficients(f)[bb]) ne Keys(Coefficients(g)[bb]) then return false; end if;
    for nn in Keys(Coefficients(f)[bb]) do
      if Coefficients(f)[bb][nn] ne Coefficients(g)[bb][nn] then return false; end if;
    end for;
  end for;
  return true;
end intrinsic;


intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  N := Level(f);
  M := Parent(f);
  k := Weight(f);
  coeffs := Coefficients(f);
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do 
    F := CoefficientField(f);

assert c in Integers(F);

    for nn in Keys(Coefficients(f)[bb]) do
      coeffs[bb][nn] := F!(c * Coefficients(f)[bb][nn]);
    end for;
  end for;
  return HMF(M, N, k, coeffs);
end intrinsic;


intrinsic '*'(c::Any, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by some scalar c.}
  N := Level(f);
  M := Parent(f);
  k := Weight(f);
  coeffs := Coefficients(f);
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do 
    F := CoefficientField(f);
    assert c in F;
    for nn in Keys(Coefficients(f)[bb]) do
      coeffs[bb][nn] := F!(c * Coefficients(f)[bb][nn]);
    end for;
  end for;
  return HMF(M, N, k, coeffs);
end intrinsic;


intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g.}
  // Currently returns the lowest precision of the forms 
  // assert Parent(f) eq Parent(g);
  assert Level(f) eq Level(g);
  assert Weight(f) eq Weight(g);
  N := Level(f) meet Level(g);
  M := Parent(f);
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
  return HMF(M, N, k, new_coeffs);
end intrinsic;

intrinsic '-'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f-g.}
  return f + (-1)*g;
end intrinsic;

// TODO only works when k has even weight
// TODO for varied precision
intrinsic '*'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f*g}
  N := Level(f) meet Level(g);
M := Parent(Parent(f));
  k := [ Weight(g)[i] + Weight(f)[i] : i in [1..#Weight(g)] ];

assert Parent(Parent(f)) eq Parent(Parent(g));
  MTable := MultiplicationTables(M);
  bbs := NarrowClassGroupReps(M);
  new_coeff := AssociativeArray();
  for bb in bbs do
    new_coeff[bb] := AssociativeArray();
ZF := Integers(CoefficientField(f));
    for nn in Keys(Coefficients(f)[bb]) do
	   c := 0;
	     c := ZF!0;
      for pair in MTable[bb][nn] do
        c +:= Coefficients(f)[bb][ pair[1] ] * Coefficients(g)[bb][ pair[2] ];
      end for;
      new_coeff[bb][nn] := c;
    end for;
  end for;
  return HMF(M, N, k, new_coeff);
end intrinsic;

//Dictionary would great here! Make linear algebra much easier
intrinsic '/'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f/g}
  N := Level(f) meet Level(g);
  M := Parent(f);
  assert Parent(f) eq Parent(g);
  if not assigned M`MultiplicationTables then
    assert HMFEquipWithMultiplication(M);
  end if;
  MTable := MultiplicationTables(M);
  coeffs := AssociativeArray();
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    // Linear Algebra Ax = B 
    A := [];
    B := [];
    Ideals := IdealsByNarrowClassGroup(M)[bb];
    for nn in Ideals do
      Append(~B,Coefficients(f)[bb][nn]);
      F := CoefficientField(g);
      A_row_nn := [F!0 : i in [1..#Ideals]];
      for pair in MTable[bb][nn] do
        A_row_nn[Index(Ideals,pair[2])] +:= Coefficients(g)[bb][pair[1]];
      end for;
      Append(~A,A_row_nn);
    end for;
    S := Solution(Transpose(Matrix(A)), Vector(B));
    for nn in Ideals do
      coeffs[bb][nn] := S[Index(Ideals,nn)];
    end for;
  end for;
  kf := Weight(f);
  kg := Weight(g);
  k := [ kf[i] - kg[i] : i in [1..#kf] ];
  return HMF(M, N, k, coeffs);
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
  {finds a small non-trivial integral linear combination between components of v. If none can be found return 0.}
  M := Matrix( [ elt : elt in list] );
  B := Basis(Kernel(M));
  if #B ne 0 then return [Eltseq(i) : i in Rows(Matrix(LLL(B)))]; else return []; end if;
end intrinsic;

//TODO add optional flag to limit the number of coefficients
//TODO make outputs to be of the same type
//TODO take working precision
intrinsic LinearDependence(List::SeqEnum[ModFrmHilDElt] ) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v. If none can be found return 0.}
  M := Parent(List[1]);
  bbs := NarrowClassGroupReps(M);
  CoeffLists := [[] : i in [1..#List]];
  for bb in bbs do
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      for i in [1..#List] do
        Append(~CoeffLists[i], Coefficients(List[i])[bb][nn]);
      end for;
    end for;
  end for; 
  return LinearDependence(CoeffLists);
end intrinsic;


////////// ModFrmHilDElt: M_k(N1) -> M_k(N2) //////////

//Todo: Verify Correctness. Reference?
intrinsic Inclusion(f::ModFrmHilDElt, N2::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f of level N1 and produces list of all inclusions of f into the space of level N2} 
  M := Parent(f);
  N1 := Level(f);
  k := Weight(f);
  assert N1 subset N2; // To contain is to divide
  bbs := NarrowClassGroupReps(M);
  mp := NarrowClassGroupMap(M);
  IncludedForms := [];
  for ee in Divisors(N2/N1) do 
    // 1 new form for each divisor
    coeff := Coefficients(f);
    for bb in bbs do
      bbee := mp((bb*ee)@@mp); // Representative of narrow class bbee := bb*ee
      for nn in Keys(coeff[bb]) do
        if nn*ee in Keys(coeff[bbee]) then
          coeff[bbee][nn*ee] := coeff[bb][nn];
        else 
          coeff[bbee][nn] := 0;
        end if;
      end for;
    end for;
    Append(~IncludedForms, HMF(M, N2, k, coeff));
  end for;
  return IncludedForms;
end intrinsic;


////////// ModFrmHilDElt: swap map //////////

/* intrinsic Swap(f::ModFrmHilDElt) -> ModFrmHilDElt */
/*   {given a hilbert modular form f(z_1, z_2), returns the swapped form f(z_2,z_1)} */
/*   M:=Parent(f); */
/*   g:=M!(1*f); */
/*   F:=BaseField(M); */
/*   ZF<w>:=Integers(F); */
/*   ideals:=Ideals(f); */
/*   for i in ideals do */
/*     x:=GetCoefficient(f, Conjugate(i)); */
/*     SetCoefficient(g, i, x); */
/*   end for; */
/*   return g; */
/* end intrinsic; */
