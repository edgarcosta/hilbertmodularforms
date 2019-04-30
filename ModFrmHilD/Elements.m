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
  k := [0 : i in [1..Degree(BaseField(M))]];
  Mk := HMFSpace(M, k);
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

intrinsic IsCoercible(Mk::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if Type(f) ne ModFrmHilDElt then
    return false;
  else // f is an HMF so has a chance to be coercible
    M := Parent(Mk); // graded ring associated to Mk
    Mkf := Parent(f); // space of HMFs associated to f
    Mf := Parent(Mkf); // graded ring associated to f
    if M ne Mf then
      return false;
    else // at least the graded rings match up
      test1 := Weight(Mk) eq Weight(Mkf);
      test2 := Level(Mk) eq Level(Mkf);
      test3 := Character(Mk) eq Character(Mkf);
      if test1 and test2 and test3 then // all tests must be true to coerce
        return true, HMF(Mk, Coefficients(f));
      else
        return false;
      end if;
    end if;
  end if;
end intrinsic;

intrinsic '!'(Mk::ModFrmHilD, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f with parent M}
  coeffs := Coefficients(f);
  return HMF(Mk, coeffs);
end intrinsic;

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
fSpace := Parent(f);
M := Parent(fSpace);
k := Weight(fSpace);
M := Parent(Parent(f));

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
Append(~result, HMF(fSpace,coeff));
  end for;
  return result;
end intrinsic;


intrinsic GaloisOrbitDescent(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form over Q}
fSpace := Parent(f);
M := Parent(fSpace);
k := Weight(fSpace);

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
Append(~result, HMF(fSpace,coeff));
  end for;
  return result;
end intrinsic;



///////////// ModFrmHilDElt: Hecke Operators ////////////////



 intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl) -> ModFrmHilDElt
   {returns T(n)(f) for the trivial character}
   return HeckeOperator(f, nn, HeckeCharacterGroup(Level(f))! 1);
 end intrinsic;


 intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl, chi::GrpHeckeElt) -> Assoc
   {returns associative array with coefficients for T(nn)(f) with loss of precision.}
   Mk := Parent(f);
   M :=Parent(Mk);
   ZF:=Integers(BaseField(M));
   fcoeffs := Coefficients(f);
   ideals := IdealsByNarrowClassGroup(M);
   k0 := Max(Weight(f));
   //We work in smaller precision and obtain a function the space of precision Prec/Norm(nn)
   coeffsTnnf := AssociativeArray();
   //for x:=2 to #ideals do
    // if Norm(ideals[x]) le prec/Norm(nn) then
    //   idealssmallprec:= idealssmallprec cat [ideals[x]];
    // end if;
   //end for;
   for bb in  NarrowClassGroupReps(M) do
    coeffsTnnf[bb] := AssociativeArray();
    for I in IdealsByNarrowClassGroup(M)[bb] do
      c :=0;
        allDivisors:=true; //keeps track if all the coefficients in the sum for an ideal are defined
        // loop over divisors
        // Formula 2.23 in Shimura - The Special Values of the zeta functions associated with Hilbert Modular Forms
        for aa in Divisors(I + nn) do
          if aa^(-2) * (I* nn) notin AllIdeals(M) then
           allDivisors:=false ; break; //stop if coefficient for divisor is not defined
             else
              if I eq 0*ZF then c+:= chi(aa) * Norm(aa)^(k0 - 1) * Coefficients(f)[bb][I]; //takes care if the coefficients for the zero ideal are different
                else c+:= chi(aa) * Norm(aa)^(k0 - 1) * Coefficient(f, ZF !! (aa^(-2) * (I* nn)));
                  end if;
       end if;
          end for;
        if allDivisors eq true then coeffsTnnf[bb][I] := c;
         else break; //stop if not all coefficients for the divisors in the sum for an ideal are defined
         end if;
        end for;
    end for;
    return coeffsTnnf;
 end intrinsic;

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

Space := Parent(f);
GrRing := Parent(Space);
  coeffs := Coefficients(f);
  bbs := NarrowClassGroupReps(GrRing);
  for bb in bbs do
    F := CoefficientField(f);

assert c in F;
//assert c in Integers(F);

    for nn in Keys(Coefficients(f)[bb]) do
      coeffs[bb][nn] := F!(c * Coefficients(f)[bb][nn]);
    end for;
  end for;
return HMF(Space,coeffs);
end intrinsic;


intrinsic '*'(c::Any, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by some scalar c.}
Space := Parent(f);
GrRing := Parent(Space);
  coeffs := Coefficients(f);
  bbs := NarrowClassGroupReps(GrRing);
  for bb in bbs do
    F := CoefficientField(f);
    assert c in F;
    for nn in Keys(Coefficients(f)[bb]) do
      coeffs[bb][nn] := F!(c * Coefficients(f)[bb][nn]);
    end for;
  end for;
return HMF(Space,coeffs);
end intrinsic;


intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g.}
  // Currently returns the lowest precision of the forms
  // assert Parent(f) eq Parent(g);
fSpace := Parent(f); gSpace := Parent(g);
fGrRing := Parent(fSpace); gGrRing := Parent(gSpace);

assert fSpace eq gSpace;


M := fGrRing;
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
return HMF(HMFSpace(M, k, Level(fSpace), Character(fSpace)), new_coeffs);
end intrinsic;

intrinsic '-'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f-g.}
  return f + (-1)*g;
end intrinsic;

// TODO only works when k has even weight
// TODO for varied precision
intrinsic '*'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f*g}
  fSpace := Parent(f); gSpace := Parent(g);
  fGrRing := Parent(fSpace); gGrRing := Parent(gSpace);
  assert fGrRing eq gGrRing;
  newLevel := Level(fSpace) meet Level(gSpace);
  newCharacter := Character(fSpace)*Character(gSpace);
  k := [ Weight(gSpace)[i] + Weight(fSpace)[i] : i in [1..#Weight(gSpace)] ];
  MTable := MultiplicationTables(fGrRing);
  bbs := NarrowClassGroupReps(fGrRing);
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
  return HMF(HMFSpace(fGrRing, k, newLevel, newCharacter), new_coeff);
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
   M := Parent(Parent(f));
   g := HMFIdentity(M);
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
  M := Parent(Parent(List[1]));
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
intrinsic Inclusion(f::ModFrmHilDElt, Sp::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f of level N1 and produces list of all inclusions of f into the space of level N2}
  fSpace := Parent(f);
  M := Parent(fSpace);
  N1 := Level(fSpace);
  k := Weight(fSpace);
  N2 := Level(Sp);
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
  Append(~IncludedForms, HMF(Sp, coeff));
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
