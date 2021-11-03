// TODO needs testing
// TODO fix normalization at the end
// Eisenstein Series have only been implemented for integral parallel weight
intrinsic EisensteinSeries(Mk::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt) -> ModFrmHilDElt
  {Let aa*bb be the modulus of psi*eta^-1. Return the Eisenstein series E_k(eta,psi) in M_k(aa*bb,eta*psi).}
  // We are following the notation in Section 2.2 of Dasgupta, Darmon, Pollack - Hilbert Modular Forms and the Gross-Stark Conjecture
  M := Parent(Mk);
  k := Weight(Mk);
  N := Level(Mk);
  vprintf HilbertModularForms: "eta * psi = %o\n", eta*psi;
  vprintf HilbertModularForms: "Character(Mk) = %o\n", Character(Mk);
  vprintf HilbertModularForms: "eta*psi eq Character(Mk) = %o\n", eta*psi eq Character(Mk);
  vprintf HilbertModularForms: "Parent(eta*psi) = %o Parent(Character(Mk)) = %o\n", Parent(eta*psi), Parent(Character(Mk));
  require eta*psi eq Character(Mk): "we must have psi*eta = Character(Mk)";
  vprintf HilbertModularForms: "EisensteinSeries(k=%o, N=%o, eta=%o, psi=%o)\n", k, N, eta, psi;
  Cl := NarrowClassGroup(M);
  mp := NarrowClassGroupMap(M);
  require #SequenceToSet(k) eq 1: "We only support EisensteinSeries with parallel weight";
  k := k[1];

  X := Parent(eta); Y := Parent(psi);
  CoefficientField := X`TargetRing; // where the character values live

  n := Degree(BaseField(M));
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  assert aa*bb eq N;
  vprintf HilbertModularForms: "aa = %o\n", aa;
  vprintf HilbertModularForms: "bb = %o\n", bb;
  Haa := HeckeCharacterGroup(aa);
  Hbb := HeckeCharacterGroup(bb);

  nus := ShintaniReps(M);
  coeffs := AssociativeArray();
  bbs := NarrowClassGroupReps(M);
  ZF := Integers(M);
  for tt in bbs do
    coeffs[tt] := AssociativeArray();
    // a0 term for tt
    // using Dasgupta, Darmon, Pollack - Hilbert Modular Forms and the Gross-Stark Conjecture
    coeffs[tt][0*ZF] := 0;
    c0 := 0;
    if aa eq ideal<Order(aa)|1> then // aa = 1
      prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
      Lvalue := LValue_Recognized(M, Mk, prim);
      c0 +:= (eta^(-1))(tt)*Lvalue;
    end if;
    // k = 1 and bb == 1
    if k eq 1 and bb eq ideal<Order(bb)|1> then
        prim := AssociatedPrimitiveCharacter(eta*psi^(-1));
        c0 +:= (psi^(-1))(tt) * LValue_Recognized(M, Mk, prim);
    end if;
    coeffs[tt][0*ZF] := 2^(-n) * c0;

    // All other coefficients, equation (48)
    for nn in IdealsByNarrowClassGroup(M)[tt] do
      if not IsZero(nn) then
        coeffs[tt][nn] := &+[eta(nn/rr)*psi(rr)*Norm(rr^(k - 1)) : rr in Divisors(nn)];
      end if;
    end for;
    // Makes coefficients rational
    if IsIsomorphic(CoefficientField, RationalsAsNumberField()) then
      for nn in IdealsByNarrowClassGroup(M)[tt] do
        coeffs[tt][nn] := Rationals()!coeffs[tt][nn];
      end for;
    end if;
  end for;
  E := HMF(Mk, coeffs : CoeffsByIdeals:=true);
  // Normalize coefficients
  if not (coeffs[bbs[1]][0*ZF] in [0,1]) then
    E := (1/coeffs[bbs[1]][0*ZF]) * E;
  end if;
  return E;
end intrinsic;

// TODO finish this and use in EisensteinSeries intrinsic

//Toolbox function to use in the Eisenstein series function--gives us an L value
intrinsic LValue_Recognized(M::ModFrmHilDGRng, Mk::ModFrmHilD, prim::GrpHeckeElt) -> FldNumElt
   {This is a toolbox function to compute L values in the right space}
    N:=Level(Mk);
    k:=Weight(Mk);

   // Lf := LSeries(prim : Precision := 50);
   // TODO clean up precision
   // Maybe a separate function to compute L-values?
   CoefficientField := Parent(prim)`TargetRing; // where the character values live
   Lf := LSeries(prim : Precision := 100);
   LSetPrecision(Lf, 100); // do we need this?
   Lvalue := Evaluate(Lf, 1-k[1]);
   // figure out the right place */
   primes := PrimesUpTo(Precision(M), BaseField(M));
   places := InfinitePlaces(CoefficientField);
   i := 1;
   while #places gt 1 and i le #primes do
     pp := primes[i];
     app := prim(pp);
     places := [pl : pl in places | Evaluate(app, pl) eq -Coefficients(EulerFactor(Lf, pp : Degree := 1))[2] ];
     // why is this the right way to find the correct place to recognize? */
     i +:=1;
   end while;
   assert #places eq 1;
   pl := places[1];
   CC<I> := ComplexField(Precision(Lvalue));
   return RecognizeOverK(CC!Lvalue, CoefficientField, pl, false);
 end intrinsic;
