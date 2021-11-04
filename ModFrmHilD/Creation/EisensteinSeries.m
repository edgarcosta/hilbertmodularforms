// TODO needs testing
// TODO fix normalization at the end
// Eisenstein Series have only been implemented for integral parallel weight
intrinsic EisensteinSeries(Mk::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt) -> ModFrmHilDElt
  {Let aa*bb be the modulus of psi*eta^-1. Return the Eisenstein series E_k(eta,psi) in M_k(aa*bb,eta*psi).}
  // We are following the notation in Section 2.2 of Dasgupta, Darmon, Pollack - Hilbert Modular Forms and the Gross-Stark Conjecture
  M := Parent(Mk);
  k := Weight(Mk);
  N := Level(Mk);
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  require eta*psi eq Character(Mk): "we must have psi*eta = Character(Mk)";
  require aa*bb eq N: "We must have Modulos(eta)*Modulos(psi) = Level(Ml)";
  require #SequenceToSet(k) eq 1: "We only support EisensteinSeries with parallel weight";
  k := k[1];

  CoefficientField := Parent(eta)`TargetRing; // where the character values live

  Haa := HeckeCharacterGroup(aa);
  Hbb := HeckeCharacterGroup(bb);


  // deal with L-values
  if aa eq ideal<Order(aa)|1> then // aa = 1
    prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
    c0aa := LValue_Recognized(M, Mk, prim);
  else
    c0aa := 0;
  end if;
  // k = 1 and bb == 1
  if k eq 1 and bb eq ideal<Order(bb)|1> then
    prim := AssociatedPrimitiveCharacter(eta*psi^(-1));
    c0bb +:= LValue_Recognized(M, Mk, prim);
  else
    c0bb := 0;
  end if;


  nus := ShintaniReps(M);
  coeffs := AssociativeArray();
  bbs := NarrowClassGroupReps(M);
  ZF := Integers(M);
  n := Degree(BaseField(M));
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    // zero term for bb, equation (49) and (50)
    // For them [nn] = \lambda, while we have [nn][bb']=[(1)]
    // Thus we may take tt_lambda = 1/bb'$
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    tt_lambda := bbp^-1;
    coeffs[bb][0] := 2^(-n)*( (eta^(-1))(tt_lambda)*c0aa +  (psi^(-1))(tt_lambda)*c0bb );

    // All other coefficients, equation (48)
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      if not IsZero(nu) then
        coeffs[bb][nu] := &+[eta(nn/rr) * psi(rr) * Norm(rr)^(k - 1) : rr in Divisors(nn)];
      end if;
    end for;
  end for;
  E := HMF(Mk, coeffs);
  // Makes coefficients rational
  if IsIsomorphic(CoefficientField, RationalsAsNumberField()) then
    E := ChangeCoefficientRing(E, Rationals());
  end if;
  // Normalize coefficients
  if not (coeffs[bbs[1]][0] in [0,1]) then
    E := (1/coeffs[bbs[1]][0]) * E;
  end if;
  return E;
end intrinsic;


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
   //LSetPrecision(Lf, 100); // do we need this?
   Lvalue := Evaluate(Lf, 1-k[1]);
   // figure out the right place to recognize
   // i.e., figure out what complex embedding magma used to embed the L-function into CC
   places := InfinitePlaces(CoefficientField);
   for p in PrimesUpTo(Precision(M), BaseField(M)) do
     if #places eq 1 then
       // there is only one place left, so that must be the one
       break;
      end if;
     ap_K := prim(p); // in CoefficientField
     ap_CC := -Coefficients(EulerFactor(Lf, p : Degree := 1))[2];
     // restrict to the places where pl(ap_K) = ap_CC
     places := [pl : pl in places | Evaluate(ap_K, pl) eq ap_CC ];
     i +:=1;
   end for;
   assert #places eq 1;
   pl := places[1];
   CC<I> := ComplexField(Precision(Lvalue));
   return RecognizeOverK(CC!Lvalue, CoefficientField, pl, false);
 end intrinsic;
