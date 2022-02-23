intrinsic EisensteinSeries(
  Mk::ModFrmHilD,
  eta::GrpHeckeElt,
  psi::GrpHeckeElt
  :
  dd:=1,
  Coefficients:=false
  ) -> ModFrmHilDElt
  {Return the Eisenstein series E_k(eta,psi)(dd*z) in M_k(N, eta*psi), where aa*bb*dd | N and aa, bb is the modulus of eta, psi, respectively.
  One may pass the coefficients matchng the output of EisensteinCoefficients, to skip calling it.
  }
  M := Parent(Mk);
  k := Weight(Mk);
  N := Level(Mk);
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  require N subset aa*bb*dd: "Modulos(eta)*Modulos(psi)*dd must divide Level(Mk)";
  X := Parent(Character(Mk));
  require IsTrivial(eta*psi*Character(Mk)^-1): Sprintf("we must have psi*eta = Character(Mk), %o, %o", Parent(eta*psi), (Parent(Character(Mk))));
  require #SequenceToSet(k) eq 1: "the weight is not parallel, there are no Eisenstein Series in this case";
  k := k[1];


  ZF := Integers(M);
  ddinv := dd^-1;
  if Coefficients cmpeq false then
    ideals := [ ZF !! (nn*ddinv) : nn in Ideals(M) | IsIntegral(nn*ddinv) ];
    Coefficients := EisensteinCoefficients(M, Weight(Mk), eta, psi, ideals);
  end if;

  constant_term, coeffs_ideals := Explode(Coefficients);
  coeffs := AssociativeArray();
  n := Degree(BaseField(M));
  for bb in NarrowClassGroupReps(M) do
    ddbb := NarrowClassRepresentative(M,dd*bb);
    coeffs[ddbb] := AssociativeArray();
    coeffs[ddbb][0] := constant_term[bb];

    // All other coefficients, equation (48)
    for nu->nn in ShintaniRepsIdeal(M)[ddbb] do
      if not IsZero(nu) then
        mm := nn*ddinv;
        if IsIntegral(mm) then
          mm := ZF !! mm;
          coeffs[ddbb][nu] := coeffs_ideals[mm];
        else
          coeffs[ddbb][nu] := 0;
        end if;
      end if;
    end for;
  end for;
  E := HMF(Mk, coeffs);
  return E;
end intrinsic;



intrinsic EisensteinCoefficients(
  M::ModFrmHilDGRng,
  Weight::SeqEnum[RngIntElt],
  eta::GrpHeckeElt,
  psi::GrpHeckeElt,
  ideals::SeqEnum[RngOrdIdl]
  ) -> Tup
  {return two associative arrays, the first one with constant coefficients indexed by bb, and the other with a_nn with nn in ideals}


  // We are following the notation in Section 2.2 of Dasgupta, Darmon, Pollack - Hilbert Modular Forms and the Gross-Stark Conjecture
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  require #SequenceToSet(Weight) eq 1: "We only support EisensteinSeries with parallel weight";
  k := Weight[1];

  //Set the coefficient field to be the common field for eta and psi.
  lcm := LCM(Order(eta), Order(psi));
  L<z> := CyclotomicField(lcm);
  SetTargetRing(~eta, z);
  SetTargetRing(~psi, z);

  // deal with L-values
  if IsOne(aa) then // aa = 1
    prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
    SetTargetRing(~prim, z);
    c0aa := LValue_Recognized(M, k, prim);
  else
    c0aa := 0;
  end if;
  // k = 1 and bb == 1
  if k eq 1 and IsOne(bb) then
    prim := AssociatedPrimitiveCharacter(eta*psi^(-1));
    SetTargetRing(~prim, z);
    c0bb := LValue_Recognized(M, k, prim);
  else
    c0bb := 0;
  end if;

  constant_term := AssociativeArray();
  n := Degree(BaseField(M));
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
    constant_term[bb] := AssociativeArray();
    // zero term for bb, equation (49) and (50)
    // For them [nn] = \lambda, while we have [nn][bb']=[(1)]
    // Thus we may take tt_lambda = 1/bb'$
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    tt_lambda := bbp^-1;
    constant_term[bb] := 2^(-n)*( (eta^(-1))(tt_lambda)*c0aa +  (psi^(-1))(tt_lambda)*c0bb );
  end for;


  // Normalize coefficients
  bb1 := bbs[1];
  c0inv := (not (constant_term[bb1] in [0,1])) select (1/constant_term[bb1]) else 1;
  for bb->c in constant_term do
    constant_term[bb] *:= c0inv;
  end for;
  assert constant_term[bb1] in [0,1];


  coeffs := AssociativeArray();
  for nn in ideals do
    if not IsZero(nn) then
      coeffs[nn] := c0inv * &+[eta(nn/rr) * psi(rr) * Norm(rr)^(k - 1) : rr in Divisors(nn)];
    end if;
  end for;

  // reduce field of definition
  if Degree(L) eq 1 then
    Lsub := Rationals();
  else
    Lsub := sub<L | [elt : elt in (Values(coeffs) cat Values(constant_term))]>;
  end if;
  if L ne Lsub then
    for nn->c in coeffs do
      coeffs[nn] := Lsub!c;
    end for;
    for bb->c in constant_term do
      constant_term[bb] := Lsub!c;
    end for;
  end if;

  return <constant_term, coeffs>;
end intrinsic;



//Toolbox function to use in the Eisenstein series function--gives us an L value
intrinsic LValue_Recognized(M::ModFrmHilDGRng, k::RngIntElt, psi::GrpHeckeElt) -> FldNumElt
  {This is a toolbox function to compute L values in the right space}
  require IsPrimitive(psi): "Hecke character must be primitive";
  bool, val := IsDefined(M`LValues, <k, psi>);
  if not bool then
    // Maybe a separate function to compute L-values?
    CoefficientField := Parent(psi)`TargetRing; // where the character values live
    // TODO: this is a total guess...
    prec := 100 + k^2;
    Lf := LSeries(psi : Precision:=prec);
    if IsTrivial(psi) then LSetPrecision(Lf, prec); end if;// Waiting for magma to fix
    Lvalue := Evaluate(Lf, 1-k);
    // figure out the right place to recognize
    // i.e., figure out what complex embedding magma used to embed the L-function into CC
    places := InfinitePlaces(CoefficientField);
    for p in PrimesUpTo(1000) do
      if Conductor(Lf) mod p eq 0 then continue; end if;
      if #places eq 1 then
        // there is only one place left, so that must be the one
        break;
      end if;
      assert #places ge 1;
      ap_K := psi(p); // in CoefficientField
      // Over degree 2
      // EulerFactor = 1 - psi(p) T^2 if p inert
      //             = 1 - ? + psi(p)T^2 if p splits
      pfactor := Factorisation(p*Integers(BaseField(M)));
      sign := (-1)^(&+[elt[2] : elt in pfactor]);
      ap_CC := sign*Coefficient(EulerFactor(Lf, p), Degree(Lf));
      // print Evaluate(ap_K, places[1]), ap_CC, EulerFactor(Lf, p);
      // restrict to the places where pl(ap_K) = ap_CC
      places := [pl : pl in places | -3 gt Log(Abs(Evaluate(ap_K, pl) - ap_CC)) ];
    end for;
    // we did our best, if #places > 1, then any embedding should work, e.g, the Image is smaller than the Codomain
    pl := places[1];
    CC<I> := ComplexField(Precision(Lvalue));
    val := RecognizeOverK(CC!Lvalue, CoefficientField, pl, false);
    M`LValues[<k, psi>] := val;
  end if;
  return val;
end intrinsic;


intrinsic EisensteinInclusions(Mk::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt) -> SeqEnum[ModFrmHilDElt]
  {return E(eta, psi)(dd*zz) for dd in divisors of Level(Mk)/(Conductor(psi) * Conductor(eta))}
  require IsPrimitive(eta) and IsPrimitive(psi): "We expect eta and psi to be primitive";
  M := Parent(Mk);
  divisors := Divisors(Level(Mk)/(Conductor(psi) * Conductor(eta)));
  ZF := Integers(M);
  ideals := &cat[[ZF !! (nn*ddinv) : nn in Ideals(M) | IsIntegral(nn*ddinv)] where ddinv := dd^-1 : dd in divisors];
  coeffs := EisensteinCoefficients(M, Weight(Mk), eta, psi, ideals);
  return [EisensteinSeries(Mk, eta, psi: dd:=dd, Coefficients:=coeffs) : dd in divisors];
end intrinsic;
