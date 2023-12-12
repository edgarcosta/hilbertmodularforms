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
  require &and[Conductor(c) eq Modulus(c) : c in [* eta, psi *]]: "characters need to be primitive";
  M := Parent(Mk);
  k := Weight(Mk);
  N := Level(Mk);
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  require N subset aa*bb*dd: "Modulos(eta)*Modulos(psi)*dd must divide Level(Mk)";
  X := Parent(Character(Mk));
  require IsTrivial(eta*psi*Character(Mk)^-1): Sprintf("we must have psi*eta = Character(Mk), %o, %o", Parent(eta*psi), (Parent(Character(Mk))));
  require IsParallel(k): "the weight is not parallel, there are no Eisenstein Series in this case";
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

  coeff_rings := AssociativeArray();
  m := Order(Character(Mk));
  l := LCM(Order(eta), Order(psi));

  // We would prefer to put it in the default coefficient ring of Mk
  coeff_ring := (IsDivisibleBy(m, l)) select DefaultCoefficientRing(Mk) else CyclotomicField(l);

  for bb in NarrowClassGroupReps(M) do
    ddbb := NarrowClassRepresentative(M,dd*bb);
    coeffs[ddbb] := AssociativeArray();
    coeffs[ddbb][0] := StrongCoerce(coeff_ring, constant_term[bb]);

    coeff_rings[bb] := coeff_ring;
    // All other coefficients, equation (48)
    for nu->nn in RepToIdeal(M)[ddbb] do
      if not IsZero(nu) then
        mm := nn*ddinv;
        if IsIntegral(mm) then
          mm := ZF !! mm;
          coeffs[ddbb][nu] := StrongCoerce(coeff_ring, coeffs_ideals[mm]);
        else
          coeffs[ddbb][nu] := coeff_ring!0;
        end if;
      end if;
    end for;
  end for;
  E := HMF(Mk, coeffs : coeff_rings := coeff_rings);
  return E;
end intrinsic;

intrinsic EisensteinConstantCoefficient(
    M::ModFrmHilDGRng,
    Weight::SeqEnum[RngIntElt],
    eta::GrpHeckeElt,
    psi::GrpHeckeElt
    ) -> Tup
  {return an associative array with constant coefficients indexed by bb}
  // We are following the notation in Section 2.2 of Dasgupta, Darmon, Pollack - Hilbert Modular Forms and the Gross-Stark Conjecture
  aa := Modulus(eta); // aa := Conductor(eta);
  bb := Modulus(psi); // bb := Conductor(psi);
  require #SequenceToSet(Weight) eq 1: "We only support EisensteinSeries with parallel weight";
  k := Weight[1];

  //Set the coefficient field to be the common field for eta and psi.
  lcm := LCM(Order(eta), Order(psi));
  L<z> := CyclotomicField(lcm);
  etainv := eta^-1;
  psiinv := psi^-1;
  SetTargetRing(~eta, z);
  SetTargetRing(~psi, z);

  // deal with L-values
  if IsOne(aa) then // aa = 1
    prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
    SetTargetRing(~prim, z);
    c0aa := L!LValue_Recognized(M, k, prim);
  else
    c0aa := 0;
  end if;
  // k = 1 and bb == 1
  if k eq 1 and IsOne(bb) then
    prim := AssociatedPrimitiveCharacter(eta*psi^(-1));
    SetTargetRing(~prim, z);
    c0bb := L!LValue_Recognized(M, k, prim);
  else
    c0bb := 0;
  end if;
  
  constant_term := AssociativeArray();
  n := Degree(BaseField(M));
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
    constant_term[bb] := AssociativeArray();
    // zero term for bb, equation (49) and (50)
    // their tt_lambda is our bbp
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    etainv_of_bbp := (IsDisjoint(Support(bbp), Support(Conductor(eta)))) select eta(bbp)^-1 else 0;
    psiinv_of_bbp := (IsDisjoint(Support(bbp), Support(Conductor(psi)))) select psi(bbp)^-1 else 0;

    constant_term[bb] := 2^(-n)*(etainv_of_bbp * c0aa + psiinv_of_bbp * c0bb );
  end for;


  // Normalize coefficients
  bb1 := bbs[1];
  c0inv := (not (constant_term[bb1] in [0,1])) select (1/constant_term[bb1]) else 1;
  for bb->c in constant_term do
    constant_term[bb] *:= c0inv;
  end for;
  assert constant_term[bb1] in [0,1];

  return constant_term, c0inv;
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

  constant_term, c0inv := EisensteinConstantCoefficient(M, Weight, eta, psi);

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
  if not IsDefined(M`LValues, Parent(psi))  then
    M`LValues[Parent(psi)] := AssociativeArray();
  end if;
  bool, val := IsDefined(M`LValues[Parent(psi)], <k, psi>);
  if not bool then
    // Maybe a separate function to compute L-values?
    z := psi`Zeta;
    CoefficientField := Parent(z); // where the character values live
    // TODO: this is a total guess...
    prec := 100 + k^2;
    Lf := LSeries(psi : Precision:=prec);
    if IsTrivial(psi) then LSetPrecision(Lf, prec); end if;// Waiting for magma to fix
    Lvalue := Evaluate(Lf, 1-k);
    // figure out the right place to recognize
    // i.e., figure out what complex embedding magma used to embed the L-function into CC
    places := InfinitePlaces(CoefficientField);
    CC<I> := ComplexField(Precision(Parent(Lvalue)));
    zCC := Exp(2*Pi(CC)*I/CyclotomicOrder(CoefficientField));
    v0, p0 := Minimum([Abs(Evaluate(z, pl : Precision := Precision(CC)) - zCC) : pl in places]);
    v1, p1 := Minimum([Abs(ComplexConjugate(Evaluate(z, pl : Precision := Precision(CC))) - zCC) : pl in places]);
    conjugate := v1 lt v0;
    if conjugate then
      pl := places[p1];
    else
      pl := places[p0];
    end if;
    val := RecognizeOverK(CC!Lvalue, CoefficientField, pl, conjugate);
    M`LValues[Parent(psi)][<k, psi>] := val;
  end if;
  return val;
end intrinsic;

intrinsic EisensteinAdmissibleCharacterPairs(Mk::ModFrmHilD : IdentifyConjugates := true, NewformsOnly := true) -> List
  {
    input: 
      A space of Hilbert modular forms, say of level N, weight k, and nebentypus chi.
    returns:
      A SetEnum of pairs <eta, psi>, where eta and psi are primitive characters
      associated to ray class characters of conductor (M, [1,2])
  }  
  require IsParallel(Mk`Weight) : "Eisenstein series don't exist in nonparallel weight";
  N := Mk`Level;
  k := Mk`Weight[1];
  chi := Character(Mk);
  F := BaseField(Parent(Mk));
  H := HeckeCharacterGroup(N, [1 .. Degree(F)]);

  if (not IsGamma1EisensteinWeight(chi,k)) then
      return [* *];
  end if;
  
  check_chi := func<eta, psi | (eta * psi eq chi)>;
  
  // By default we only produce pairs of characters corresponding to newforms,
  // i.e. such that Cond(eta) * Cond(psi) = N, but for backwards compatibility
  // and testing it is useful to be able to produce the pairs corresponding to
  // all the Eisenstein series.
  check_n := func<eta, psi, exact |\
    (exact) select (N eq Conductor(eta) * Conductor(psi)) else (N subset Conductor(eta) * Conductor(psi))>;

  pairs := &join{{<eta, psi> : psi in Elements(H) |\
    check_chi(eta, psi) and check_n(eta, psi, NewformsOnly)} : eta in Elements(H)};

  mth_power := func<pair, m | <pair[1]^m, pair[2]^m>>;
  n := Exponent(AbelianGroup(H));
  coprime_to_n := [m : m in [1 .. n] | IsCoprime(m, n)];

  if IdentifyConjugates then
    pairs_up_to_galois := {};
    while #pairs gt 0 do
      pair := Rep(pairs);
      Include(~pairs_up_to_galois, pair);
      for m in coprime_to_n do
        Exclude(~pairs, mth_power(pair, m));
      end for;

      if k eq 1 then
        Exclude(~pairs, <pair[2], pair[1]>);
      end if;
    end while;
    pairs := pairs_up_to_galois;
  end if;

  APC := func<pair | <AssociatedPrimitiveCharacter(pair[1]), AssociatedPrimitiveCharacter(pair[2])>>;
  Mk`EisensteinAdmissibleCharacterPairs := [* APC(pair) : pair in pairs *];
  return Mk`EisensteinAdmissibleCharacterPairs;
end intrinsic;
