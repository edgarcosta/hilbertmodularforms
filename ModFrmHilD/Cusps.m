// cusp stuff

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

intrinsic FindEltWithValuations(F::Fld, ps::SeqEnum[RngOrdIdl], vs::SeqEnum[RngIntElt])
        -> FldElt
  {Find an element of F that has exactly the required valuations at a finite number of primes,
  and nonnegative valuations at other primes}
    ss := 1*Integers(F);
    MM := 1*Integers(F);
    for i:=1 to #ps do
        ss *:= ps[i] ^ vs[i];
        MM *:= ps[i];
    end for;
    
    m := ClassGroupPrimeRepresentatives(Integers(F), MM);
    for c in Domain(m) do
        b, x := IsPrincipal(m(c)*ss);
        if b then
            return x;
        end if;
    end for;
end intrinsic;

// see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4
intrinsic GeneratorOfQuotientModuleCRT(ss::RngOrdFracIdl, MM::RngOrdIdl) -> RngElt 
  {Find a generator of ss/ss*MM as a ZF/MM-module}
    primes_ss := SequenceToSet([p[1]: p in Factorization(ss)]);
    primes_MM := SequenceToSet([p[1]: p in Factorization(MM)]);
    primes := SetToSequence(primes_ss join primes_MM);
    vals := [Valuation(ss, p): p in primes];
    return FindEltWithValuations(FieldOfFractions(Order(ss)), primes, vals);
end intrinsic;
    
/*   ZF := Order(ss); */
/*   if ss*MM eq ss then */
/*     return ZF!1; */
/*   end if; */
/*   facts_num, facts_den := NumDenFactorization(ss*MM); */
/*   ss_vals_num := []; */
/*   ss_vals_den := []; */
/*   //printf "ss_vals num = %o\n", ss_vals_num; */
/*   //printf "ss_vals den = %o\n", ss_vals_den; */
/*   residues_num := []; */
/*   residues_den := []; */
/*   moduli_num := []; */
/*   moduli_den := []; */
/*   for i := 1 to #facts_num do */
/*     fact := facts_num[i]; */
/*     P := fact[1]; */
/*     //v := fact[2]; */
/*     v := ss_vals_num[i]; */
/*     t := UniformizingElement(P); */
/*     residues_num cat:= [0, (t^v mod P^(v+1))]; // might be a problem if v=0 */
/*     moduli_num cat:= [P^v, P^(v+1)]; */
/*   end for; */
/*   for i := 1 to #facts_den do */
/*     fact := facts_den[i]; */
/*     P := fact[1]; */
/*     //v := -fact[2]; // want positive valuation */
/*     v := -ss_vals_den[i]; // want positive valuation */
/*     t := UniformizingElement(P); */
/*     residues_den cat:= [0, (t^v mod P^(v+1))]; */
/*     moduli_den cat:= [P^v, P^(v+1)]; */
/*   end for; */
/*   if #moduli_num eq 0 then // if list of moduli is empty */
/*     a_num := ZF!1; */
/*   else */
/*     // ensure no cross-cancelation between num and den */
/*     moduli_num cat:= [el[1] : el in facts_den]; */
/*     residues_num cat:= [1 : el in facts_den]; */
/*     //printf "residues for num = %o\n", residues_num; */
/*     //printf "moduli for num = %o\n", moduli_num; */
/*     a_num := CRT(residues_num, moduli_num); */
/*   end if; */
/*   if #moduli_den eq 0 then */
/*     a_den := ZF!1; */
/*   else */
/*     // ensure no cross-cancelation between num and den */
/*     moduli_den cat:= [el[1] : el in facts_num]; */
/*     residues_den cat:= [1 : el in facts_num]; */
/*     //printf "residues for den = %o\n", residues_den; */
/*     //printf "moduli for den = %o\n", moduli_den; */
/*     a_den := CRT(residues_den, moduli_den); */
/*   end if; */
/*   //printf "a_num = %o\n", a_num; */
/*   //printf "a_den = %o\n", a_den; */
/*   // verify it generates */
/*   a := a_num/a_den; */
/*   assert a*ZF + ss*MM eq ss; */
/*   return a; */
/* end intrinsic; */

/* // see section 5 of paper (eqn 5.1.5) or Dasgupta-Kakde Def 3.4 */
/* intrinsic GeneratorsOfQuotientModuleBruteForce(ss::RngOrdFracIdl, MM::RngOrdIdl) -> SeqEnum */
/*   {Return the sequence of generators of ss/(ss*MM) as a ZF/MM-module by looping over all elements of ss/(ss*MM).} */
/*   ZF := Order(ss); */
/*   F := NumberField(ZF); */
/*   ZFMM, mpMM := quo< ZF | MM>; */
/*   // loop over all elts of ss/(ss*MM) */
/*   ss_gens := Generators(ss); */
/*   ss_ngens := #ss_gens; */
/*   quotient_gens := []; */
/*   for el in CartesianPower(ZFMM, ss_ngens) do */
/*     t := ZF!0; */
/*     for i := 1 to ss_ngens do */
/*       t +:= (el[i] @@ mpMM)*ss_gens[i]; */
/*     end for; */
/*     // check if new mod ss*MM */
/*     /\* */
/*       new_bool := true; */
/*       for q in quotient_gens do */
/*         if (t - q) in ss*MM then */
/*           new_bool := false; */
/*         end if; */
/*       end for; */
/*     *\/ */
/*     //if (t*ZF + ss*MM eq ss) and new_bool then */
/*     if (t*ZF + ss*MM eq ss) then */
/*       Append(~quotient_gens, ReduceModuloIdeal(t, ss, ss*MM)); */
/*     end if; */
/*   end for; */
/*   quotient_gens := SetToSequence(SequenceToSet(quotient_gens)); */
/*   //printf "# of quotient gens = %o\n", #quotient_gens; */
/*   //printf "number of units in ZF/ideal = %o\n", #UnitGroup(ZFMM); */
/*   assert #quotient_gens eq #UnitGroup(ZFMM); */
/*   return quotient_gens; */
/* end intrinsic; */

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
    vprintf HilbertModularForms: "orbit found = %o\n", orb;
    remaining := [el : el in remaining | not el in orb];
    vprintf HilbertModularForms: "remaining indices = %o\n", remaining;
  end while;
  vprintf HilbertModularForms: "orbits = %o\n", orbits;
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

intrinsic MakePairsForQuadruple(NN::RngOrdIdl, bb::RngOrdIdl, ss::RngOrdFracIdl, MM::RngOrdIdl : GammaType := "Gamma0") -> SeqEnum
  {}

  ZF := Order(NN);
  F := NumberField(ZF);
  eps_p := FundamentalUnitTotPos(F);
  if Degree(F) eq 1 then
    eps := ZF!1;
  else
    eps := FundamentalUnit(F);
  end if;

  if GammaType in ["Gamma0", "Gamma1"] then
    a := GeneratorOfQuotientModuleCRT(ss,MM);
    c := GeneratorOfQuotientModuleCRT(ss*bb*MM,(NN/MM));
    ZFMM, mpMM := quo<ZF | MM>;
    ZFNNMM, mpNNMM := quo<ZF | (NN div MM) >;
  elif GammaType eq "Gamma" then
    // TODO: is this right?
    a := GeneratorOfQuotientModuleCRT(ss,NN);
    c := GeneratorOfQuotientModuleCRT(ss*bb,NN);
    ZFMM, mpMM := quo<ZF | NN>;
    ZFNNMM, mpNNMM := quo<ZF | NN >;
  else
    error "GammaType not recognized";
  end if;
  UQMM, mpQMM := UnitGroup(ZFMM);
  UQNNMM, mpQNNMM := UnitGroup(ZFNNMM);

  eps_barMM := mpMM(eps) @@ mpQMM;
  eps_barNNMM := mpNNMM(eps) @@ mpQNNMM;
  eps_p_barMM := mpMM(eps_p) @@ mpQMM;
  eps_p_barNNMM := mpNNMM(eps_p) @@ mpQNNMM;

  D, i1, i2, p1, p2 := DirectSum(UQMM, UQNNMM);
  //printf "direct sum = %o\n", D;
  if GammaType eq "Gamma1" then
    gens := [i1(mpMM(eps) @@ mpQMM) + i2(mpNNMM(eps) @@ mpQNNMM), i1(mpMM(-1) @@ mpQMM) + i2(mpNNMM(-1) @@ mpQNNMM), i1(eps_p_barMM), i2(eps_p_barNNMM)];
  elif GammaType eq "Gamma0" then
    gens := [i1(mpMM(eps) @@ mpQMM) + i2(mpNNMM(eps) @@ mpQNNMM), i1(mpMM(-1) @@ mpQMM) + i2(mpNNMM(-1) @@ mpQNNMM), i1(eps_p_barMM), i2(eps_p_barNNMM)];
    // mod out by (R/NN)^\times, as in eqn 5.1.7
    ZFNN, mpNN := quo<ZF |NN>;
    UQNN, mpQNN:= UnitGroup(ZFNN);
    UQNN_gens := [mpQNN(el) : el in Generators(UQNN)];
    gens cat:= [i1(mpMM(el) @@ mpQMM) - i2(mpNNMM(el) @@ mpQNNMM) : el in UQNN_gens]; // in i2 el or -el???
  elif GammaType eq "Gamma" then
    gens := [i1(mpMM(eps) @@ mpQMM) + i2(mpNNMM(eps) @@ mpQNNMM), i1(mpMM(-1) @@ mpQMM) + i2(mpNNMM(-1) @@ mpQNNMM)];
  else
    error "GammaType not recognized";
  end if;
  eps_gp := sub< D | gens >;
  //printf "eps_gp = %o\n", eps_gp;
  //printf "gens = %o\n", gens;
  T := [];
  for el in Transversal(D, eps_gp) do
    Append(~T, [* mpQMM(p1(el)) @@ mpMM, mpQNNMM(p2(el)) @@ mpNNMM *]);
  end for;
  reps := [ [* a*(el[1] @@ mpMM), c*(el[2] @@ mpNNMM) *] : el in T];
  final := [];
  for el in reps do
    a0, c0 := Explode(el);
    if GammaType in ["Gamma0", "Gamma1"] then
      // alternative Gamma0 approach: take output of Gamma1 cusps, then mod out by following relation. Rescale so that first components match, then see if second components differ multiplicatively by a unit of ZF/NN
      // see also p. 100 of Diamond and Shurman
      a_new := ReduceModuloIdeal(a0, ss, ss*MM);
      c_new := ReduceModuloIdeal(c0, ss*bb*MM, ss*bb*NN);
      if c_new eq 0 then
        c_new := Generators(ss*bb*MM)[1];
      end if;
      vprintf HilbertModularForms: "final a = %o, c = %o\n", a_new, c_new;
      Append(~final, [a_new, c_new]);
    elif GammaType eq "Gamma" then
      a_new := ReduceModuloIdeal(a0, ss, ss*NN);
      c_new := ReduceModuloIdeal(c0, ss*bb, ss*bb*NN);
      Append(~final, [a_new, c_new]);
    else
      error "GammaType not recognized";
    end if;
  end for;
  return final;
end intrinsic;

// P_1(NN)_bb in eqn 5.1.6 in paper, or Lemma 3.6 of Dasgupta-Kakde
// P_0(NN)_bb in eqn 5.1.9 in paper
intrinsic CuspQuadruples(NN::RngOrdIdl, bb::RngOrdIdl : GammaType := "Gamma0") -> SeqEnum
  {Return list of quadruples given in Lemma 3.6 of Dasgupta-Kakde (resp., eqn 5.1.9 in paper), which is in bijection with cusps of Gamma_1(NN)_bb (resp., of Gamma_0(NN)_bb).}
  ZF := Order(NN);
  F := NumberField(ZF);
  mpCl := ClassGroupPrimeRepresentatives(ZF,NN);
  Cl := Domain(mpCl);
  Cl_seq := [mpCl(el) : el in Cl];
 
  quads := [];
  for ss in Cl_seq do
    //printf "ss = %o\n", ss;
    for MM in Divisors(NN) do
      //printf "MM = %o\n", MM;
      //RssMM := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss,MM);
      //RssMM_comp := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss*bb*MM,(NN/MM));
      pairs := MakePairsForQuadruple(NN, bb, ss, MM : GammaType := GammaType);
      //printf "pairs = %o\n", pairs;
      for el in pairs do
        Append(~quads, [* ss, MM, el *]);
      end for;
    end for;
  end for;
  return quads;
end intrinsic;

// see Lemma 5.1.10 in paper, or Lemma 3.6 of Dasgupta-Kakde
intrinsic CuspLiftSecondCoordinate(c_bar::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl : GammaType := "Gamma0") -> RngElt 
  {With the notation as in section 5 of the paper, given c_bar in P_1(NN)_bb, lift c_bar to a c satisfying GCD(c*bb^-1,NN) = MM.}

  ZF := Order(ss);

  // fulfill congruence condition
  // TODO: still okay for GammaType := Gamma?
  residues := [c_bar];
  moduli := [ss*bb*NN];

  // fulfill GCD condition
  if GammaType in ["Gamma0", "Gamma1"] then
    //facts := Factorization(ss*bb*NN);
    facts := Factorization(bb*NN);
  elif GammaType eq "Gamma" then
    //facts := Factorization(ss*bb);
    facts := Factorization(bb);
  else
    error "GammaType not recognized";
  end if;
  //printf "factors of ss*bb*NN: %o\n", facts;
  
  //Ps := [fact[1] : fact in facts];
  //mults := [fact[2] : fact in facts];
  for fact in facts do
    P := fact[1];
    vN := fact[2];
    //v := mults_num[i];
    if GammaType in ["Gamma0", "Gamma1"] then
      v := Valuation(bb*MM,P);
    elif GammaType eq "Gamma" then
      // TODO: double check this
      v := Valuation(bb*NN,P);
    else
      error "GammaType not recognized";
    end if;

    //printf "nonzero valuation; P = %o, v = %o\n", P, v;
    residues cat:= [0, (c_bar mod P^(v+1))]; // might be a problem if v=0
    moduli cat:= [P^v, P^(v+1)];
    //else
    //  residues cat:= [(c_bar mod P^vN)]; // might be a problem if v=0
    //  moduli cat:= [P^vN];
  end for;

  vprintf HilbertModularForms: "residues = %o\n", residues;
  vprintf HilbertModularForms: "moduli = %o\n", moduli;

  if #moduli eq 0 then // if list of moduli is empty
    c := ZF!1;
  else
    c := CRT(residues, moduli);
  end if;
  if c eq 0 then
    c +:= Generators(&*moduli)[1];
  end if;
  assert GCD(c*(bb^-1),NN) eq MM;
  assert c - c_bar in ss*bb*NN;
  return c;
end intrinsic;

// see Lemma 5.1.10 in paper, or Lemma 3.6 of Dasgupta-Kakde
intrinsic CuspLiftFirstCoordinate(a_bar::RngElt, c::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
  {}

  ZF := Order(NN);
  F := NumberField(ZF);
  bad_primes := [el[1] : el in Factorization(c*(bb^-1)) | Valuation(MM, el[1]) eq 0];
  vs := [];
  for p in bad_primes do
    if Valuation(a_bar, p) gt 0 then
      Append(~vs, Valuation(ss, p));
    else
      Append(~vs, Valuation(ss,p)+1);
    end if;
  end for;
  x := FindEltWithValuations(F, bad_primes, vs);
  return a_bar + x;
end intrinsic;

/*
  intrinsic CuspLiftFirstCoordinate(a_bar::RngElt, c::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
    {}
    ZF := Order(ss);
    //facts := Factorization(ss*MM);
    if a_bar eq 0 then
      return ZF!1;
    end if;
    // if c=0, then ss should be principal
    if c eq 0 then // we've excluded this from happening in CuspLiftSecondCoordinate; can probably delete
      pbool, a := IsPrincipal(ss);
      assert pbool;
      //facts := Factorization(ss*MM);
      //Ps_num := [fact[1] : fact in facts | fact[2] gt 0];
      ////mults_num := [fact[2] : fact in facts | fact[2] gt 0];
      //mults_num := [Valuation((ss*MM), P) : P in Ps_num];
      //Ps_den := [fact[1] : fact in facts | fact[2] lt 0];
      ////mults_den := [fact[2] : fact in facts | fact[2] lt 0];
      //mults_den := [Valuation((ss*MM), P) : P in Ps_den];
      Q, mp := quo< ZF | ss*MM>;
      UQ, mpUQ := UnitGroup(Q);
      U, mpU := UnitGroup(ZF);
      Qunits := sub< UQ | [(mp(mpU(el))) @@ mpUQ : el in Generators(U)]>;
      u := (mp(a)^-1*a_bar) @@ (mpU*mpUQ);
      return u*a;
    end if;

    
    facts := Factorization(c*(bb^-1));
    Ps_num    := [fact[1] : fact in facts | fact[2] gt 0];
    mults_num := [Valuation((c*bb^-1), P) : P in Ps_num];
    Ps_den    := [fact[1] : fact in facts | fact[2] lt 0];
    mults_den := [Valuation((c*bb^-1), P) : P in Ps_den];
    
    //print "Ps_num = ", Ps_num;
    //print "c = ", c;

    residues_num := [a_bar];
    moduli_num := [ss*MM];
    residues_den := [];
    moduli_den := [];

    // numerator residues and moduli
    //print "making numerator";
    for i := 1 to #Ps_num do
      P := Ps_num[i];
      //v := mults_num[i];
      v := Valuation(ss,P);
      if v gt 0 then
        vprintf HilbertModularForms: "nonzero valuation; P = %o, v = %o\n", P, v;
        residues_num cat:= [0, (a_bar mod P^(v+1))]; // might be a problem if v=0
        moduli_num cat:= [P^v, P^(v+1)];
      else
        vMM := Valuation(MM,P);
        if vMM gt 0 then
          residues_num cat:= [(a_bar mod P^mults_num[i])]; // might be a problem if v=0
          moduli_num   cat:= [P^mults_num[i]];
        else
          residues_num cat:= [(ZF!1 mod P^mults_num[i])]; // might be a problem if v=0
          moduli_num   cat:= [P^mults_num[i]];
        end if;
      end if;
    end for;

    // denominator residues and moduli
    //print "making denominator";
    for i := 1 to #Ps_den do
      P := Ps_den[i];
      //v := -mults_den[i];
      v := -Valuation(ss,P);
      if v gt 0 then
      vprintf HilbertModularForms: "nonzero valuation; P = %o, v = %o\n", P, v;
        residues_den cat:= [0, (a_bar mod P^(v+1))]; // might be a problem if v=0
        moduli_den cat:= [P^v, P^(v+1)];
      else
        residues_den cat:= [(a_bar mod P^mults_den[i])]; // might be a problem if v=0
        moduli_den cat:= [P^mults_den[i]];
      end if;
    end for;

    if GetVerbose("HilbertModularForms") gt 0 then
      printf "residues for num = %o\n", residues_num;
      printf "moduli for num = %o\n", moduli_num;
      printf "residues for den = %o\n", residues_den;
      printf "moduli for den = %o\n", moduli_den;
    end if;

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
*/

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

intrinsic IntegralCoordinates(x::Pt) -> SeqEnum
  {}
  x_seq := Eltseq(x);
  d := &*[Denominator(el) : el in x_seq];
  return [Integers()!(d*el) : el in x_seq];
end intrinsic;

intrinsic Cusps(NN::RngOrdIdl, bb::RngOrdIdl : GammaType := "Gamma0") -> SeqEnum
  {}
  ZF := Order(NN);
  F := NumberField(ZF);
  PP1 := ProjectiveSpace(F,1);
  quads := CuspQuadruples(NN, bb : GammaType := GammaType);
  cusps_seq := [];
  for quad in quads do
    ss, MM, ac_bar := Explode(quad);
    vprintf HilbertModularForms: "quadruple = %o\n", quad;
    a_bar, c_bar := Explode(ac_bar);
    vprintf HilbertModularForms: "Lifting second coordinate. c_bar = %o\n", c_bar;
    //c := CuspLiftSecondCoordinate(c_bar, ss, MM, NN, bb);
    c := c_bar;
    vprintf HilbertModularForms: "Lifting first coordinate. a_bar = %o\n", a_bar;
    a := CuspLiftFirstCoordinate(a_bar, c, ss, MM, NN, bb);
    vprintf HilbertModularForms: "Lifted coordinates [a,c] = [%o,%o]\n", a, c;
    Append(~cusps_seq, [* bb, MM, PP1![a,c] *]);
  end for;
  return cusps_seq;
end intrinsic;

intrinsic WriteCuspDataToRow(surface_label::MonStgElt, pt::Pt, bb::RngOrdIdl, MM::RngOrdIdl, min_period::SeqEnum, rep::RngIntElt) -> MonStgElt
  {Script for writing cusp data to data table row}

  return Sprintf("%o|%o|%o|%o|%o|%o", surface_label, Eltseq(pt), LMFDBLabel(bb), LMFDBLabel(MM), min_period, rep);
end intrinsic;

// copy-pasta-ed from ModSym/Dirichlet.m and adapted for Hecke
intrinsic GaloisConjugacyRepresentatives(S::[GrpHeckeElt]) -> SeqEnum
  {Representatives for the Gal(Qbar/Q)-conjugacy classes of Hecke characters
 contained in the given sequence S}

   G := Universe(S);

   if #S eq 0 or Type(G`TargetRing) eq FldRat then
     return S;
   end if;

   require ISA(Type(G`TargetRing), FldAlg) :
          "The base ring of argument 1 must be a number field.";

   //r, n := DistinguishedRoot(G);
   n := G`CycloOrder;
   r := G`TargetRing.1;
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

// see Lemma 5.2, p. 78 of van der Geer
intrinsic GammaCuspCount(NN::RngOrdIdl) -> RngIntElt 
  {}
  ZF := Order(NN);
  F := NumberField(ZF);
  U, mpU := UnitGroup(ZF);
  Q, pi := quo< ZF | NN >;
  UQ, mpUQ := UnitGroup(Q);
  mp_unit := hom< U -> UQ | x :-> (pi(mpU(x)) @@ mpUQ) >;
  img_unit := Image(mp_unit);
  cnt := Norm(NN)^2/#img_unit;
  for pair in Factorization(NN) do
    PP := pair[1];
    cnt *:= (1 - Norm(PP)^-2);
  end for;
  return NarrowClassNumber(F)*ClassNumber(ZF)*cnt;
end intrinsic;

intrinsic CuspSanityCheck(NN::RngOrdIdl : GammaType := "Gamma0") -> BoolElt
  {}
  ZF := Order(NN);
  F := NumberField(ZF);
  NCl, mp := NarrowClassGroup(ZF);
  H := HeckeCharacterGroup(ideal<ZF|NN>, [1..#RealPlaces(F)]);
  R := GradedRingOfHMFs(F, 1);
  quad_cnt := 0;
  for bb in NCl do
    quads := CuspQuadruples(NN,mp(bb) : GammaType := GammaType);
    quad_cnt +:= #quads;
  end for;
  if GammaType eq "Gamma" then
    vprintf HilbertModularForms: "formula = %o\n", GammaCuspCount(NN);
    vprintf HilbertModularForms: "#quads = %o\n", quad_cnt;
    return quad_cnt eq GammaCuspCount(NN);
  elif GammaType eq "Gamma0" then
    //chis := [H!1];
    chis := [chi : chi in Elements(H) | IsEvenAtoo(chi) and IsTrivial(DirichletRestriction(chi))];
  elif GammaType eq "Gamma1" then
    chis := [chi : chi in Elements(H) | IsEvenAtoo(chi)];
    else
    error "GammaType not recognized";
  end if;
  chis := GaloisConjugacyRepresentatives(chis);
  d := 0;
  for chi in chis do
    //print "chi = ", Eltseq(chi);
    Mk_chi := HMFSpace(R, NN, [2,2], chi);
    d +:= EisensteinDimension(Mk_chi);
  end for;
  vprintf HilbertModularForms: "Eisenstein dimension = %o\n", d;
  vprintf HilbertModularForms: "quadruple count = %o\n", quad_cnt;
  return quad_cnt eq d;
end intrinsic;

