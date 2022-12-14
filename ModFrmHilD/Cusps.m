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
    elif GammaType eq "Gamma" then
      a_new := ReduceModuloIdeal(a0, ss, ss*NN);
      c_new := ReduceModuloIdeal(c0, ss*bb, ss*bb*NN);
      if c_new eq 0 then
        c_new := Generators(ss*bb*MM)[1];
      end if;
    else
      error "GammaType not recognized";
    end if;
    //vprintf HilbertModularForms: "final a = %o, c = %o\n", a_new, c_new;
    Append(~final, [F|a_new, c_new]);
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
intrinsic CuspLiftFirstCoordinate(a_bar::RngElt, c::RngElt, ss::RngOrdIdl, MM::RngOrdIdl, NN::RngOrdIdl, bb::RngOrdIdl) -> RngElt 
  {}
  ZF := Order(NN);
  F := NumberField(ZF);
  fac_ss := Factorization(ss);
  fac_MM := Factorization(MM);
  ssMM_primes := [el[1]: el in fac_ss] cat [el[1]: el in fac_MM];
  ssMM_primes := SetToSequence(SequenceToSet(ssMM_primes));
  bad_primes := [el[1] : el in Factorization(c*(bb^-1)) | not el[1] in ssMM_primes];
  vs := [];
  for p in bad_primes do
    if Valuation(a_bar, p) gt 0 then
      Append(~vs, Valuation(ss, p));
    else
      Append(~vs, Valuation(ss,p)+1);
    end if;
  end for;
  for p in ssMM_primes do
      if Valuation(a_bar, p) gt Valuation(ss, p) then
          //p is necessarily prime to MM
          Append(~vs, Valuation(ss, p));
      elif Valuation(a_bar, p) eq Valuation(ss*MM, p) then
          //p is necessarily prime to MM
          Append(~vs, Valuation(ss*MM,p)+1);
      else
          Append(~vs, Valuation(ss*MM, p));
      end if;
  end for;
  x := FindEltWithValuations(F, bad_primes cat ssMM_primes, vs);
  a := a_bar+x;
  assert a*ZF + c*(bb^-1) eq ss;
  assert a - a_bar in ss*MM;
  return a;
end intrinsic;

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

intrinsic TotalNumberOfCusps(NN::RngOrdIdl : GammaType := "Gamma0") -> RngIntElt
{Return total number of cusps}
    ZF := Order(NN);
    F := NumberField(ZF);
    NCl, mp := NarrowClassGroup(ZF);
    quad_cnt := 0;
    for bb in NCl do
        quads := CuspQuadruples(NN,mp(bb) : GammaType := GammaType);
        quad_cnt +:= #quads;
    end for;
    return quad_cnt;
end intrinsic;

intrinsic CuspSanityCheck(NN::RngOrdIdl : GammaType := "Gamma0") -> BoolElt
{Test total number of cusps using sum of phi's}

  ZF := Order(NN);
  F := NumberField(ZF);
  R := GradedRingOfHMFs(F, 1);
  quad_cnt := TotalNumberOfCusps(NN: GammaType:=GammaType);
  
  if GammaType eq "Gamma0" then
      Mk := HMFSpace(R, NN, [2,2]);
      d := NumberOfCusps(Mk); //Computed using \sum_M \phi(...)    
  elif GammaType eq "Gamma1" then
      d := quad_cnt; //Replace with some other test
  else
      error "GammaType not recognized";
  end if;
  
  return quad_cnt eq d;
end intrinsic;

intrinsic CuspCheckEisensteinDim(NN::RngOrdIdl : GammaType := "Gamma0") -> BoolElt
{}
    ZF := Order(NN);
    F := NumberField(ZF);
    H := HeckeCharacterGroup(ideal<ZF|NN>, [1..#RealPlaces(F)]);
    R := GradedRingOfHMFs(F, 1);
    quad_cnt := TotalNumberOfCusps(NN: GammaType:=GammaType);
    
    if GammaType eq "Gamma" then
        vprintf HilbertModularForms: "formula = %o\n", GammaCuspCount(NN);
        vprintf HilbertModularForms: "#quads = %o\n", quad_cnt;
        return quad_cnt eq GammaCuspCount(NN);
    elif GammaType eq "Gamma0" then
        chis := [chi : chi in Elements(H) | IsEvenAtoo(chi) and IsTrivial(DirichletRestriction(chi))];
    elif GammaType eq "Gamma1" then
        chis := [chi : chi in Elements(H) | IsEvenAtoo(chi)];
    else
        error "GammaType not recognized";
    end if;
    // There are issues about Galois conjugacy classes (Issue #241), so we keep all characters here in this test
    d := 0;
    for chi in chis do
        //print "chi = ", Eltseq(chi);
        Mk_chi := HMFSpace(R, NN, [2,2], chi);
        a := CuspGetEisensteinDimension(Mk_chi);
        //print "other dimension = ", a;
        d +:= a;
        //a := EisensteinDimension(Mk_chi);        
        //print "dimension from EisensteinDimension = ", a;
    end for;
    vprintf HilbertModularForms: "Eisenstein dimension = %o\n", d;
    vprintf HilbertModularForms: "quadruple count = %o\n", quad_cnt;
    return quad_cnt eq d;
end intrinsic;

intrinsic CuspGetEisensteinDimension(Mk::ModFrmHilD) -> RngIntElt
{return the dimension of E(Mk)}
    N := Level(Mk);
    newforms_levels := AssociativeArray();
    for pair in CuspEisensteinAdmissibleCharacterPairs(Mk) do
        lvl := Conductor(pair[1]) * Conductor(pair[2]);
        if not IsDefined(newforms_levels, lvl) then
            newforms_levels[lvl] := 0;
        end if;
        //print [Order(e) : e in pair];
        newforms_levels[lvl] +:= 1; //EulerPhi(LCM([Order(e) : e in pair]));
    end for;
    partial_dims := [Integers()| #Divisors(N/mm)*rel_dim : mm->rel_dim in newforms_levels];
    //print partial_dims;
    return &+partial_dims;
end intrinsic;

intrinsic CuspEisensteinAdmissibleCharacterPairs(Mk::ModFrmHilD) -> SeqEnum
{returns a list of all the primitive pairs <chi1, chi2> such that chi1*chi2 =
Character(Mk) and Conductor(chi1)*Conductor(chi2) | Level(Mk) If the weight is
1, we only return pairs up to permutation}
    N := Level(Mk);
    k := Weight(Mk);
    assert k eq [2,2];
    k := k[1];
    chi := Character(Mk);
    M := Parent(Mk);
    X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
    assert X eq Parent(chi);
    chis := Elements(X);
    chis_reps := Set(chis); //Set(GaloisConjugacyRepresentatives(chis));
    chis_reps_index := {i : i->c in chis | c in chis_reps};
    chiscond := [Conductor(c) : c in chis];
    chisdict := AssociativeArray();
    for i->c in chis do
        chisdict[c] := i;
    end for;
    // [i, j] pairs st chis[i]*chis[j] = chi
    pairs := [ [i, chisdict[chi*c^-1]] : i->c in chis | i in chis_reps_index ];
    // filter based on conductor
    pairs := [ p : p in pairs | N subset chiscond[p[1]] * chiscond[p[2]] ];
    // k=2, so ignore special weight 1 case
    prims := AssociativeArray();
    for i in SequenceToSet(&cat pairs) do
        prims[i] := AssociatedPrimitiveCharacter(chis[i]);
    end for;
    return [* <prims[p[1]], prims[p[2]]> : p in pairs *];
end intrinsic;

