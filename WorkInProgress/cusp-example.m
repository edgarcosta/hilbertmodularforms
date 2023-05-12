//AttachSpec("spec");
SetDebugOnError(true);
S<x> := PolynomialRing(QQ);
//F<a> := NumberField(x^2 - 5);
F<nu> := QuadraticField(5);
ZF := Integers(F);
bb := 1*ZF;
NN := 3*ZF;
//NN := 21*ZF;
P1 := CuspQuadruples(NN, bb : GammaType := "Gamma0");
C1 := Cusps(NN, bb : GammaType := "Gamma0");
//eps := FundamentalUnitTotPos(F);
//eps_RR := [Evaluate(eps,pl) : pl in InfinitePlaces(F)];
//bb := 1*ZF;
//ss := (1/nu)*ZF;
//MM := 7*ZF;
//GeneratorOfQuotientModuleCRT(ss,MM);
/*
  ss_mod := Module([ss]);
  ssMM_mod := Module([ss*MM]);
  ss_quo, mp_ss_quo := quo< ss_mod | ssMM_mod >;  // just this
*/

//RssMM0 := GeneratorsOfQuotientModule(ss,MM);
//RssMM_comp0 := GeneratorsOfQuotientModule(ss*bb*MM,(NN/MM));
/*
  a := RssMM0[1];
  inds := [1];
  rep_bool := false;
  while not rep_bool do
    a := ReduceModuloIdeal(eps*a, ss, ss*MM);
    ind := Index(RssMM0, a);
    if ind eq 1 then
      rep_bool := true;
      break;
    end if;
    Append(~inds, ind);
  end while;
*/

RssMM := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss,MM);
RssMM_comp := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss*bb*MM,(NN/MM));
//P1 := Gamma1Quadruples(NN, bb);
//cusps := Gamma1Cusps(NN, bb);

quad := P1[5];
a_bar, c_bar := Explode(quad[3]);
a_bar, c_bar;
c := CuspLiftSecondCoordinate(c_bar, quad[1], quad[2], NN, bb);
a := CuspLiftFirstCoordinate(a_bar, c, quad[1], quad[2], NN, bb);

X := CartesianProduct(RssMM, RssMM_comp);
Q, mpQ := quo< ZF | NN>;
UQ, mpUQ := UnitGroup(Q);

// act by (R/NN)^*
gens_ab := Generators(UQ);
gens := [mpUQ(el) : el in gens_ab];
new := (ZF!gens[1])*RssMM[1];
new := ReduceShintaniMinimizeDistance(new);

// should be congruent to something in RssMM mod ss*MM
for el in RssMM do
  el - new in MM;
end for;

// alternative way of forming ss/(ss*MM)
/*
  ss_lat := NumberFieldLattice([Vector(F,[1])] : Ideals := [ss]);
  ssMM_lat := NumberFieldLattice([Vector(F,[1])] : Ideals := [ss*MM]);
  ss_ded := Module(ss_lat);
  ssMM_ded := Module(ssMM_lat);
  quo<ss_ded | ssMM_ded>;

  quo< Module([ss]) | Module([ss*MM])>;  // just this
*/

/*
  ss_module := Module([ss]);
  ssMM_module := Module([ss*MM]);
  ElementaryDivisors(s_module, sm_module);
*/

/*
  ss_basis := AbsoluteBasis(ss);
  ZFMM, mpMM := quo< ZF | MM>;
  quotient_gens := [];
  for el in ZFMM do
    a := ZF!el;
    t := &+[a[i]*ss_basis[i] : i in [1..#ss_basis]];
    if t*ss + ss*MM eq ss then
      Append(~quotient_gens, t);
    end if;
  end for;
*/

/*
  Q, mp := quo< ZF | (ss^-1)*MM >;
  UQ, mpUQ := UnitGroup(Q);
  UQ_seq := [ZF!mpUQ(el) : el in UQ];
  nu := UQ_seq[8];
  nu_RR := [Evaluate(nu,pl) : pl in InfinitePlaces(F)];
  r := 1/(2*(Log(eps_RR[1]) - Log(eps_RR[2])))*(Log(-(nu_RR[2]^2/nu_RR[1]^2)*(Log(eps_RR[2])/Log(eps_RR[1]))));
  mixed := [el : el in UQ_seq | Signature(el) in [[1,-1], [-1, 1]]];
  pairs := [ReduceShintaniMinimizeDistance(el) : el in mixed];
  mixed_red := [el[1] : el in pairs];
*/

/*
  for i := 1 to #mixed do
    nu := mixed[i];
    printf "original elt = %o\n", mixed[i];
    printf "original dist = %o\n", DistanceSquared(EmbedNumberFieldElement(mixed[i]));
    printf "new elt = %o\n", mixed_red[i];
    printf "new dist = %o\n", DistanceSquared(EmbedNumberFieldElement(mixed_red[i]));
    print "Nearby points...";
    for j := -3 to 3 by 1 do
      nu_new := eps^j*nu;
      print DistanceSquared(EmbedNumberFieldElement(nu_new));
    end for;
    print "";
  end for;
*/
