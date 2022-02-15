AttachSpec("spec");
S<x> := PolynomialRing(QQ);
//F<a> := NumberField(x^2 - 5);
F<a> := QuadraticField(5);
ZF := Integers(F);
eps := FundamentalUnitTotPos(F);
eps_RR := [Evaluate(eps,pl) : pl in InfinitePlaces(F)];
s := (1/a)*ZF;
M := 7*ZF;
Q, mp := quo< ZF | (s^-1)*M >;
UQ, mpUQ := UnitGroup(Q);
UQ_seq := [ZF!mpUQ(el) : el in UQ];
nu := UQ_seq[8];
nu_RR := [Evaluate(nu,pl) : pl in InfinitePlaces(F)];
r := 1/(2*(Log(eps_RR[1]) - Log(eps_RR[2])))*(Log(-(nu_RR[2]^2/nu_RR[1]^2)*(Log(eps_RR[2])/Log(eps_RR[1]))));
mixed := [el : el in UQ_seq | Signature(el) in [[1,-1], [-1, 1]]];
pairs := [ReduceShintaniMinimizeDistance(el) : el in mixed];
mixed_red := [el[1] : el in pairs];

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

RssMM(s,M);

// alternative way of forming s/(s*M)
/*
  s_lat := NumberFieldLattice([Vector(F,[1])] : Ideals := [s]);
  sm_lat := NumberFieldLattice([Vector(F,[1])] : Ideals := [s*M]);
  s_ded := Module(s_lat);
  sm_ded := Module(sm_lat);
  quo<s_ded | sm_ded>;
  quo< Module([s]) | Module([s*M])>;
*/
