F<nu> := QuadraticField(5);
CuspSanityCheck(2*ZF : GammaType := "Gamma");
quads := CuspQuadruples(2*ZF, 1*ZF : GammaType := "Gamma");
for quad in quads do
  pair := quad[3];
  print [F!el : el in pair];
end for;
Q, mpQ := quo<ZF | 2*ZF >;
Q;
#Q;
UQ, mpUQ := UnitGroup(Q);
U, mpU := UnitGroup(ZF);
Ugens := [mpU(el) : el in Generators(U)];
/*
  cart := CartesianPower(Q,2);
  cart;
  cart0 := [el : el in cart | el ne <0,0>];
  #cart0;
  units := [mpQ(mpU(el)) : el in Generators(U)];
  cart[1];
  cart0[1];
  [units[2]*cart0[1][1], units[2]*cart0[1][2]];
*/
M := Module(ZF,1);
M;
quo< M | 2*M >;
QM := $1;
DirectSum(QM, QM);
D, i1, i2, p1, p2 := DirectSum(Q,Q);
