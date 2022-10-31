F<nu> := QuadraticField(5);
ZF := Integers(F);
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
//Ugens := [mpU(el) : el in Generators(U)];
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
//mpM := Coercion(ZF, M);
mpM := hom< ZF -> M | x :-> x*M.1>;
QM, mpQM := quo< M | 2*M >; // I don't think this is what I want...
mpQtoQM := hom< Q -> QM | x :-> mpQM(mpM(x @@ mpQ))>;
D, i1, i2, p1, p2 := DirectSum(QM,QM); //Magma is too dumb for this to work
//D, i1, i2, p1, p2 := DirectSum(M,M);
//DQ, mpDQ := quo< D | [i1(2*M.1), i2(2*M.1)] >;
//units := [mpQM(mpM(mpU(el))) : el in Generators(U)];
D_seq := [(a @@ mpQ)*D.1+(b @@ mpQ)*D.2 : a,b in Q];
//D_seq := [mpDQ(i1(mpQtoQM(a)) + i2(mpQtoQM(b))) : a,b in Q];
D_seq0 := D_seq;
Remove(~D_seq,1);
orbits := [];
while #D_seq ne 0 do
  d := D_seq[#D_seq];
  printf "d = %o, in position %o\n", d, #D_seq;
  //Remove(~D_seq,#D_seq);
  orb_d := [d];
  for u in UQ do
    printf "u = %o\n", mpUQ(u);
    new := (mpUQ(u) @@ mpQ)*d;
    //new := mpUQ(u)*d;
    new := i1(p1(new)) + i2(p2(new)); // this is really dumb
    printf "new = %o\n", new;
    printf "in position %o\n", Index(D_seq0,new);
    Append(~orb_d, new);
    if new in D_seq then
      Remove(~D_seq, Index(D_seq,new));
    end if;
  end for;
  Append(~orbits, orb_d);
end while;
