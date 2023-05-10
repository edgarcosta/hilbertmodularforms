printf "Testing Universal Igusa over Q(sqrt(d))... d="; //use printf with no \n
prec := 4;
D:=40;
printf "%o ", D;
F := QuadraticField(D);
ZF := Integers(F);
M := GradedRingOfHMFs(F, prec);
k:=[4,4];
S4plus, S4minus := SiegelEisensteinPullback(M, k);
B4 := Basis(HMFSpace(M, k));
if #LinearDependence(B4 cat [S4plus]) eq 0 then printf "Igusa test broken; pullback not in space of weight  "; printf "%o ", k[1]; end if;


