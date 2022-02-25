printf "Testing Universal Igusa over Q(sqrt(5))..."; //use printf with no \n
prec := 4;
F := QuadraticField(5);
ZF := Integers(F);

M := GradedRingOfHMFs(F, prec);
S4plus, S4minus := SiegelEisensteinPullback(M,[4,4]);
S6plus, S6minus := SiegelEisensteinPullback(M,[6,6]);
B10 := Basis(HMFSpace(M, [10,10]));
assert #LinearDependence([S4plus*S6plus] cat B10) eq 1;
return true;
