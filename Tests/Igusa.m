printf "Testing Universal Igusa over Q(sqrt(d))... d="; //use printf with no \n
prec := 4;
for D in [5, 12] do
  printf "%o ", D;
  F := QuadraticField(D);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, prec);
  S4plus, S4minus := SiegelEisensteinPullback(M, [4,4]);
  S6plus, S6minus := SiegelEisensteinPullback(M, [6,6]);
  B4 := Basis(HMFSpace(M, [4, 4]));
  assert #LinearDependence(B4 cat [S4plus]) eq 1;
  B6:=Basis(HMFSpace(M, [6,6]));
  assert #LinearDependence(B6 cat [S6plus]) eq 1;
  B10 := Basis(HMFSpace(M, [10,10]));
  assert #LinearDependence([S4plus*S6plus] cat B10) eq 1;
  assert #LinearDependence([S4minus*S6minus] cat B10) eq 1;
end for;
return true;
