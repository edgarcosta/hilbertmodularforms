
procedure test_sqrt5()
    // Hirzebruch's Scheme
    R<w,x,y,z> := PolynomialRing(Rationals(),[2,6,10,20]);
    PS := ProjectiveSpace(R);
    P := z^2 -y*(3125*y^3 + 2000*y^2*x*w^2 + 256*y^2*w^5 - 900*y*x^3*w - 128*y*x^2*w^4 + 16*x^4*w^3 + 108*x^5);
    S := Scheme(PS,P);
    // Our Scheme
    R1<X2,X6,X10,X20> := PolynomialRing(Rationals(),[2,6,10,20]);
    PS1 := ProjectiveSpace(R1);
    P1 := -X2^2*X6^6 + 16*X2*X6^3*X20 - 64*X20^2 + 3*X2^3*X6^4*X10 - 864*X6^5*X10 - 16*X2^2*X6*X20*X10 - 3*X2^4*X6^2*X10^2 + 1696*X2*X6^3*X10^2 + 832*X20*X10^2 + X2^5*X10^3 - 896*X2^2*X6*X10^3 + 47296*X10^4;
    S1 := Scheme(PS1,P1);
    assert IsIsomorphic(S, S1);
end procedure;

procedure test_sqrt2()
    QQ := Rationals();
    P<X2,X4,X6,X14> := PolynomialRing(QQ,[2,4,6,14]);
    P_wtd := Proj(P);
    // van der Geer's equations
    PolyList2 := [27*(X14)^2 + (X4*(X6-4*X2*X4))*X6*(-4*(X2^2 +12*X4)^3 + (27*X6 + 2*(X2)^3 - 72*X2*X4)^2)];
    S_vdG := Scheme(P_wtd, PolyList2);
    // our equations
    PolyList := [-X14^2 + 2*X2*X14*X4^3 - X2^2*X4^6 + X2^2*X14*X4*X6 + 20*X14*X4^2*X6 - 276*X2*X4^5*X6 + 2*X2*X14*X6^2 - 80*X2^2*X4^3*X6^2 - 1124*X4^4*X6^2 - 740*X2*X4^2*X6^3 - X2^2*X6^4 - 1728*X4*X6^4];
    S := Scheme(P_wtd, PolyList);
    assert IsIsomorphic(S, S_vdG);
end procedure;

procedure test_sqrt13()
    QQ := Rationals();
    P<X2,X4,X6,Y6,X8> := PolynomialRing(QQ,[2,4,6,6,8]);
    P_wtd := Proj(P);
    // van der Geer's equations
    // given in van de Geer - Zagier paper on Q(sqrt(13)) on page 120
    PolynomialList := [X4^3 - X6*Y6, X8^2 - (256*X2^5*X6 - 128*X2^4*X4^2 + 16*X2^3*X4*Y6 -656*X2^3*X4*X6 +776*X2^2*X4^3 -261*X2*X4^2*Y6 + 27*X4*Y6^2 -27*X2^2*X6^2 +495/2*X2*X4^2*X6 -947/16*X4^4 +54*X4*X6^2)];
    S_vdG := Scheme(P_wtd, PolynomialList);
    // The older stored equations
    eqns_S :=
	[
	    -X4^3 + X2*X4*Y6 + 4*X6*Y6 - 4*Y6^2,
	    -X2^4*X4^2 + 4*X2^3*X4*X6 + 416*X2*X4^2*X6 - 16*X2^2*X6^2 - 3456*X4*X6^2 + X2^5*Y6 - 4*X2^3*X4*Y6 - 268*X2*X4^2*Y6 - 384*X2^2*X6*Y6 + 2928*X4*X6*Y6 + 252*X2^2*Y6^2 - 1200*X4*Y6^2 - 112*X4^2*X8 + 64*X2*X6*X8 + 112*X2*Y6*X8 - 64*X8^2
	];
    S := Scheme(P_wtd, eqns_S);
    assert IsIsomorphic(S, S_vdG);
    // The old stored equations
    StoredAmbient<[x]> := ProjectiveSpace(Rationals(), [1,2,3,3,4]);
    storedEquations := [
	-x[2]^3 + x[1]*x[2]*x[4] + 4*x[3]*x[4] - 4*x[4]^2,
	-x[1]^4*x[2]^2 + 4*x[1]^3*x[2]*x[3] + 816*x[1]*x[2]^2*x[3] - 16*x[1]^2*x[3]^2 - 3456*x[2]*x[3]^2 + x[1]^5*x[4] - 4*x[1]^3*x[2]*x[4] + 2932*x[1]*x[2]^2*x[4] - 784*x[1]^2*x[3]*x[4] - 9872*x[2]*x[3]*x[4] - 2948*x[1]^2*x[4]^2 + 11600*x[2]*x[4]^2 - 912*x[2]^2*x[5] + 64*x[1]*x[3]*x[5] + 912*x[1]*x[4]*x[5] - 64*x[5]^2];
    storedS := Scheme(StoredAmbient, storedEquations);
    assert IsIsomorphic(S, storedS);
    // The new equations
    storedEquations := [
     x[2]^3 - x[1]*x[2]*x[4] - 4*x[3]*x[4] + 4*x[4]^2,
     x[1]^4*x[2]^2 - 4*x[1]^3*x[2]*x[3] - 176*x[1]*x[2]^2*x[3] + 16*x[1]^2*x[3]^2 + 3456*x[2]*x[3]^2 - x[1]^5*x[4] + 4*x[1]^3*x[2]*x[4] - 212*x[1]*x[2]^2*x[4] + 144*x[1]^2*x[3]*x[4] - 1008*x[2]*x[3]*x[4] + 228*x[1]^2*x[4]^2 - 720*x[2]*x[4]^2 - 368*x[2]^2*x[5] - 64*x[1]*x[3]*x[5] + 368*x[1]*x[4]*x[5] + 64*x[5]^2];
    storedS := Scheme(StoredAmbient, storedEquations);
    assert IsIsomorphic(S, storedS);
end procedure;

import "ModFrmHilD/CanonicalRing/IO.m": SetPrecisionAndBounds;
procedure test_sqrt13_dynamic()
  F := LMFDBField("2.2.13.1");
  NN := LMFDBIdeal(F, "1.1");
  prec, gen_bd, rel_bd := SetPrecisionAndBounds(NN);
  S := HilbertModularVariety(F, NN, gen_bd, rel_bd : Precision := prec, IdealClassesSupport := false, Alg := "Standard");
  // Compare with van der Geer-Zagier
  QQ := Rationals();
  P<X2,X4,X6,Y6,X8> := PolynomialRing(QQ,[2,4,6,6,8]);
  P_wtd := Proj(P);
  // van der Geer's equations
  // given in van de Geer - Zagier paper on Q(sqrt(13)) on page 120
  PolynomialList := [X4^3 - X6*Y6, X8^2 - (256*X2^5*X6 - 128*X2^4*X4^2 + 16*X2^3*X4*Y6 -656*X2^3*X4*X6 +776*X2^2*X4^3 -261*X2*X4^2*Y6 + 27*X4*Y6^2 -27*X2^2*X6^2 +495/2*X2*X4^2*X6 -947/16*X4^4 +54*X4*X6^2)];
  S_vdG := Scheme(P_wtd, PolynomialList);
  assert IsIsomorphic(S_vdG, S);
end procedure;

printf "testing D=5, ";
test_sqrt5();
printf "8, ";
test_sqrt2();
printf "13, ";
test_sqrt13();
printf "13 dynamic";
test_sqrt13_dynamic();
