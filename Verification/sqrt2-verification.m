//load "config.m";
QQ := Rationals();
// hardcoded the equations, so don't have to recompute
/*
  M := QuadSpace(2,100);
  K<nu> := CoefficientField(M);
  ZK := Integers(K);
  G,R := ConstructGeneratorsAndRelations(M,1*ZK,2,16);
  //G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,18);
  G1,R1 := Relations(M,G,R,30);
  S := MakeScheme(G1,R1);

  //G,R,Q := ConstructGeneratorsAndRelations(M,2,16);
  //G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,30);
  //S := MakeScheme(G1,R1);

  P_wtd<X2, X14, X4, X6> := Ambient(S);
  eqns_S := DefiningEquations(S);
*/

P<X2,X4,X6,X14> := PolynomialRing(QQ,[2,4,6,14]);
PolyList := [-X14^2 + 2*X2*X14*X4^3 - X2^2*X4^6 + X2^2*X14*X4*X6 + 20*X14*X4^2*X6 - 276*X2*X4^5*X6 + 2*X2*X14*X6^2 - 80*X2^2*X4^3*X6^2 - 1124*X4^4*X6^2 - 740*X2*X4^2*X6^3 - X2^2*X6^4 - 1728*X4*X6^4];
PolyList2 := [27*(X14)^2 + (X4*(X6-4*X2*X4))*X6*(-4*(X2^2 +12*X4)^3 + (27*X6 + 2*(X2)^3 - 72*X2*X4)^2)];
//P_wtd<X2, X14, X4, X6> := Proj(P);
P_wtd := Proj(P);
S := Scheme(P_wtd, PolyList);
S_vdG := Scheme(P_wtd, PolyList2);
eqns_S := DefiningEquations(S);
eqns_S_vdG := DefiningEquations(S_vdG);
F_S := eqns_S[1];
F_S_vdG := eqns_S_vdG[1];

Pvars<a2_1, a4_1, a4_2, a6_1, a6_2, a6_3, a14_1, a14_2, a14_3, a14_4, a14_5, a14_6, a14_7, a14_8, a14_9> := PolynomialRing(QQ,15);
Pa<X2, X4, X6, X14> := ChangeRing(P,Pvars);
F2 := a2_1*X2;
F4 := a4_1*X2^2 + a4_2*X4;
F6 := a6_1*X2^3 + a6_2*X2*X4 + a6_3*X6;
F14 := a14_1*X2^7 + a14_2*X2^5*X4 + a14_3*X2^3*X4^2 + a14_4*X2*X4^3 + a14_5*X2^4*X6 + a14_6*X2^2*X4*X6 + a14_7*X4^2*X6 + a14_8*X2*X6^2 + a14_9*X14;
aut_polys := [F2, F4, F6, F14];
F_S_aut := Evaluate(F_S, aut_polys);
difference := F_S_aut - Pa!F_S_vdG;
coeffs := Coefficients(difference);
I := ideal< Pvars | coeffs>;
G := GroebnerBasis(I);
solns := SolveZeroDimIdeal(I);

