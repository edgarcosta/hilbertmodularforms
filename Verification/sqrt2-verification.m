load "config.m";
QQ := Rationals();
/*
M := QuadSpace(2,100);
G,R,Q := ConstructGeneratorsAndRelations(M,2,16);
G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,30);
S := MakeScheme(G1,R1);

P_wtd<X2, X14, X4, X6> := Ambient(S);
eqns_S := DefiningEquations(S);
*/

P<X2,X4,X6,X14> := PolynomialRing(Rationals(),[2,4,6,14]);
PolyList := [-X14^2 + 2*X2*X14*X4^3 - X2^2*X4^6 + X2^2*X14*X4*X6 + 20*X14*X4^2*X6 - 276*X2*X4^5*X6 + 2*X2*X14*X6^2 - 80*X2^2*X4^3*X6^2 - 1124*X4^4*X6^2 - 740*X2*X4^2*X6^3 - X2^2*X6^4 - 1728*X4*X6^4];
PolyList2 := [27*(X14)^2 + (X4*(X6-4*X2*X4))*X6*(-4*(X2^2 +12*X4)^3 + (27*X6 + 2*(X2)^3 - 72*X2*X4)^2)];
//P_wtd<X2, X14, X4, X6> := Proj(P);
P_wtd := Proj(P);
S := Scheme(P_wtd, PolyList);
S_VdG := Scheme(P_wtd, PolyList2);
eqns_S_VdG := DefiningEquations(S_VdG);