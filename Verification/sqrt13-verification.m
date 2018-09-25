load "config.m";
QQ := Rationals();
M := QuadSpace(13,100);
G,R,Q := ConstructGeneratorsAndRelations(M,2,10);
G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,18);
S := MakeScheme(G1,R1);
P24668<X2, X4, X6, Y6, X8> := Ambient(S);
eqns_S := DefiningEquations(S);

// equation given in Van de Geer - Zagier paper on Q(sqrt(13)) on page 120
P<A,B,C,D,E> := PolynomialRing(QQ,[2,4,6,6,8]);
//PS := ProjectiveSpace(P);
PolynomialList := [B^3 - C*D, E^2 - (256*A^5*C - 128*A^4*B^2 + 16*A^3*B*D -656*A^3*B*C +776*A^2*B^3 -261*A*B^2*D + 27*B*D^2 -27*A^2*C^2 +495/2*A*B^2*C -947/16*B^4 +54*B*C^2)];
S_VdG := Scheme(P24668, PolynomialList);
eqns_S_VdG := DefiningEquations(S_VdG);

// write an map with undetermined coefficients to try to find an isomorphism between S and S_VdG
Pvars<a2_1, a4_1, a4_2, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6> := PolynomialRing(QQ,17);
Pa<A,B,C,D,E> := ChangeRing(P,Pvars);
F2 := a2_1*A;
F4 := a4_1*A^2 + a4_2*B;
F6 := a6_1*A^3 + a6_2*A*B + a6_3*C + a6_4*D;
F6_2 := a6_5*A^3 + a6_6*A*B + a6_7*C + a6_8*D;
F8 := a8_1*A^8 + a8_2*A^2*B + a8_3*B^2 + a8_4*A*C + a8_5*A*D + a8_6*E;
aut_polys := [F2, F4, F6, F6_2, F8];
eqns_S_aut := [Evaluate(poly, aut_polys) : poly in eqns_S];
diffs := [eqns_S_aut[i] - (Pa!eqns_S_VdG[i]) : i in [1..#eqns_S_VdG]];
coeffs := [];
for poly in diffs do
  coeffs := coeffs cat Coefficients(poly);
end for;

G2 := a2_1*A;
G4 := -B; // a4_2^3 = -1, so...
G6 := a6_2*A*B + a6_3*C + a6_4*D;
G6_2 := a6_7*C + a6_8*D;
G8 := a8_2*A^2*B + a8_3*B^2 + a8_4*A*C + a8_5*A*D + a8_6*E;
aut_polys2 := [G2, G4, G6, G6_2, G8];
eqns_S_aut2 := [Evaluate(poly, aut_polys2) : poly in eqns_S];

diffs := [eqns_S_aut2[i] - (Pa!eqns_S_VdG[i]) : i in [1..#eqns_S_VdG]];
coeffs := [];
for poly in diffs do
  coeffs := coeffs cat Coefficients(poly);
end for;

H2 := a2_1*A;
H4 := -B; // a4_2^3 = -1, so...
H6 := (1/4*a2_1)*A*B + a6_3*C + a6_4*D;
H6_2 := a6_3*C;
H8 := a8_2*A^2*B + a8_3*B^2 + a8_4*A*C + a8_5*A*D + a8_6*E;
aut_polys3 := [H2, H4, H6, H6_2, H8];
eqns_S_aut3 := [Evaluate(poly, aut_polys3) : poly in eqns_S];

diffs := [eqns_S_aut3[i] - (Pa!eqns_S_VdG[i]) : i in [1..#eqns_S_VdG]];
coeffs := [];
for poly in diffs do
  coeffs := coeffs cat Coefficients(poly);
end for;
