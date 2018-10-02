//load "config.m";
QQ := Rationals();
// hardcoded the equations, so don't have to recompute
/*
  M := QuadSpace(13,100);
  //G,R,Q := ConstructGeneratorsAndRelations(M,2,10);
  K<nu> := CoefficientField(M);
  ZK := Integers(K);
  G,R := ConstructGeneratorsAndRelations(M,1*ZK,2,10);
  //G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,18);
  G1,R1 := Relations(M,G,R,18);
  S := MakeScheme(G1,R1);
  P_wtd<X2, X4, X6, Y6, X8> := Ambient(S);
  eqns_S := DefiningEquations(S);
  P := Parent(eqns_S[1]);
*/
P<X2,X4,X6,Y6,X8> := PolynomialRing(QQ,[2,4,6,6,8]);
eqns_S :=
[
-X4^3 + X2*X4*Y6 + 4*X6*Y6 - 4*Y6^2,
-X2^4*X4^2 + 4*X2^3*X4*X6 + 416*X2*X4^2*X6 - 16*X2^2*X6^2 - 3456*X4*X6^2 + X2^5*Y6 - 4*X2^3*X4*Y6 - 268*X2*X4^2*Y6 - 384*X2^2*X6*Y6 + 2928*X4*X6*Y6 + 252*X2^2*Y6^2 - 1200*X4*Y6^2 - 112*X4^2*X8 + 64*X2*X6*X8 + 112*X2*Y6*X8 - 64*X8^2
];
P_wtd := Proj(P);
S := Scheme(P_wtd, eqns_S);

// equation given in van de Geer - Zagier paper on Q(sqrt(13)) on page 120
//P<A,B,C,D,E> := PolynomialRing(QQ,[2,4,6,6,8]);
//PS := ProjectiveSpace(P);
//PolynomialList := [B^3 - C*D, E^2 - (256*A^5*C - 128*A^4*B^2 + 16*A^3*B*D -656*A^3*B*C +776*A^2*B^3 -261*A*B^2*D + 27*B*D^2 -27*A^2*C^2 +495/2*A*B^2*C -947/16*B^4 +54*B*C^2)];
PolynomialList := [X4^3 - X6*Y6, X8^2 - (256*X2^5*X6 - 128*X2^4*X4^2 + 16*X2^3*X4*Y6 -656*X2^3*X4*X6 +776*X2^2*X4^3 -261*X2*X4^2*Y6 + 27*X4*Y6^2 -27*X2^2*X6^2 +495/2*X2*X4^2*X6 -947/16*X4^4 +54*X4*X6^2)];
S_vdG := Scheme(P_wtd, PolynomialList);
eqns_S_vdG := DefiningEquations(S_vdG);

// write an map with undetermined coefficients to try to find an isomorphism between S and S_vdG
//Pvars<a2_1, a4_1, a4_2, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6> := PolynomialRing(QQ,17);
Pvars<a2_1, a4_1, a4_2, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6> := FunctionField(QQ,17);
Pa<X2,X4,X6,Y6,X8> := ChangeRing(P,Pvars);
F2 := a2_1*X2;
F4 := a4_1*X2^2 + a4_2*X4;
F6 := a6_1*X2^3 + a6_2*X2*X4 + a6_3*X6 + a6_4*Y6;
F6_2 := a6_5*X2^3 + a6_6*X2*X4 + a6_7*X6 + a6_8*Y6;
F8 := a8_1*X2^8 + a8_2*X2^2*X4 + a8_3*X4^2 + a8_4*X2*X6 + a8_5*X2*Y6 + a8_6*X8;
/*
  Pa<A,B,C,D,E> := ChangeRing(P,Pvars);
  F2 := a2_1*A;
  F4 := a4_1*A^2 + a4_2*B;
  F6 := a6_1*A^3 + a6_2*A*B + a6_3*C + a6_4*D;
  F6_2 := a6_5*A^3 + a6_6*A*B + a6_7*C + a6_8*D;
  F8 := a8_1*A^8 + a8_2*A^2*B + a8_3*B^2 + a8_4*A*C + a8_5*A*D + a8_6*E;
*/
aut_polys := [F2, F4, F6, F6_2, F8];
eqns_S_aut := [Evaluate(poly, aut_polys) : poly in eqns_S];
// form Groebner basis for equations of S_vdG
// reduce polys in eqns_S_aut to normal form wrt to this Groeber basis
eqns_S_vdG_vars := [Pa!eqn : eqn in eqns_S_vdG];
G := GroebnerBasis(eqns_S_vdG_vars);
reduced := [NormalForm(poly,G) : poly in eqns_S_aut];
coeffs := [];
for f in reduced do
  coeffs cat:= Coefficients(f);
end for;
// not working...try to guess some "obvious" relations
//coeffs cat:= [a4_1, a4_2 + 1];
coeffs cat:= [a4_2 + 1];
coeffs := [Numerator(el) : el in coeffs];
SetVerbose("Groebner",3);
G_vars := GroebnerBasis(coeffs);
Pvars_poly := Integers(Pvars);
I := ideal< Pvars_poly | G_vars >;
/*
  diffs := [eqns_S_aut[i] - (Pa!eqns_S_vdG[i]) : i in [1..#eqns_S_vdG]];
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

  diffs := [eqns_S_aut2[i] - (Pa!eqns_S_vdG[i]) : i in [1..#eqns_S_vdG]];
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

  diffs := [eqns_S_aut3[i] - (Pa!eqns_S_vdG[i]) : i in [1..#eqns_S_vdG]];
  coeffs := [];
  for poly in diffs do
    coeffs := coeffs cat Coefficients(poly);
  end for;
*/
