// SearchGradedIsomorphism (Verification/IsIsomorphic.m) on the three literature
// canonical-ring comparisons. Each search runs a few tens of 0-dimensional Variety
// solves; the three searches total about 20 seconds.
//  D=8  (weights [2,4,6,14]):    ours (Fours)      -> Hirzebruch (SF)
//  D=5  (weights [2,6,10,20]):   literature (fH)   -> ours (fO)
//  D=13 (weights [2,4,6,6,8]):   vdG (F,G)         -> ours (F',G')  [permutes the two
//                                                    weight-6 generators]
// Success = the finder returns a map that VerifyGradedIsomorphism confirms (it need not
// equal any by-hand map; any confirmed map is a valid witness).
printf "SearchGradedIsomorphism on D=5, D=8, D=13...\n";
Q := Rationals();

Check := procedure(name, I, J)
  t0 := Cputime();
  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  printf "  %o: found=%o [%o s]\n", name, found, Cputime(t0);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

// ---- D=8 ----
R8<X2,X4,X6,X14> := PolynomialRing(Q,[2,4,6,14]);
Fours := X2^2*X4^6 + 276*X2*X4^5*X6 + 80*X2^2*X4^3*X6^2 + 1124*X4^4*X6^2
  + 740*X2*X4^2*X6^3 + X2^2*X6^4 + 1728*X4*X6^4
  - 2*X2*X4^3*X14 - X2^2*X4*X6*X14 - 20*X4^2*X6*X14 - 2*X2*X6^2*X14 + X14^2;
disc := (X4*(X6-4*X2*X4))*X6*(-4*(X2^2+12*X4)^3 + (27*X6+2*X2^3-72*X2*X4)^2);
SF := 27*X14^2 - disc;
Check("D=8", ideal<R8|Fours>, ideal<R8|SF>);

// ---- D=5 ----
RH<w,x,y,z> := PolynomialRing(Q, [2,6,10,20]);
fH := z^2 - y*(3125*y^3 + 2000*y^2*x*w^2 + 256*y^2*w^5 - 900*y*x^3*w
             - 128*y*x^2*w^4 + 16*x^4*w^3 + 108*x^5);
RO<X2,X6,X10,X20> := PolynomialRing(Q, [2,6,10,20]);
fO := -X2^2*X6^6 + 16*X2*X6^3*X20 - 64*X20^2 + 3*X2^3*X6^4*X10 - 864*X6^5*X10
      - 16*X2^2*X6*X20*X10 - 3*X2^4*X6^2*X10^2 + 1696*X2*X6^3*X10^2 + 832*X20*X10^2
      + X2^5*X10^3 - 896*X2^2*X6*X10^3 + 47296*X10^4;
toRH := hom< RO -> RH | [w, x, y, z] >;
Check("D=5", ideal<RH|fH>, ideal<RH| toRH(fO) >);

// ---- D=13 (two relations; weight-6 permutation) ----
R13<X2,X4,X6,Y6,X8> := PolynomialRing(Q, [2,4,6,6,8]);
F := X4^3 - X6*Y6;
G := X8^2 - (256*X2^5*X6 - 128*X2^4*X4^2 + 16*X2^3*X4*Y6 - 656*X2^3*X4*X6
            + 776*X2^2*X4^3 - 261*X2*X4^2*Y6 + 27*X4*Y6^2 - 27*X2^2*X6^2
            + 495/2*X2*X4^2*X6 - 947/16*X4^4 + 54*X4*X6^2);
Fp := X4^3 - X2*X4*Y6 - 4*X6*Y6 + 4*Y6^2;
Gp := X2^4*X4^2 - 4*X2^3*X4*X6 - 816*X2*X4^2*X6 + 16*X2^2*X6^2 + 3456*X4*X6^2
      - X2^5*Y6 + 4*X2^3*X4*Y6 - 2932*X2*X4^2*Y6 + 784*X2^2*X6*Y6 + 9872*X4*X6*Y6
      + 2948*X2^2*Y6^2 - 11600*X4*Y6^2 + 912*X4^2*X8 - 64*X2*X6*X8 - 912*X2*Y6*X8 + 64*X8^2;
Check("D=13", ideal<R13|F,G>, ideal<R13|Fp,Gp>);

printf "PASSED\n";
