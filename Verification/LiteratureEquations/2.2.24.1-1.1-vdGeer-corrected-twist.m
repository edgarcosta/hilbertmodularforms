// Algebraic comparison candidate for stored GL+ component 2.1, not a literature certificate.
// Source: G. van der Geer, Math. Ann. 233 (1978), Theorem 10, pp. 175-176;
// equation (13), also printed in Hilbert Modular Surfaces, VIII.2.20, p. 200.

// Replace -sigma4*sigma2^2 by -4*sigma4*sigma2^2 in equation (13).
// The coefficient-4 octic has six nodes and twelve A2 cusps, as described on p. 175.
// Its Jacobian scheme has length 30; the printed coefficient gives length 6.

// Write r=sigma3/sqrt(sigma4), q=delta/sqrt(sigma4), a=sigma2, c=sigma4,
// and v=Delta. Assume the sign action fixing r,a,c and negating q,v, then take
// even weights: p=r^2, a, c, w=r*q*v. Multiply the corrected branch by -3.
// Neither the sign action nor this rational descent is derived geometrically.
LitData := function(Rsrc, Rtgt)
  assert VariableWeights(Rsrc) eq [2,2,4,10];
  assert VariableWeights(Rtgt) eq [2,2,4,10];
  p := Rsrc.1; a := Rsrc.2; c := Rsrc.3; w := Rsrc.4;
  quartic := 256*c^2-128*c*a^2+16*a^4+144*c*a*p-27*c*p^2-4*a^3*p;
  I := ideal<Rsrc | w^2+3*p*a*(9*a*p-4*a^2+12*c)*c*quartic>;
  x := [Rtgt.i : i in [1..4]];
PhiImages :=[
4/9*x[1] + 1/18*x[2],
x[1],
1/3*x[3],
-20/9*x[1]^5 - 1/9*x[1]^4*x[2] + 94/9*x[1]^3*x[3] - 1/9*x[1]^2*x[2]*x[3] - 1/36*x[1]*x[2]^2*x[3] - 20/9*x[1]*x[3]^2 - 1/9*x[2]*x[3]^2 + 2/9*x[4]
];
  x := [Rsrc.i : i in [1..4]];
PsiImages :=[
x[2],
18*x[1] - 8*x[2],
3*x[3],
9*x[1]*x[2]^4 + 6*x[2]^5 + 243/2*x[1]^2*x[2]*x[3] - 81*x[1]*x[2]^2*x[3] - 129*x[2]^3*x[3] + 81*x[1]*x[3]^2 + 54*x[2]*x[3]^2 + 9/2*x[4]
];
  citation := "van der Geer Theorem 10 candidate, coefficient 4 and twist -3";
  storedSHA256 := "2551928b334e82d6101cea8ed6136d40d88142b82a65c7809978c2ef5f072bd6";
  componentLabel := "2.1";
  return I, PhiImages, PsiImages, citation, storedSHA256, componentLabel;
end function;
return LitData;
