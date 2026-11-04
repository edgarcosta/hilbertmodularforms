// Elkies-Kumar, Algebra & Number Theory 8 (2014), 2297-2411, Section 7.
// On the X2 chart: a=X4/X2^2, b=X6/X2^3, t=X14/X2^7.

// SHA256 of the source files in https://arxiv.org/src/1209.3527v3:
// allhms.txt   65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc
// 8/igusa8.txt 58707dbad72f895da9286a06817ddd43c97d4f147e9d184044c1c30b96a568e7

P<a, b, t> := PolynomialRing(Rationals(), 3);
K := FieldOfFractions(P);
Q<r, s, z> := PolynomialRing(Rationals(), 3);
L := FieldOfFractions(Q);
f := Q!(32*r^3 + 64*r^2*s + 48*r^2 + 32*r*s^2 - 80*r*s + 24*r - 2*s + 4);
Z := -2*t + 2*a^3 + a*b + 20*a^2*b + 2*b^2;
q := b*(a + 4*b)^2/(2*a);
branch := Evaluate(f, [K | -2*b/(a + 4*b), -8*a^3/(b*(a + 4*b)), 0])*q^2;
assert Denominator(branch) eq 1;
phiFF := [K | -2*b/(a + 4*b), -8*a^3/(b*(a + 4*b)), Z/q];
ai := r*s/(16*(2*r + 1)^2);
bi := -r^2*s/(32*(2*r + 1)^3);
qi := bi*(ai + 4*bi)^2/(2*ai);
psiFF := [L | ai, bi, (2*ai^3 + ai*bi + 20*ai^2*bi + 2*bi^2 - qi*z)/2];
H := PolynomialRing(Rationals(), [2, 4, 6, 14]);
pullbacks := [H |
  H.1^2 + 144*H.2,
  H.1^3 - 648*H.1*H.2 - 1728*H.3,
  -H.2*H.3/4,
  H.2^3 + H.1*H.2*H.3/12 + H.3^2
];
excludedEK := Q!(256*r^7*s + 1088*r^6*s^2 + 1152*r^6*s + 1840*r^5*s^3 +
  2048*r^5*s^2 + 2112*r^5*s + 1440*r^4*s^4 + 552*r^4*s^3 - 688*r^4*s^2 +
  2016*r^4*s + 432*r^3*s^5 - 792*r^3*s^4 - 1968*r^3*s^3 - 2896*r^3*s^2 +
  1056*r^3*s - 1179*r^2*s^4 + 3172*r^2*s^3 - 1516*r^2*s^2 + 288*r^2*s +
  72*r*s^3 - 160*r*s^2 + 32*r*s);
A1 := L!(2*r*s^2);
A := L!(-(9*r*s + 4*r^2 + 4*r + 1)/3);
B1 := L!(r*s^2*(3*s + 8*r - 2)/3);
B := L!(-(54*r^2*s + 81*r*s - 16*r^3 - 24*r^2 - 12*r - 2)/27);
B2 := L!(r^2);
IEK := [L | -24*B1/A1, -12*A, 96*(A/A1)*B1 - 36*B, -4*A1*B2];
witness_format := eval (Read("examples/_elkies_kumar.m")
  cat "return witness_format;");
return rec<witness_format | P := P, K := K, Q := Q, L := L, f := f, Z := Z,
  branch := P!branch, phiFF := phiFF, psiFF := psiFF, pullbacks := pullbacks,
  excludedEK := excludedEK, IEK := IEK>;
