// level has label 1.1
// Computed with precision = 100
// generator degree bound = 14
// relation degree bound = 28
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.8.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 14, 4, 6 ], <"grevlexw", \[ 2, 14, 4, 6 ]>);
A := Proj(R);
eqns := [
276*x[1]*x[2]*x[3]^3 + 80*x[1]^2*x[3]^6 - 20*x[3]^7 + x[1]^2*x[2]*x[3]*x[4] + 1124*x[2]*x[3]^2*x[4] + 740*x[1]*x[3]^5*x[4] - 2*x[1]*x[2]*x[4]^2 - x[1]^2*x[3]^3*x[4]^2 + 1728*x[3]^4*x[4]^2 - 2*x[1]*x[3]^2*x[4]^3 + x[1]^2*x[4]^4 + x[3]*x[4]^4
];
S := Scheme(A,eqns);
// Computation took 353.820 seconds
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 355.180 seconds

