// level has label 1.1
// Computed with precision = 90
// generator degree bound = 10
// relation degree bound = 20
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.13.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 4, 6, 6, 8 ], <"grevlexw", \[ 2, 4, 6, 6, 8 ]>);
A := Proj(R);
eqns := [
x[2]^3 - x[1]*x[2]*x[4] - 4*x[3]*x[4] + 4*x[4]^2,
x[1]^4*x[2]^2 - 4*x[1]^3*x[2]*x[3] - 416*x[1]*x[2]^2*x[3] + 16*x[1]^2*x[3]^2 + 3456*x[2]*x[3]^2 - x[1]^5*x[4] + 4*x[1]^3*x[2]*x[4] + 268*x[1]*x[2]^2*x[4] + 384*x[1]^2*x[3]*x[4] - 2928*x[2]*x[3]*x[4] - 252*x[1]^2*x[4]^2 + 1200*x[2]*x[4]^2 + 112*x[2]^2*x[5] - 64*x[1]*x[3]*x[5] - 112*x[1]*x[4]*x[5] + 64*x[5]^2,
x[1]^3*x[2]^2*x[3] - 4*x[1]^2*x[2]*x[3]^2 - 864*x[2]^2*x[3]^2 - x[1]^3*x[2]^2*x[4] - x[1]^4*x[3]*x[4] + 8*x[1]^2*x[2]*x[3]*x[4] + 732*x[2]^2*x[3]*x[4] + 416*x[1]*x[3]^2*x[4] + x[1]^4*x[4]^2 - 4*x[1]^2*x[2]*x[4]^2 - 300*x[2]^2*x[4]^2 - 684*x[1]*x[3]*x[4]^2 + 268*x[1]*x[4]^3 + 16*x[1]*x[2]*x[3]*x[5] - 112*x[3]*x[4]*x[5] + 112*x[4]^2*x[5] - 16*x[2]*x[5]^2
];
S := Scheme(A,eqns);
// Computation took 31.150 seconds
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 32.110 seconds

