// level has label 1.1
// Computed with precision = 90
// generator degree bound = 20
// relation degree bound = 40
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.5.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 6, 20, 10 ], <"grevlexw", \[ 2, 6, 20, 10 ]>);
A := Proj(R);
eqns := [
x[1]^2*x[2]^6 + 3*x[1]^4*x[2]^2*x[3] - 1696*x[1]*x[2]^3*x[3] - 47296*x[3]^2 - 3*x[1]^3*x[2]^4*x[4] + 864*x[2]^5*x[4] - x[1]^5*x[3]*x[4] + 896*x[1]^2*x[2]*x[3]*x[4] - 16*x[1]*x[2]^3*x[4]^2 - 832*x[3]*x[4]^2 + 16*x[1]^2*x[2]*x[4]^3 + 64*x[4]^4
];
S := Scheme(A,eqns);
// Computation took 2242.400 seconds
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 2244.090 seconds

