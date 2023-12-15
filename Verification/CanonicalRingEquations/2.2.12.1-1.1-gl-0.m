// level has label 1.1
// Computed with precision = 190
// generator degree bound = 14
// relation degree bound = 28
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.12.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 14, 4, 6 ], <"grevlexw", \[ 2, 14, 4, 6 ]>);
A := Proj(R);
eqns := [
20*x[1]^3*x[2]*x[3]^2 - 23712*x[1]*x[2]*x[3]^3 + 644*x[1]^2*x[3]^6 - 1312*x[3]^7 + x[1]^4*x[2]*x[4] - 1584*x[1]^2*x[2]*x[3]*x[4] - 83696*x[2]*x[3]^2*x[4] + 7568*x[1]*x[3]^5*x[4] - 96*x[1]*x[2]*x[4]^2 - 4*x[1]^2*x[3]^3*x[4]^2 + 27648*x[3]^4*x[4]^2 - 16*x[1]*x[3]^2*x[4]^3 + 4*x[1]^2*x[4]^4 + 16*x[3]*x[4]^4
];
S := Scheme(A,eqns);
// Computation took 3796.340 seconds
// component with label 2.1
// Hilbert modular variety with label 2.2.12.1-1.1-2.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 14, 4, 6 ], <"grevlexw", \[ 2, 14, 4, 6 ]>);
A := Proj(R);
eqns := [
-3/2*x[1]^3*x[2]*x[3]^2 + 48*x[1]*x[2]*x[3]^3 + 3/4*x[1]^4*x[3]^5 - 48*x[1]^2*x[3]^6 + 3328*x[3]^7 + x[1]^2*x[2]*x[3]*x[4] + 10816*x[2]*x[3]^2*x[4] - 9024*x[1]*x[3]^5*x[4] - 32*x[1]*x[2]*x[4]^2 + 16*x[1]^2*x[3]^3*x[4]^2 - 1/8*x[1]^5*x[4]^3 + 12*x[1]^3*x[3]*x[4]^3 - 1920*x[1]*x[3]^2*x[4]^3 + 1872*x[1]^2*x[4]^4 + 256*x[3]*x[4]^4
];
S := Scheme(A,eqns);
// Computation took 3561.600 seconds
// Sanity check failed!
// series from trace formula = (-2*X^12 + X^10 + X^6 - X^4 - 1)/(X^10 - 2*X^8 + X^6 - X^4 + 2*X^2 - 1)
// computed series = (-2*t^12 + 2*t^10 - 2*t^8 + 2*t^6 - 2*t^4 + 2*t^2 - 2)/(t^10 - 2*t^8 + t^6 - t^4 + 2*t^2 - 1)
// Total computation for all components took 7365.250 seconds

