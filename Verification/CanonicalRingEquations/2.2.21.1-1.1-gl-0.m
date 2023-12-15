// level has label 1.1
// Computed with precision = 180
// generator degree bound = 10
// relation degree bound = 20
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.21.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 4, 6, 6, 8 ], <"grevlexw", \[ 2, 4, 6, 6, 8 ]>);
A := Proj(R);
eqns := [
x[2]^3 - 1/2*x[1]*x[2]*x[4] - 4*x[3]*x[4] + 32*x[4]^2,
x[1]^4*x[2]^2 - 8*x[1]^3*x[2]*x[3] + 6912*x[1]*x[2]^2*x[3] + 64*x[1]^2*x[3]^2 + 55296*x[2]*x[3]^2 - 1/2*x[1]^5*x[4] + 192*x[1]^3*x[2]*x[4] - 204768*x[1]*x[2]^2*x[4] - 3456*x[1]^2*x[3]*x[4] - 1347840*x[2]*x[3]*x[4] + 33264*x[1]^2*x[4]^2 + 7216128*x[2]*x[4]^2 - 20736*x[2]^2*x[5] - 512*x[1]*x[3]*x[5] + 10368*x[1]*x[4]*x[5] + 1024*x[5]^2,
x[1]^3*x[2]^2*x[3] - 8*x[1]^2*x[2]*x[3]^2 - 6912*x[2]^2*x[3]^2 - 24*x[1]^3*x[2]^2*x[4] - 1/2*x[1]^4*x[3]*x[4] + 168480*x[2]^2*x[3]*x[4] - 3456*x[1]*x[3]^2*x[4] + 4*x[1]^4*x[4]^2 + 8640*x[1]^2*x[2]*x[4]^2 - 902016*x[2]^2*x[4]^2 + 130032*x[1]*x[3]*x[4]^2 - 819072*x[1]*x[4]^3 + 64*x[1]*x[2]*x[3]*x[5] + 10368*x[3]*x[4]*x[5] - 82944*x[4]^2*x[5] - 128*x[2]*x[5]^2
];
S := Scheme(A,eqns);
// Computation took 722.290 seconds
// component with label 3.1
// Hilbert modular variety with label 2.2.21.1-1.1-3.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 4, 4, 6, 10 ], <"grevlexw", \[ 2, 4, 4, 6, 10 ]>);
A := Proj(R);
eqns := [
x[2]^2 - 1/4*x[1]^2*x[3] + 14*x[2]*x[3] + 49*x[3]^2 - 2*x[1]*x[4],
x[2]*x[3]^4 + 81/11*x[3]^5 + 21/22*x[1]*x[3]^3*x[4] + 12/11*x[2]*x[3]*x[4]^2 + 93/11*x[3]^2*x[4]^2 + 1/22*x[1]*x[4]^3 - 1/22*x[1]*x[3]^2*x[5] - 1/11*x[2]*x[4]*x[5] - 4/11*x[3]*x[4]*x[5] + 1/11*x[5]^2
];
S := Scheme(A,eqns);
// Computation took 737.360 seconds
// Sanity check failed!
// series from trace formula = (-2*X^12 + X^10 - X^8 + X^6 - 2*X^4 - 1)/(X^10 - 2*X^8 + X^6 - X^4 + 2*X^2 - 1)
// computed series = (-2*t^12 + 2*t^10 - 3*t^8 + 2*t^6 - 3*t^4 + 2*t^2 - 2)/(t^10 - 2*t^8 + t^6 - t^4 + 2*t^2 - 1)
// Total computation for all components took 1464.600 seconds

