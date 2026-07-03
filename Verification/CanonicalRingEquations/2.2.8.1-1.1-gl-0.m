// level has label 1.1
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.8.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 4, 6, 14 ], <"grevlexw", \[ 2, 4, 6, 14 ]>);
A := Proj(R);
eqns := [
x[1]^2*x[2]^6 + 276*x[1]*x[2]^5*x[3] + 80*x[1]^2*x[2]^3*x[3]^2 + 1124*x[2]^4*x[3]^2 + 740*x[1]*x[2]^2*x[3]^3 + x[1]^2*x[3]^4 + 1728*x[2]*x[3]^4 - 2*x[1]*x[2]^3*x[4] - x[1]^2*x[2]*x[3]*x[4] - 20*x[2]^2*x[3]*x[4] - 2*x[1]*x[3]^2*x[4] + x[4]^2
];
S := Scheme(A,eqns);
// Certified: algebraic independence verified
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 755.610 seconds

