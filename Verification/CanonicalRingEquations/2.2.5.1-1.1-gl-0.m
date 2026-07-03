// level has label 1.1
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.5.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 6, 10, 20 ], <"grevlexw", \[ 2, 6, 10, 20 ]>);
A := Proj(R);
eqns := [
x[1]^2*x[2]^6 - 3*x[1]^3*x[2]^4*x[3] + 864*x[2]^5*x[3] + 3*x[1]^4*x[2]^2*x[3]^2 - 1696*x[1]*x[2]^3*x[3]^2 - x[1]^5*x[3]^3 + 896*x[1]^2*x[2]*x[3]^3 - 47296*x[3]^4 - 16*x[1]*x[2]^3*x[4] + 16*x[1]^2*x[2]*x[3]*x[4] - 832*x[3]^2*x[4] + 64*x[4]^2
];
S := Scheme(A,eqns);
// Certified: algebraic independence verified
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 4378.150 seconds

