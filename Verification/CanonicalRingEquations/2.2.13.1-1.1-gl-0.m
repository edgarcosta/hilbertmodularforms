// level has label 1.1
// using Standard algorithm
// component with label 1.1
// Hilbert modular variety with label 2.2.13.1-1.1-1.1-gl-0
R<[x]> := PolynomialRing(RationalField(), [ 2, 4, 6, 6, 8 ], <"grevlexw", \[ 2, 
4, 6, 6, 8 ]>);
A := Proj(R);
eqns := [
x[2]^3 - x[1]*x[2]*x[4] - 4*x[3]*x[4] + 4*x[4]^2,
x[1]^4*x[2]^2 - 4*x[1]^3*x[2]*x[3] - 816*x[1]*x[2]^2*x[3] + 16*x[1]^2*x[3]^2 + 
3456*x[2]*x[3]^2 - x[1]^5*x[4] + 4*x[1]^3*x[2]*x[4] - 2932*x[1]*x[2]^2*x[4] + 
784*x[1]^2*x[3]*x[4] + 9872*x[2]*x[3]*x[4] + 2948*x[1]^2*x[4]^2 - 
11600*x[2]*x[4]^2 + 912*x[2]^2*x[5] - 64*x[1]*x[3]*x[5] - 912*x[1]*x[4]*x[5] + 
64*x[5]^2
];
S := Scheme(A,eqns);
// Certified: algebraic independence verified
// Sanity check passed: Hilbert series agree!
// Total computation for all components took 16.800 seconds

