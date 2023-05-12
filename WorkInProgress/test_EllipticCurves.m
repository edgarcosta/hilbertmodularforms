R<x> := PolynomialRing(Rationals());
K<phi> := NumberField(R![-1, -1, 1]);
// from LMFDB conductor norm 145.1
// http://www.lmfdb.org/EllipticCurve/2.2.5.1/?start=0&field=2.2.5.1&conductor_norm=145&include_isogenous=off
eqns := [[0, phi + 1, phi, -9*phi - 9, -31*phi - 23],
       [phi, -phi - 1, 0, 1, 0],
       [0, 0, phi, -783*phi - 163, -5687*phi - 11611]];
K5 := QuadraticField(5);
_, m5 := IsIsomorphic(K, K5);
Es := [ EllipticCurve(m5(eqn)) : eqn in eqns];
prec := 100;
M := GradedRingOfHMFs(K5, prec);
// 5s
time HMFEquipWithMultiplication(M);
time fs := [EllipticCurveToHMF(M, E) : E in Es];
