printf "Testing that the space M_2(Gamma0(5)) for F = Q(sqrt(17)) has nonsymmetric forms"; //use printf with no \n
// Create the graded ring
F:=QuadraticField(17);
prec := 50;
M:=GradedRingOfHMFs(F, prec);

// Create the space of parallel weight [2,2] and level 7
ZF:=Integers(F);
N:= 5*ZF;
M2 := HMFSpace(M, N, [2,2]);

// Compute the basis //
B2 := Basis(M2);
B2sym:=SymmetricBasis(M2);

assert #B2 - #B2sym eq 1;

