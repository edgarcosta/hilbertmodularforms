printf "Testing that the space S_2(Gamma0(7)) for F = Q(sqrt(5)) is correct"; //use printf with no \n
// Create the graded ring
F:=QuadraticField(5);
prec:=5;
M:=GradedRingOfHMFs(F, prec);

// Create the space of parallel weight [2,2] and level 7
ZF:=Integers(F);
N:= Factorization(7*ZF)[1][1];
M2 := HMFSpace(M, N, [2,2]);

// Compute the basis //
B2 := CuspFormBasis(M2);

assert #(B2) eq 1;

return true;

//In the future, add further check of coefficients
