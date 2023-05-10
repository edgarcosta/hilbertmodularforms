printf "Testing GaloisDescent argument...";
F:=QuadraticField(10);
prec:=1;
M:=GradedRingOfHMFs(F, prec);
NumberOfCoefficients(M);
F:=QuadraticField(10);
prec:=1;
M:=GradedRingOfHMFs(F, prec);
ZF:=Integers(F);
N:= 23*ZF;
M2 := HMFSpace(M, N, [2,2]);
C2 := CuspFormBasis(M2);
delete M2`CuspFormBasis;
// recompute without GaloisDescent
C2 := CuspFormBasis(M2 : GaloisDescent:=false);
