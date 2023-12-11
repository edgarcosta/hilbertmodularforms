printf "Testing GaloisDescent argument...";
F:=QuadraticField(10);
prec:=1;
M:=GradedRingOfHMFs(F, prec);
ZF:=Integers(F);
N:= 23*ZF;
M2 := HMFSpace(M, N, [2,2]);
time C2 := CuspFormBasis(M2 : ViaTraceForm:=false);
delete M2`CuspFormBasis;
// recompute without GaloisDescent
time noC2 := CuspFormBasis(M2 : GaloisDescent:=false);
