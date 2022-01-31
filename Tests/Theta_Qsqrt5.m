printf "Testing Theta series example over Q(sqrt(5))...";
F := QuadraticField(5);
ZF := Integers(F);
prec:=6;
M := GradedRingOfHMFs(F, prec);

// Theta series
M2theta:=HMFSpace(M,  4*ZF, [2,2]);
B2theta:=Basis(M2theta);
Mat := Matrix(ZF,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
g := ThetaSeries(M, Mat);
assert #LinearDependence([g] cat B2theta) gt 0;
return true;
