printf "\n\tTesting Theta series example over Q(sqrt(13))... ";
F := QuadraticField(13);
ZF := Integers(F);
prec:=6;
M := GradedRingOfHMFs(F, prec);

// Theta series
M2theta:=HMFSpace(M,  4*ZF, [2,2]);
B2theta:=Basis(M2theta);
Mat := Matrix(ZF,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
g := ThetaSeries(M, Mat);
assert #LinearDependence([g] cat B2theta) gt 0;
print "Success!";
return true;
