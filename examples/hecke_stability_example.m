load "config.m";

F := QuadraticField(5);
ZF<w> := Integers(F);
N := ideal<ZF | {7}>;
prec := 100;
M := HMFSpace(F, prec);

k := [2,2];
//There's no particular reason to make these characters trivial--but they work.
//eta := H ! 1;
/* psi := H ! 1; */
//psi := eta;
//All eisenstein series we are using as candidates
//E := EisensteinSeries(M, N, eta, psi, ke);
//print E;
//ListSignatures(GrpHecke);
//for eta in Elements(H) do
//  print Modulus(eta);
//end for;
//A := Generators(H);
//print #H;
//print "Done";
print HeckeStability(M, N, k);

//print #S;
