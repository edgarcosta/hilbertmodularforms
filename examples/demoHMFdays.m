// Demo file for HMF days, by Angie Babei
load "config.m";


// Create the graded ring

F:=QuadraticField(5);
prec:=5;
M:=GradedRingOfHMFs(F, prec);
M;

// Create the space of parallel weight [4,4] and level 1

ZF:=Integers(F);
N:=1*ZF;
M2 := HMFSpace(M, [2,2]);
M4 := HMFSpace(M, [4,4]);

// Creation functions
// Open up basis
B4:=Basis(M4);
f:=B4[1];

//Reading an HMF
f;
//Coefficients(f)[1*ZF][2*ZF];

// Eisenstein series
X := HeckeCharacterGroup(N);
triv := X!1;
eta := Random(X);
psi:=Random(X);

E2 := EisensteinSeries(M2, eta, psi);
assert #LinearDependence([E2^2] cat B4) gt 0;



// Theta series

M2theta:=HMFSpace(M,  4*ZF, [2,2]);
B2theta:=Basis(M2theta);
Mat := Matrix(ZF,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
g := ThetaSeries(M, Mat);
assert #LinearDependence([g] cat B2theta) gt 0;

// Hecke operators

h:=1/Coefficients(E2)[1*ZF][1*ZF]*E2;
h;
HeckeOperator(h, 2*ZF);



// Graded ring
prec:=4;
ZF := 1*ZF;
MaxGenWeight := 8;
MaxRelWeight := 16;


time g,r,m:=GeneratorsAndRelations(F, ZF: Precision := prec, MaxRelationWeight:=MaxRelWeight, MaxGeneratorWeight:=MaxGenWeight);

X:=MakeScheme(g,r);
print X;

// An example with non trivial unit group character

F:=QuadraticField(5);
ZF:=Integers(F);
prec:=15;
M:=GradedRingOfHMFs(F, prec);


fplus, fminus:=SiegelEisensteinPullback1(M, [4,4]);

assert IsZero(fminus);
assert Coefficients(fplus)[ZF.2+2] eq 30240;


// Narrow class number >1
F:=QuadraticField(12);
prec:=4;
M:=GradedRingOfHMFs(F, prec);
B8:=Basis(HMFSpace(M, [8,8]));


gplus, gminus:=SiegelEisensteinPullback(M, [4,4]);
// Add an assert that has the following info
//assert LinearDependence([gminus^2] cat B8)[5] eq [ 1, 0, 0, -32, 0, 60032/649, 0, -856/1947, 0 ];
