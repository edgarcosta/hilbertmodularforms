// Demo file for HMF days
load "config.m";

// Create the graded ring
F:=QuadraticField(13);
prec:=4;
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
Coefficients(f)[1*ZF][1];

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
h:=1/(Coefficients(E2)[1*ZF][1])*E2;
h;
hecke_h := HeckeOperator(h, 2*ZF);

// Graded ring
prec:=10;
MaxGenWeight := 8;
MaxRelWeight := 16;

time H := HilbertModularSurface(F, 1*ZF,MaxGenWeight,MaxRelWeight: Precision := prec );

/// Igusa unit character not 1
prec := 4;
F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, prec);
a,b,c,d,e,f := UniversalIgusa(M);

/* This part of the demo still does not run
function Slash(eta, k, M)
// eta a totally positive unit,
// an even parallel weight k
// a graded ring M
// returns the HMF f_k|[[eta, 0],[0, 1]] where f_k is the pullback of of the Siegel Eisenstein series of weight k over the field F. Only defined on the component [1*ZF]
	F:=BaseField(M);
	prec:=M`Precision;
	ZF:=Integers(F);
	coeffs := AssociativeArray();
	repcoeffs := AssociativeArray();
	bb:=1*ZF;
    numcoeffs := #ShintaniReps(M)[bb];
    elts := ShintaniReps(M)[bb];
    for j := 1 to numcoeffs do
       repcoeffs[ShintaniRepresentativeToIdeal(M, bb,elts[j])]:=Coeff(elts[j]*eta^(-1),k[1]); //Coeff(reps[i],elts[j]*eta^(-1),Weight(f)[1]);
    end for;
    coeffs[bb]:=repcoeffs;
 	A := HMF(HMFSpace(M, k), CompleteCoeffsZeros(M, coeffs));
 	return A;
end function;

eta:=Integers(F)!(Integers(F).2+2);

a1:=Slash(eta, [4,4], GR);
b1:=Slash(eta, [6,6], GR);

LinearDependence([a+a1] cat B4 : IdealClasses:=[1*ZF]);
LinearDependence([b+b1] cat B6: IdealClasses:=[1*ZF]);

assert LinearDependence([a+a1] cat B4 : IdealClasses:=[1*ZF])[3] eq [ 1, -1, -1, -2520/23, 0 ];
assert LinearDependence([b+b1] cat B6: IdealClasses:=[1*ZF])[4] eq [ 1, -1, -1, 15007608/122713, 0, 7161/122713, 0 ];


f:=a-a1;
g:=b-b1;
*/

// once we get the unit characters implemented, we want the following
//assert LinearDependence([f*g] cat B10 : IdealClasses:=[1*ZF])[6] eq [ 1, 0, 0, -13218209762345280/15151705053833, 0, 365338373818355/90910230322998, 0, -17337475078945/4363691055503904, 0, 57065308895/52364292666046848, 0 ];
