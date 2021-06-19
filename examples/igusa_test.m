load "config.m";

_<x>:=PolynomialRing(Rationals());
prec :=10;


//// D= 5
i := 5;
F:=NumberField(x^2-i);
Cl, mp:=NarrowClassGroup(F);
reps:=[mp(g):g in Cl];
ZF := reps[1];
GR := GradedRingOfHMFs(F,prec);


B4:=Basis(HMFSpace(GR, [4,4]));
B6:=Basis(HMFSpace(GR, [6,6]));
B10:=Basis(HMFSpace(GR, [10,10]));
B12:=Basis(HMFSpace(GR, [12,12]));



a,b,c,d,e,f:=UniversalIgusaV2(GR);
LinearDependence([a] cat B4 : IdealClasses:=[reps[1]]);
LinearDependence([b] cat B6: IdealClasses:=[reps[1]]);
LinearDependence([c] cat B10 : IdealClasses:=[reps[1]]);
LinearDependence([d] cat B12: IdealClasses:=[reps[1]]);
LinearDependence([e] cat B10 : IdealClasses:=[reps[1]]);
LinearDependence([f] cat B12: IdealClasses:=[reps[1]]);


/// D=12
i := 12;
F:=NumberField(x^2-i);
Cl, mp:=NarrowClassGroup(F);
reps:=[mp(g):g in Cl];
ZF := reps[1];
GR := GradedRingOfHMFs(F,prec);


B4:=Basis(HMFSpace(GR, [4,4]));
B6:=Basis(HMFSpace(GR, [6,6]));
B10:=Basis(HMFSpace(GR, [10,10]));
B12:=Basis(HMFSpace(GR, [12,12]));



a,b,c,d,e,f:=UniversalIgusaV2(GR);
LinearDependence([a] cat B4 : IdealClasses:=[reps[1]]);
LinearDependence([b] cat B6: IdealClasses:=[reps[1]]);
LinearDependence([c] cat B10 : IdealClasses:=[reps[1]]);
LinearDependence([d] cat B12: IdealClasses:=[reps[1]]);
LinearDependence([e] cat B10 : IdealClasses:=[reps[1]]);
LinearDependence([f] cat B12: IdealClasses:=[reps[1]]);
