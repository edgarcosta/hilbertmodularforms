load "config.m";

_<x>:=PolynomialRing(Rationals());
prec := 10;
i := 5;
F:=NumberField(x^2-i);
Cl, mp:=NarrowClassGroup(F);
reps:=[mp(g):g in Cl];
ZF := reps[1];
GR := GradedRingOfHMFs(F,prec);


a,b,c,d,e,f:=UniversalIgusa(GR);
