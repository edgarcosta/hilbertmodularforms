SetDebugOnError(true);
load "config.m";

_<x>:=PolynomialRing(Rationals());
prec := 30;
i := 13;
F:=NumberField(x^2-i);

Cl, mp:=NarrowClassGroup(F);
reps:=[mp(g):g in Cl];
ZF := reps[1];

MaxGenWeight := 10;
MaxRelWeight := 20;

p := 2;
TestLevel := p*ZF;

time g,r,m:=GeneratorsAndRelations(F,TestLevel: Precision := prec, MaxRelationWeight:=MaxRelWeight, MaxGeneratorWeight:=MaxGenWeight);

X:=MakeScheme(g,r);
print X;
