
load "config.m";

F<nu> := QuadraticField(6);
ZF := Integers(F);
N := ideal<ZF|[1]>;
prec := 50;
M := HMFSpace(F, prec);

Cl := NarrowClassGroup(M);
mp := NarrowClassGroupMap(M);

bb := mp(Cl.1);
basis := Basis(bb);
t := 5;

Attach("ModFrmHilD/deprecated/ModFrmHilDMult.m");
