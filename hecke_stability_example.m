load "config.m";

F := QuadraticField(5);
ZF<w> := Integers(F);
N := ideal<ZF | {1}>;
prec := 50;
M := HMFSpace(F, prec);

k := [1, 1];
H := HeckeCharacterGroup(N);

