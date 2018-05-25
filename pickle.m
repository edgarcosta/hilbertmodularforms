load "config.m";

// basic inputs to creation functions
F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | { 3}>;
k := [2, 2];
K := Rationals();
prec := 200;

// ModFrmHilD creation and access to attributes
M := HMFSpace(F, N, prec);

