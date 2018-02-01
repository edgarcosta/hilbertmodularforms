/*****
examples using ModFrmHilD, ModFrmHilDElt
*****/

// load configuration, spec file, printing, etc.
load "config.m";

// basic inputs to creation functions
F := QuadraticField(8);
ZF := Integers(F);
N := 12*ZF;
k := [2, 2];
K := Rationals();
prec := 100;

// creation
M := HMFSpace(F, N, k, K);
f := HMFZero(F, N, k, K, prec);
g := HMFZero(F, N, k, K, 200);

// arithmetic (currently only scalar multiplication and addition are implemented)

// EigenEdgar
