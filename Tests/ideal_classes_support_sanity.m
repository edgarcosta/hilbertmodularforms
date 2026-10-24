SetNthreads(4);
printf "Checking Hilbert-series sanity on a strict component subset...\n";
F := QuadraticField(3);
N := 1*Integers(F);
M := GradedRingOfHMFs(F, 1);
comps := NarrowClassGroupReps(M);
assert #comps eq 2;
bb := comps[2];

Q<t> := FunctionField(Rationals());
expected := (1+t^14)/((1-t^2)*(1-t^4)*(1-t^6));
P<[x]> := PolynomialRing(Rationals(), [2, 4, 6, 14]);
I := ideal<P | x[4]^2 - x[1]^14>;
sane, H_trace, H_test := HilbertSeriesSanityCheck(M, N, [I]
    : IdealClassesSupport := [bb]);
assert sane;
assert H_trace eq expected;
assert H_test eq expected;
assert not HilbertSeriesSanityCheck(M, N, [I]);
assert HilbertSeriesSanityCheck(M, N, [I, I]
    : IdealClassesSupport := Reverse(comps));
assert HilbertSeriesSanityCheck(M, N, [quo<P | I>]
    : IdealClassesSupport := [bb]);
S := Scheme(Proj(P), I);
assert HilbertSeriesSanityCheck(M, N, [S]
    : IdealClassesSupport := [bb]);
J := ideal<P | x[4]^2 - x[1]^14, x[2]>;
assert not HilbertSeriesSanityCheck(M, N, [J]
    : IdealClassesSupport := [bb]);
printf "Selected component series agrees: %o\n", H_trace;

// These components have different dimensions, so averaging the total cannot work.
F6 := QuadraticField(6);
N6 := 1*Integers(F6);
M6 := GradedRingOfHMFs(F6, 1);
bb6 := NarrowClassGroupReps(M6)[2];
assert Norm(bb6) eq 2;
P6<[y]> := PolynomialRing(Rationals(), [2, 2, 4, 10]);
I6 := ideal<P6 | y[4]^2 - y[1]^10>;
expected6 := (1+t^10)/((1-t^2)^2*(1-t^4));
sane6, H_trace6, H_test6 := HilbertSeriesSanityCheck(M6, N6, [I6]
    : IdealClassesSupport := [bb6]);
assert sane6;
assert H_trace6 eq expected6;
assert H_test6 eq expected6;
assert H_trace6 ne (HilbertSeries(M6, N6) + 1)/2;
assert not HilbertSeriesSanityCheck(M6, N6, [I6]
    : IdealClassesSupport := [N6]);
printf "Unequal components checked: selected dimensions differ from the average\n";

F7 := QuadraticField(7);
N7 := [NN : NN in IdealsUpTo(14, F7) | Norm(NN) eq 14][1];
M7 := GradedRingOfHMFs(F7, 1);
comps7 := NarrowClassGroupReps(M7);
assert #comps7 eq 2;
H7 := Q!0;
for bb7 in comps7 do
    Gamma7 := CongruenceSubgroup("GL+", "Gamma0", F7, N7, bb7);
    assert IsEmpty(Keys(EllipticPointData(Gamma7)));
    sane7, H_trace7, H_test7 := HilbertSeriesSanityCheck(M7, N7, [I]
        : IdealClassesSupport := [bb7]);
    assert not sane7;
    H7 +:= H_trace7;
end for;
assert H7 eq HilbertSeries(M7, N7) + 1;
printf "Components without elliptic points agree with the total trace series\n";
printf "PASSED\n";
