SetNthreads(1);
printf "Checking Hilbert-series sanity with narrow class number 2...";
F := QuadraticField(3);
M := GradedRingOfHMFs(F, 1);
N := 1*Integers(F);
assert NarrowClassNumber(M) eq 2;

// Each level-one component has series (1+t^14)/((1-t^2)*(1-t^4)*(1-t^6)).
P<[x]> := PolynomialRing(Rationals(), [2, 4, 6, 14]);
I := ideal<P | x[4]^2 - x[1]^14>;
sane, H_trace, H_test := HilbertSeriesSanityCheck(M, N, [I, I]);
PS<t> := PowerSeriesRing(Rationals(), 16);
printf "constant terms: trace=%o, components=%o\n",
    Coefficient(PS!H_trace, 0), Coefficient(PS!H_test, 0);
assert sane;
assert Coefficient(PS!H_trace, 0) eq 2;
assert H_trace eq HilbertSeries(F, N);
assert HilbertSeriesSanityCheck(M, N, [quo<P | I>, quo<P | I>]);
S := Scheme(Proj(P), I);
assert HilbertSeriesSanityCheck(M, N, [S, S]);

assert not HilbertSeriesSanityCheck(M, N, [I]);
J := ideal<P | x[4]^2 - x[1]^14, x[2]>;
assert not HilbertSeriesSanityCheck(M, N, [I, J]);
printf "PASSED\n";
