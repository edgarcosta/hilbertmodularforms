/********************************                                             
 * Tests Bug report 143                                                      
 ********************************/

// Timing Hecke eigenvalue of f (over the field F) for prime of norm p
function time_eigenvalue(F, f, p)
    pp := PrimeIdealsOverPrime(F, p)[1];
    inert := Conjugate(pp) eq pp;
    // printf "\nEigenvalue for prime of norm %o (%o)\n",
    //  Norm(pp), inert select "inert" else "split";
    t0 := Cputime();
    ev := HeckeEigenvalue(f, pp);
    t := Cputime() - t0;
    return Norm(pp), t, ev, inert;
end function;

procedure test_Bug_143(inert_split_ratio)
    F<sqrt5> := QuadraticField(5);
    ZF := Integers(F);
    N := (1+4*sqrt5)*ZF;
    S22 := NewformDecomposition(NewSubspace(HilbertCuspForms(F, N, [2,2])));
    f79 := Eigenform(S22[1]);

    timings := [];
    evs := [];
    for p in [311,17,1381,37,2221,47] do
        np, t, ev, inert := time_eigenvalue(F, f79, p);
        Append(~timings, <np, t, inert>);
        Append(~evs, ev);
    end for;
    
    assert evs eq [20, 2, -66, 34, 46, -74];
    vprintf ModFrmHil, 1 : "%o\n", timings;

    inert_time := &+[x[2] : x in timings | x[3]];
    split_time := &+[x[2] : x in timings | not x[3]];
    total_time := inert_time + split_time;
    
    vprintf ModFrmHil,1 : "inert_time = %o\n", inert_time;
    vprintf ModFrmHil,1 : "split_time = %o\n", split_time;

    assert inert_time lt inert_split_ratio*split_time;

    vprintf ModFrmHil,1 : "total_time = %o\n", total_time;

    return;
end procedure;

// In original bug report, the ratio between inert and split was ~12
// After the fix, the ratio should be under 3
//
// The absolute time assertion was removed because it is inherently
// flaky across profiles, machines, and their loads (e.g. debug builds take ~90s vs
// ~23s for unprot). The ratio check is the meaningful regression guard.
//
// Measured ratios on 13th Gen Intel Core i9-13900KS:
//
//   Build          | inert | split | total | ratio
//   unprot/amd64   |  16.2 |   7.2 |  23.4 |  2.26
//   unprot/avx2    |  15.9 |   6.7 |  22.6 |  2.38
//   unprot/avx64   |  16.9 |   7.3 |  24.2 |  2.31
//   unprot/native  |  17.2 |   7.3 |  24.4 |  2.37
//   debug/amd64    |  56.5 |  31.3 |  87.7 |  1.81
//   debug/avx2     |  57.7 |  35.4 |  93.1 |  1.63
//   debug/avx64    |  58.0 |  36.3 |  94.3 |  1.60
//   debug/native   |  59.2 |  36.0 |  95.2 |  1.65
test_Bug_143(3);
