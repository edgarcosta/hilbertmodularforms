// A selected component contributes its own dimensions to the series comparison.
procedure test_strict_component_subset()
    F := QuadraticField(3);
    N := 1*Integers(F);
    M := GradedRingOfHMFs(F, 1);
    comps := NarrowClassGroupReps(M);
    assert #comps eq 2;
    bb := comps[2];

    Q<t> := FunctionField(Rationals());
    // The dimension formula for either level-one component; independently, Basis with
    // IdealClassesSupport gives dimensions 1, 2, 3, 4 in weights 2, 4, 6, 8.
    expected := (1 + t^14)/((1 - t^2)*(1 - t^4)*(1 - t^6));
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
end procedure;

// Unequal component dimensions distinguish selection from averaging the total.
procedure test_unequal_components()
    F := QuadraticField(6);
    N := 1*Integers(F);
    M := GradedRingOfHMFs(F, 1);
    bb := NarrowClassGroupReps(M)[2];
    assert Norm(bb) eq 2;

    Q<t> := FunctionField(Rationals());
    // The dimension formula for the norm-2 component; independently, Basis with
    // IdealClassesSupport gives dimensions 2, 4, 6 in weights 2, 4, 6.
    expected := (1 + t^10)/((1 - t^2)^2*(1 - t^4));
    P<[y]> := PolynomialRing(Rationals(), [2, 2, 4, 10]);
    I := ideal<P | y[4]^2 - y[1]^10>;
    sane, H_trace, H_test := HilbertSeriesSanityCheck(M, N, [I]
        : IdealClassesSupport := [bb]);
    assert sane;
    assert H_trace eq expected;
    assert H_test eq expected;
    assert H_trace ne (HilbertSeries(M, N) + 1)/2;
    assert not HilbertSeriesSanityCheck(M, N, [I]
        : IdealClassesSupport := [N]);
end procedure;

// No component at this level has elliptic points; HilbertSeries(Gamma) must still give
// component series that sum to the trace-formula series.
procedure test_components_without_elliptic_points()
    F := QuadraticField(7);
    N := [NN : NN in IdealsUpTo(14, F) | Norm(NN) eq 14][1];
    M := GradedRingOfHMFs(F, 1);
    comps := NarrowClassGroupReps(M);
    assert #comps eq 2;

    Q<t> := FunctionField(Rationals());
    H := Q!0;
    for bb in comps do
        Gamma := CongruenceSubgroup("GL+", "Gamma0", F, N, bb);
        assert IsEmpty(Keys(EllipticPointData(Gamma)));
        // HilbertSeries(Gamma) indexes weight 2m by t^m.
        H +:= Evaluate(HilbertSeries(Gamma), t^2);
    end for;
    assert H eq HilbertSeries(M, N) + 1;
end procedure;

test_strict_component_subset();
test_unequal_components();
test_components_without_elliptic_points();
