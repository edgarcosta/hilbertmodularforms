// Weight zero has one constant per component of the Hilbert modular variety.
procedure test_quadratic_component_constants()
    F := QuadraticField(3);
    N := 1*Integers(F);
    M := GradedRingOfHMFs(F, 1);
    assert NarrowClassNumber(M) eq 2;
    PS<t> := PowerSeriesRing(Rationals(), 16);
    H := HilbertSeries(M, N);
    error if Coefficient(PS!H, 0) ne 2,
        Sprintf("Quadratic trace series: expected constant 2, got %o",
            Coefficient(PS!H, 0));
    assert H eq HilbertSeries(F, N);
    assert H eq HilbertSeries(M);
    assert [Coefficient(PS!H, k) : k in [2..12 by 2]] eq [2, 4, 6, 8, 10, 14];
end procedure;

// Non-quadratic fields use the trace formula through the field overload too.
procedure test_cubic_component_constants()
    P<x> := PolynomialRing(Rationals());
    F := NumberField(x^3 - 7*x - 5);
    N := 1*Integers(F);
    M := GradedRingOfHMFs(F, 1);
    assert Degree(F) eq 3;
    assert NarrowClassNumber(M) eq 2;
    PS<t> := PowerSeriesRing(Rationals(), 2);
    H := HilbertSeries(F, N);
    error if Coefficient(PS!H, 0) ne 2,
        Sprintf("Cubic field series: expected constant 2, got %o",
            Coefficient(PS!H, 0));
    assert H eq HilbertSeries(M, N);
    assert H eq HilbertSeries(M);
end procedure;

test_quadratic_component_constants();
test_cubic_component_constants();
