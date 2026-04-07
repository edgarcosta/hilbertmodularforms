procedure test_Bug422()
    F := QuadraticField(149);
    O<w> := Integers(F);
    M := HilbertCuspForms(F, 1*O);
    S := NewformDecomposition(M : Dimensions := [ 2 ]);
    assert IsEmpty(S);
end procedure;

test_Bug422();