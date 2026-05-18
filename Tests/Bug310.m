/********************************
 * Tests Bug report 310
 *
 * ElementsOfNorm had an assertion
 *   assert {Norm(x) : x in elts} eq {n};
 * that crashes when elts is empty. This test uses a definite
 * quaternion algebra over Q(sqrt(2)) with disc = (3)*(5) (h=8)
 * where some right ideal classes have no elements of norm 7,
 * triggering the empty case through the Neighbors code path.
 ********************************/

procedure test_Bug_310()
    QQ := Rationals();
    _<x> := PolynomialRing(QQ);
    F<a> := NumberField(x^2 - 2);
    O := Integers(F);
    I3 := Factorisation(3*O)[1,1];
    I5 := Factorisation(5*O)[1,1];
    D := I3*I5;
    H := QuaternionAlgebra(D, InfinitePlaces(F));
    OH := MaximalOrder(H);
    rids := RightIdealClasses(OH);
    assert #rids eq 8;
    found_empty := false;
    for I in rids do
        elts := ElementsOfNorm(I, 7);
        norms := {Norm(x) : x in elts};
        assert IsEmpty(norms) or (norms eq {7});
        if IsEmpty(norms) then found_empty := true; end if;
    end for;
    assert found_empty;
    return;
end procedure;

test_Bug_310();
