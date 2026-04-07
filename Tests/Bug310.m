/********************************                                             
 * Tests Bug report 310                                                      
 ********************************/

procedure test_Bug_310()
    QQ := Rationals();
    _<x> := PolynomialRing(QQ);
    m4 := x^3 + x^2 - 4*x + 1;
    F<c> := NumberField(m4);
    O := Integers(F);   
    I13 := Factorisation(13*O)[1, 1];
    I2 := 2*O;
    I3:=3*O;
    N0:=I2*I3*I13;
    D:=I2*I3*I13;
    H := QuaternionAlgebra(D,InfinitePlaces(F));
    OH := MaximalOrder(H);
    M := HilbertCuspForms(F,N0);
    N := NewSubspace(M : QuaternionOrder := OH);
    T7 := HeckeOperator(N,7*O);
    return;
end procedure;

test_Bug_310();