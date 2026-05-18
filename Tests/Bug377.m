/********************************                                             
 * Tests Bug report 377                                                     
 ********************************/

procedure test_sqrt6()
    K := QuadraticField(6);
    OK := MaximalOrder(K);
    P:=Factorisation(2*OK)[1,1];
    L:=Factorization(3*OK)[1,1];
    level:=P*L;
    H:=NewSubspace(HilbertCuspForms(K,level));
    // Next line originally crashed
    eigs:=NewformDecomposition(H); 
    return;
end procedure;

procedure test_cubic_field()
    R<x> := PolynomialRing(Rationals());
    K<a> := NumberField(x^3 - x^2 - 10*x + 8);
    OK:=MaximalOrder(K);
    P1:=Factorization(2*OK)[1,1];
    P2:=Factorization(2*OK)[2,1];
    P3:=Factorization(2*OK)[3,1];
    //Computing for the level P1^4*P2*P3
    level2:=P1^4*P2*P3;
    H2:=NewSubspace(HilbertCuspForms(K,level2));
    // Next line originally crashed
    eigs2:=NewformDecomposition(H2);
    return;
end procedure;

procedure test_Bug_377()
    test_sqrt6();
    test_cubic_field();
end procedure;

test_Bug_377();