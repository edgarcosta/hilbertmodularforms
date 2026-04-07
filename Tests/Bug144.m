/********************************                                             
 * Tests Bug report 144                                                      
 ********************************/

procedure test_Bug_144()
    F<sqrt5> := QuadraticField(5);
    ZF := Integers(F);
    N := (1+4*sqrt5)*ZF;
    S24 := NewformDecomposition(NewSubspace(HilbertCuspForms(F, N, [2,4])));
    h1 := Eigenform(S24[1]);
    h2 := Eigenform(S24[2]);
    a := HeckeEigenvalue(h2, 2*ZF);
    return;
end procedure;

test_Bug_144();
exit;