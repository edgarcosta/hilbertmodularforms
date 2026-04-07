/********************************                                             
 * Tests Bug report 58                                                      
 ********************************/

procedure test_Bug_58(seed1, seed2)
    // SetSeed(1869775440, 18585);
    SetSeed(seed1, seed2);
    F := QuadraticField(5);
    ZF := Integers(F);
    N := ideal<ZF|[41, 2*ZF.2 + 12]>;
    hcf := HilbertCuspForms(F, N, [6,2]);
    decomposition := NewformDecomposition( NewSubspace(hcf));
    eigforms := [* Eigenform(d) : d in decomposition *];
    return;
end procedure;

// Trying a few
// to make sure we are not passing the test accidentally
N := 10;
for i in [1..N] do
    test_Bug_58(1869775440, i);
end for;

exit;
