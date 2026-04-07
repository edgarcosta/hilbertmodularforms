procedure test_Bug443()
    K := QuadraticField(6);
    OK := MaximalOrder(K);
    P:= Factorization(2*OK)[1,1];
    Q:=Factorization(3*OK)[1,1];
    level := P^8*Q;
    M:=HilbertCuspForms(K,level);
    MN:=NewSubspace(M);
    // This command was failing due to an assertion in precompute_tps
    eigenspaces:=NewformDecomposition(MN);
end procedure;

test_Bug443();