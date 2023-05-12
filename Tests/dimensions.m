procedure testDimension(G,k)
    F := BaseField(G);
    N := Level(G);
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    hmf := HMFSpace(R, N, [k,k]);
    
    assert DimensionOfCuspForms(G,k) eq CuspDimension(hmf);
end procedure;

DN_bound := 500;
num_attempts := 10;
ds := [d : d in [2..DN_bound] | IsFundamentalDiscriminant(d)];

weights := [k : k in [2..16 by 2]];

printf "Checking dimensions at ";
for _ in [1..num_attempts] do
    d := Random(ds);
    k := Random(weights);
    F := QuadraticField(d);
    ZF := Integers(F);
    N := Random(IdealsUpTo(Floor(DN_bound/d),F));
    cg, cg_map := NarrowClassGroup(F);
    b := Random(cg);
    B := cg_map(b);
    printf "(%o;%o;%o),", d,IdealOneLine(N),IdealOneLine(B);
    a := CoprimeNarrowRepresentative(B,N);
    assert IsTotallyPositive(a);
    assert a*B + N eq 1*Order(N);
    B := a*B;
    G_SL := CongruenceSubgroup("SL", "Gamma0", F, N, B);
    testDimension(G_SL,k);
    G_GL := CongruenceSubgroup("GL+", "Gamma0", F, N, B);
    testDimension(G_GL,k);
end for;
