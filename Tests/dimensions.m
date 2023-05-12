procedure testDimension(F,N,k)
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    hmf := HMFSpace(R, N, [k,k]);
    // Summing over all components to get the total
    cg, cg_map := NarrowClassGroup(F);
    dim_sl := 0;
    dim_gl := 0;
    for b in cg do
	B := cg_map(b);
	a := CoprimeNarrowRepresentative(B,N);
	assert IsTotallyPositive(a);
	assert a*B + N eq 1*Order(N);
	B := a*B;
	// G_SL := CongruenceSubgroup("SL", "Gamma0", F, N, B);
	// dim_sl +:= DimensionOfCuspForms(G_SL,k);
	G_GL := CongruenceSubgroup("GL+", "Gamma0", F, N, B);
	dim_gl +:= DimensionOfCuspForms(G_GL,k);
    end for;
    
    dim_hmf := 0;
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    X := HeckeCharacterGroup(N,[1,2]);
    chis := [chi : chi in Elements(X) | IsTrivial(DirichletRestriction(chi))];
    for chi in chis do
	hmf := HMFSpace(R, N, [k,k], chi);
	dim_hmf +:= CuspDimension(hmf);
    end for;
    assert dim_gl eq dim_hmf;
end procedure;

DN_bound := 500;
num_attempts := 10;
ds := [d : d in [2..DN_bound] | IsFundamentalDiscriminant(d)];

weights := [k : k in [2..12 by 2]];

printf "Checking dimensions at ";
for _ in [1..num_attempts] do
    d := Random(ds);
    k := Random(weights);
    F := QuadraticField(d);
    ZF := Integers(F);
    N := Random(IdealsUpTo(Floor(DN_bound/d),F));
    printf "(%o;%o;%o),", d,IdealOneLine(N),k;
    testDimension(F,N,k);
end for;


// Long test
/*
for d in ds do
for k in weights do
F := QuadraticField(d);
    ZF := Integers(F);
for N in IdealsUpTo(Floor(DN_bound/d),F) do
printf "(%o;%o;%o),", d,IdealOneLine(N),k;
    testDimension(F,N,k);
end for;
end for;
end for;
*/
