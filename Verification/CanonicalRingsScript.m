load "config.m";
ChangeDirectory("Verification");

//for D in [i : i in [1..50] | IsFundamentalDiscriminant(i)] do
for D in [13] do
  F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
  Write("CanonicalRingsArray.m", Sprintf("F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));", D));
  for NN in IdealsUpTo(1,F) do
    S := HilbertModularVariety(F, NN, 10, 20 : Precision := 10);
    R<[x]> := CoordinateRing(Ambient(S));
    Write("CanonicalRingsArray.m", Sprintf("R<[x]> := %m;", R));
    Write("CanonicalRingsArray.m", "A := Proj(R);");
    Write("CanonicalRingsArray.m", "eqns := DefiningEquations(S);");
    Write("CanonicalRingsArray.m", "eqns := DefiningEquations(S);");
    Write("CanonicalRingsArray.m", Sprintf("NN := ideal< Integers(F) | %o >;\n", Generators(NN)));
    Write("CanonicalRingsArray.m", "C[NN] := Scheme(A,eqns);");
  end for;
end for;
