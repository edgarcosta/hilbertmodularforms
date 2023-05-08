/*
  Usage: run the following command in ~/github/hilbertmodularforms, or wherever config.m is located

  parallel -j 16 --joblog joblog --eta -a Ds.txt magma -b D:={} ~/Verification/CanonicalRingsScript.m  > output.txt
*/

load "config.m";
ChangeDirectory("Verification");

procedure WriteCanonicalRingToFile(F,S)
    R<[x]> := CoordinateRing(Ambient(S));
    Write("CanonicalRingsArray.m", Sprintf("R<[x]> := %m;", R));
    Write("CanonicalRingsArray.m", "A := Proj(R);");
    Write("CanonicalRingsArray.m", "eqns := DefiningEquations(S);");
    Write("CanonicalRingsArray.m", "eqns := DefiningEquations(S);");
    Write("CanonicalRingsArray.m", Sprintf("NN := ideal< Integers(F) | %o >;\n", Generators(NN)));
    Write("CanonicalRingsArray.m", "C[NN] := Scheme(A,eqns);");
end function;

//for D in [i : i in [9..50] | IsFundamentalDiscriminant(i)] do
  F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
  Write("CanonicalRingsArray.m", Sprintf("F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));", D));
  for NN in IdealsUpTo(1,F) do
    S := HilbertModularVariety(F, NN, 10, 20 : Precision := 10);
    WriteCanonicalRingToFile(F,S);
  end for;
//end for;
quit;
