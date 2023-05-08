/*
  Usage: run the following command in ~/github/hilbertmodularforms, or wherever spec is located

  parallel -j 16 --joblog joblog --eta magma -b D:={} Verification/CanonicalRingsScript.m  ::: {9..50} > output.txt
*/

AttachSpec("spec");

try 
  D := StringToInteger(D);
  if not IsFundamentalDiscriminant(D) then exit 0; end if;
  procedure WriteCanonicalRingToFile(F,NN,S)
      R<[x]> := CoordinateRing(Ambient(S));
      print Sprintf("R<[x]> := %m;", R);
      print "A := Proj(R);";
      print "eqns := DefiningEquations(S);";
      print "eqns := DefiningEquations(S);";
      print Sprintf("NN := ideal< Integers(F) | %o >;\n", Generators(NN));
      print "C[NN] := Scheme(A,eqns);";
  end procedure;


  //for D in [i : i in [9..50] | IsFundamentalDiscriminant(i)] do
    F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
    Write("CanonicalRingsArray.m", Sprintf("F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));", D));
    for NN in IdealsUpTo(1,F) do
      S := HilbertModularVariety(F, NN, 10, 20 : Precision := 10);
      WriteCanonicalRingToFile(F,NN,S);
    end for;
//end for;
  exit 0;
catch e
  WriteStderr(e);
  exit 1;
end try;
