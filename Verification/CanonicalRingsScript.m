/*
  Usage: run the following command in ~/github/hilbertmodularforms, or wherever spec is located

  parallel -j 16 --joblog joblog --eta magma -b D:={} Verification/CanonicalRingsScript.m  ::: {9..50} > Verification/CanonicalRingsArray.m
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
      print Sprintf("NN := ideal< Integers(F) | %o >;\n", Generators(NN));
      print "C[NN] := Scheme(A,eqns);";
  end procedure;


  //for D in [i : i in [9..50] | IsFundamentalDiscriminant(i)] do
    F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
    printf "F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));", D;
    for NN in IdealsUpTo(1,F) do
      if Discriminant(F) eq 5 then
        S := HilbertModularVariety(F, NN, 20, 40 : Precision := 10);
      elif Discriminant(F) eq 8 then
        S := HilbertModularVariety(F, NN, 14, 28 : Precision := 10);
      else
        S := HilbertModularVariety(F, NN, 10, 20 : Precision := 10);
      end if;
      WriteCanonicalRingToFile(F,NN,S);
    end for;
//end for;
  exit 0;
catch e
  WriteStderr(e);
  exit 1;
end try;
