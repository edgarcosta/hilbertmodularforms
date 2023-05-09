/*
  Usage: run the following command in ~/github/hilbertmodularforms, or wherever spec is located

  parallel -j 16 --joblog joblog --eta magma -b D:={} Verification/CanonicalRingsScript.m  ::: {9..50} >> Verification/CanonicalRingsArray.m
*/

AttachSpec("spec");

try 
  D := StringToInteger(D);
  if not IsFundamentalDiscriminant(D) then exit 0; end if;
  // TODO: deal with multiplying forms supported on only one component
  if not NarrowClassNumber(NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2))) eq 1 then exit 0; end if;
  procedure WriteCanonicalRingToFile(G,S)
      R<[x]> := CoordinateRing(Ambient(S));
      print Sprintf("R<[x]> := %m;", R);
      print "A := Proj(R);";
      printf "eqns := %o;\n", DefiningEquations(S);
      printf "C[%o] := Scheme(A,eqns);\n", LMFDBLabel(G);
  end procedure;


  //for D in [i : i in [9..50] | IsFundamentalDiscriminant(i)] do
    print "";
    printf "// Computing for quadratic field with discriminant %o\n", D;
    F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
    printf "F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));\n", D;
    for NN in IdealsUpTo(1,F) do
      NCl, mp := NarrowClassGroup(F);
      mpdet := IdealRepsMapDeterministic(F, mp);
      comps := [mpdet[el] : el in NCl];
      for bb in comps do
        G := CongruenceSubgroup("GL+", "Gamma0", F, NN, bb);
        if Discriminant(F) eq 5 then
          S := HilbertModularVariety(F, NN, 20, 40 : Precision := 10, IdealClassesSupport := [bb]);
        elif Discriminant(F) eq 8 then
          S := HilbertModularVariety(F, NN, 14, 28 : Precision := 10, IdealClassesSupport := [bb]);
        else
          S := HilbertModularVariety(F, NN, 10, 20 : Precision := 10, IdealClassesSupport := [bb]);
        end if;
        WriteCanonicalRingToFile(G,S);
      end for;
    end for;
//end for;
  exit 0;
catch e
  WriteStderr(e);
  exit 1;
end try;
