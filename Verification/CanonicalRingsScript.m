/*
  Usage: run the following command in ~/github/hilbertmodularforms

  parallel -j 16 --joblog joblog --eta magma -b D:={} Verification/CanonicalRingsScript.m  ::: {9..50} >> ../hilbertmodularsurfacesdata/CanonicalRingsArray.m
*/

AttachSpec("spec");

  procedure WriteCanonicalRingToFile(G,S)
    R<[x]> := CoordinateRing(Ambient(S));
    print Sprintf("R<[x]> := %m;", R);
    print "A := Proj(R);";
    printf "eqns := %o;\n", DefiningEquations(S);
    printf "C[\"%o\"] := Scheme(A,eqns);\n", LMFDBLabel(G);
  end procedure;

try 
  D := StringToInteger(D);
  if not IsFundamentalDiscriminant(D) then exit 0; end if;

  print "";
  printf "// Computing for quadratic field with discriminant %o\n", D;
  // set precision
  prec := 10;
  printf "// Computed with precision = %o\n", prec;
  // set bounds on degrees of generators and relations
  if D eq 5 then
    gen_bd := 20;
    rel_bd := 40;
  elif D eq 8 then
    gen_bd := 14;
    rel_bd := 28;
  elif D eq 12 then
    gen_bd := 14;
    rel_bd := 28;
  else
    gen_bd := 10;
    rel_bd := 20;
  end if;
  printf "// generator degree bound = %o\n", gen_bd;
  printf "// relation degree bound = %o\n", rel_bd;
  F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
  printf "F := NumberField(MinimalPolynomial(Integers(QuadraticField(%o)).2));\n", D;
  for NN in IdealsUpTo(1,F) do
    printf "// level has label %o\n", LMFDBLabel(NN);
    NCl, mp := NarrowClassGroup(F);
    mpdet := IdealRepsMapDeterministic(F, mp);
    comps := [mpdet[el] : el in NCl];
    series := [];
    // TODO: should loop over Galois orbits of components so that surface is both irreducible and defined over QQ
    for bb in comps do
      t0 := Cputime();
      printf "// component has label %o\n", LMFDBLabel(bb);
      G := CongruenceSubgroup("GL+", "Gamma0", F, NN, bb);
      // now using weighted LLL-reduced basis
      //S := HilbertModularVariety(F, NN, gen_bd, rel_bd : Precision := prec, IdealClassesSupport := [bb], Alg := "WeightedLLL");
      // now using standard basis
      S := HilbertModularVariety(F, NN, gen_bd, rel_bd : Precision := prec, IdealClassesSupport := [bb], Alg := "Standard");
      WriteCanonicalRingToFile(G,S);
      Append(~series, HilbertSeries(Ideal(S)));
      t1 := Cputime();
      printf "// Computation took %o seconds\n", t1-t0;
    end for;
    M := GradedRingOfHMFs(F,prec);
    H_trace := HilbertSeries(M,NN);
    H_test := &+series;
    if H_test eq H_trace then
      print "// Sanity check passed: Hilbert series agree!";
    else
      print "// Sanity check failed!";
      printf "// series from trace formula = %o\n", H_trace;
      printf "// computed series = %o\n", H_test;
    end if;
  end for;

  exit 0;
catch e
  WriteStderr(e);
  exit 1;
end try;
