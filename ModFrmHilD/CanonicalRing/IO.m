// given a discriminant D and level NN
// return the precision, generators bound, and relations bound
// TODO: dependence on level?
function SetPrecisionAndBounds(NN)
  F := NumberField(Order(NN));
  D := Discriminant(F);
  if D eq 5 then
    gen_bd := 20;
  elif D eq 8 then
    gen_bd := 14;
  elif D eq 12 then
    gen_bd := 14;
  else
    gen_bd := 10;
  end if;
  return Integers()!ComputePrecisionFromHilbertSeries(NN, gen_bd), gen_bd, 2*gen_bd;
end function;

/*
  function SetPrecisionAndBounds(D, NN)
    if D eq 5 then
      return 10, 20, 40;
    elif D eq 8 then
      return 10, 14, 28;
    elif D eq 12 then
      return 10, 14, 28;
    else
      return 10, 10, 20;
    end if;
  end function;
*/

function ConvertLabel(label)
  // convert congruence subgroup label to label for writing (no component)
  spl := Split(label,"-");
  assert #spl eq 5;
  return Join(spl[1..2] cat spl[4..5], "-");
end function;

intrinsic WriteCanonicalSurfaceToString(label::MonStgElt, S::Sch) -> MonStgElt
  {}
  s := Sprintf("// Hilbert modular variety with label %o\n", label);
  R<[x]> := CoordinateRing(Ambient(S));
  s *:= Sprintf("R<[x]> := %m;\n", R);
  s *:= "A := Proj(R);\n";
  s *:= Sprintf("eqns := %o;\n", DefiningEquations(S));
  s *:= "S := Scheme(A,eqns);\n";
  return s;
end intrinsic;


// TODO: should support all ambient types and Gamma types
// Need to add to HilbertModularVariety (requires unit character?)
intrinsic WriteCanonicalRingComputationToFile(F::FldNum, NN::RngOrdIdl : filename := "", Alg := "Standard") -> MonStgElt
  {Given a quadratic field and a level, write down equations for the Hilbert modular variety to file (including all components)}

  tt0 := Cputime();
  s := Sprintf("// Computing for quadratic field %o\n", LMFDBLabel(F));
  s := Sprintf("// level has label %o\n", LMFDBLabel(NN));
  prec, gen_bd, rel_bd := SetPrecisionAndBounds(NN);
  s *:= Sprintf("// Computed with precision = %o\n", prec);
  s *:= Sprintf("// generator degree bound = %o\n", gen_bd);
  s *:= Sprintf("// relation degree bound = %o\n", rel_bd);
  s *:= Sprintf("// using %o algorithm\n", Alg);
  NCl, mp := NarrowClassGroup(F);
  mpdet := IdealRepsMapDeterministic(F, mp);
  comps := [mpdet[el] : el in NCl];
  Ss := [];
  // TODO: should loop over Galois orbits of components so that surface is both irreducible and defined over QQ
  for bb in comps do
    t0 := Cputime();
    s *:= Sprintf("// component with label %o\n", LMFDBLabel(bb));
    G := CongruenceSubgroup("GL+", "Gamma0", F, NN, bb);
    //G := CongruenceSubgroup(AmbientType, GammaType, F, NN, bb);
    S := HilbertModularVariety(F, NN, gen_bd, rel_bd : Precision := prec, IdealClassesSupport := [bb], Alg := Alg);
    Append(~Ss, S);
    s *:= WriteCanonicalSurfaceToString(LMFDBLabel(G), S);
    t1 := Cputime();
    s *:= Sprintf("// Computation took %o seconds\n", t1-t0);
  end for;
  M := GradedRingOfHMFs(F,prec);
  sane, H_trace, H_test := HilbertSeriesSanityCheck(M,NN,Ss);
  if sane then
    s *:= "// Sanity check passed: Hilbert series agree!\n";
  else
    s *:= "// Sanity check failed!\n";
    s *:= Sprintf("// series from trace formula = %o\n", H_trace);
    s *:= Sprintf("// computed series = %o\n", H_test);
  end if;

  label := LMFDBLabel(G);
  if filename eq "" then
    filename := Sprintf("../hilbertmodularsurfacesdata/CanonicalRingEquations/%o.m", ConvertLabel(label));
  end if;

  tt1 := Cputime();
  s *:= Sprintf("// Total computation for all components took %o seconds\n", tt1-tt0);
  Write(filename, s);
  return Sprintf("Canonical ring equations written to %o\n", filename);
end intrinsic;

intrinsic WriteCanonicalRingComputationToFile(F_lab::MonStgElt, NN_lab::MonStgElt : filename := "", Alg := "Standard") -> MonStgElt
  {Given labels for a quadratic field and a level, write down equations for the Hilbert modular variety to file (including all components)}

  F := LMFDBField(F_lab);
  NN := LMFDBIdeal(F, NN_lab);
  return WriteCanonicalRingComputationToFile(F, NN: filename := filename, Alg := Alg);
end intrinsic;

intrinsic GenerateFieldsAndLevels(B::RngIntElt) -> MonStElt
  {Given a bound B, return labels of fields F and ideals NN such that disc(F)*Norm(NN) <= B}

  s := "";
  for D := 1 to B do
    if IsFundamentalDiscriminant(D) then
      F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
      for NN in IdealsUpTo(B div D, F) do
        s *:= Sprintf("%o %o\n", LMFDBLabel(F), LMFDBLabel(NN));
      end for;
    end if;
  end for;
  return s;
end intrinsic;

intrinsic CreateInputFile(B) -> MonStgElt
  {}
  Write("input.txt", GenerateFieldsAndLevels(B) : Overwrite := true);
  return "Input file input.txt created";
end intrinsic;
