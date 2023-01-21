AttachSpec("spec");
SetClassGroupBounds("GRH");

if assigned debug then
  SetDebugOnError(true);
end if;

if not assigned D then
  print "Missing argument D";
  exit 1;
end if;
D := StringToInteger(D);
if not IsFundamentalDiscriminant(D) then
  exit 0;
end if;

if not assigned cut then
  cut := 1000;
else
  cut := StringToInteger(cut);
end if;

MaxLevelNorm := Ceiling(cut*D^(-3/2));

if not assigned ambient then
  print "Missing argument ambient";
  exit 1;
end if;
assert ambient in ["GL+", "GL", "SL"];
if ambient eq "GL" then
  ambient := "GL+";
end if;

if not assigned gamma then
  print "Missing argument gamma";
  exit 1;
end if;
assert gamma in ["Gamma", "Gamma0", "Gamma1"];



F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
ZF := Integers(F);
NCl, mp := NarrowClassGroup(F);
narrow_reps := IdealRepsMapDeterministic(F, mp);
ideals := IdealsUpTo(MaxLevelNorm, F);
labels := [[StringToInteger(c) : c in Split(LMFDBLabel(elt), ".")] : elt in ideals];
ParallelSort(~labels, ~ideals);
for NN in ideals do
  chisum := 0;
  //skipping := (GCD(NN, 3*D*ZF) ne 1*ZF) or (gamma eq "Gamma1" and not IsSquarefree(NN));
  skipping := (gamma eq "Gamma1" and not IsSquarefree(NN));
  for bb in narrow_reps do
    G := CongruenceSubgroup(ambient, gamma, F, NN, bb);
    if skipping then
      print StripWhiteSpace(Join([LMFDBLabel(G),"SKIPPED"],":"));
    else
      try
        print WriteGeometricInvariantsToRow(G);
        chisum +:= ArithmeticGenus(G);
      catch e
        print StripWhiteSpace(Join([LMFDBLabel(G),"FAILED"],":"));
        WriteStderr(Sprintf("Failed WriteGeometricInvariantsToRow for %o\n", LMFDBLabel(G)));
        WriteStderr(e);
      end try;
    end if;
  end for;
  if testarithmeticgenus assigned and not skipping and [ambient, gamma] eq ["GL+", "Gamma0"] then
    M := GradedRingOfHMFs(F, 0);
    h := HilbertSeriesCusp(M, NN);
    chi2 := Coefficient(PowerSeriesRing(Rationals())!h,2) + #NCl;
    if not chisum eq chi2 then
        WriteStderr(Sprintf("Failed TestArithmeticGenus for %o %o != %o\n", LMFDBLabel(G), chisum, chi2));
    end if;
  end if;
end for;
exit;

