AttachSpec("spec");
SetClassGroupBounds("GRH");

if assigned debug then
  SetDebugOnError(true);
end if;

if assigned label then
  G := LMFDBCongruenceSubgroup(label);
  try
    C := CountEllipticPoints(G);
    for r in Keys(C) do
        print WriteEllipticPointDataToRow(G, r, C[r]);
    end for;        
    exit 0;
  catch e
    print StripWhiteSpace(Join([LMFDBLabel(G),"FAILED"],":"));
    WriteStderr(Sprintf("Failed WriteElllipticPointDataToRow for %o\n", LMFDBLabel(G)));
    WriteStderr(e);
    exit 1;
  end try;
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
          C := CountEllipticPoints(G);
          for r in Keys(C) do
              print WriteEllipticPointDataToRow(G, r, C[r]);
          end for;
      catch e
        print StripWhiteSpace(Join([LMFDBLabel(G),"FAILED"],":"));
        WriteStderr(Sprintf("Failed WriteEllipticPointDataToRow for %o\n", LMFDBLabel(G)));
        WriteStderr(e);
      end try;
    end if;
  end for;
end for;
exit;
