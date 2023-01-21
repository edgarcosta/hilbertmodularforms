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
assert gamma eq "Gamma0";



F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
ZF := Integers(F);
_, mp := NarrowClassGroup(F);
narrow_reps := IdealRepsMapDeterministic(F, mp);
ideals := IdealsUpTo(MaxLevelNorm, F);
labels := [[StringToInteger(c) : c in Split(LMFDBLabel(elt), ".")] : elt in ideals];
ParallelSort(~labels, ~ideals);
for NN in ideals do
  for bb in narrow_reps do
    G := CongruenceSubgroup(ambient, gamma, F, NN, bb);
    if (GCD(NN, 3*D*ZF) ne 1*ZF) or (gamma eq "Gamma1" and not IsSquarefree(NN)) then
      print StripWhiteSpace(Join([LMFDBLabel(G),"SKIPPED"],":"));
    else
      try
        print StripWhiteSpace(Join([LMFDBLabel(G), Sprint(KodairaDimensionPossibilities(G))],":"));
      catch e
        print StripWhiteSpace(Join([LMFDBLabel(G),"FAILED"],":"));
        WriteStderr(Sprintf("Failed WriteGeometricInvariantsToRow for %o", LMFDBLabel(G)));
        WriteStderr(e);
      end try;
    end if;
  end for;
end for;
exit;


