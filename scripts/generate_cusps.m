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

if not assigned AmbientType then
  print "Missing argument AmbientType";
  exit 1;
end if;
assert AmbientType in ["GL", "SL"];

if not assigned GammaType then
  print "Missing argument GammaType";
  exit 1;
end if;
assert GammaType in ["Gamma", "Gamma0", "Gamma1"];



F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
_, mp := NarrowClassGroup(F);
narrow_reps := IdealRepsMapDeterministic(F, mp);
ideals := IdealsUpTo(MaxLevelNorm, F);
labels := [[StringToInteger(c) : c in Split(LMFDBLabel(elt), ".")] : elt in ideals];
ParallelSort(~labels, ~ideals);
for NN in ideals do
  for bb in narrow_reps do
    try
      G := CongruenceSubgroup(AmbientType, GammaType, F, NN, bb);
      for c in CuspsWithResolution(G) do
        print WriteCuspDataToRow(G, c);
      end for;
    catch e
      WriteStderr(Sprintf("Failed for D = %o, NN =%o , bb=%o", D, LMFDBLabel(NN), LMFDBLabel(bb)));
      WriteStderr(e);
      exit 1;
    end try;
  end for;
end for;
