AttachSpec("spec");
SetClassGroupBounds("GRH");


if assigned D then
  Ds := [StringToInteger(D)];
else
  Ds := [0..3000];
end if;

Ds := [elt : elt in Ds | IsFundamentalDiscriminant(elt) or elt eq 0];

if not assigned cut then
  cut := 5000;
else
  cut := StringToInteger(cut);
end if;

MaxLevelNorm := func<D|Ceiling(cut*D^(-3/2))>;


ambients := [<"GL+", "gl">, <"SL", "sl">];

gammas := [<"Gamma0", "0">];

for D in Ds do
  if D eq 0 then
    print("header");
    continue;
  end if;
  F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
  field_label := LMFDBLabel(F);
  ZF := Integers(F);
  NCl, mp := NarrowClassGroup(F);
  narrow_reps := IdealRepsMapDeterministic(F, mp);
  ideals := IdealsUpTo(MaxLevelNorm(D), F);
  labels := [[StringToInteger(c) : c in Split(LMFDBLabel(elt), ".")] : elt in ideals];
  ParallelSort(~labels, ~ideals);
  for i->NN in ideals do
    level_label := Join([Sprint(x) : x in labels[i]], ".");
    for bb in narrow_reps do
      component_label := LMFDBLabel(bb);
      for elt in CartesianProduct(ambients, gammas) do
        ambient, gamma := Explode(elt);
        label := Join([field_label, level_label, component_label, ambient[2], gamma[2]], "-");
        print(label);
      end for;
    end for;
  end for;
end for;
exit;
