AttachSpec("spec");
SetClassGroupBounds("GRH");

if assigned debug then
  SetDebugOnError(true);
end if;

if assigned label then
  G := LMFDBCongruenceSubgroup(label);
  F := Field(G);
  NN := Level(G);
  H := HilbertSeriesCusp(F, NN);
  num := Numerator(H);
  den := Denominator(H);
  _<x> := Parent(num);
  print StripWhiteSpace(Sprintf("%o-%o:%o:%o", Flabel, LMFDBLabel(NN), Numerator(H), Denominator(H)));
  exit 0;
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




F := NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
ideals := IdealsUpTo(MaxLevelNorm, F);
labels := [[StringToInteger(c) : c in Split(LMFDBLabel(elt), ".")] : elt in ideals];
ParallelSort(~labels, ~ideals);
Flabel := LMFDBLabel(F);
for i->NN in ideals do
  H := HilbertSeriesCusp(F, NN);
  num := Numerator(H);
  den := Denominator(H);
  _<x> := Parent(num);
  NNlabel := Join([Sprint(elt) : elt in labels[i]], ".");
  print StripWhiteSpace(Sprintf("%o-%o:%o:%o", Flabel, NNlabel, Numerator(H), Denominator(H)));
end for;

