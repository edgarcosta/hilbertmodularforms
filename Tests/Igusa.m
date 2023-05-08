printf "Testing Universal Igusa over Q(sqrt(d)) with h = 1 for... d="; //use printf with no \n

function TestIgusa(D : prec:=5)
  if not IsFundamentalDiscriminant(D) then return true; end if;
  F := QuadraticField(D);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, prec);
  S4plus, S4minus := SiegelEisensteinPullback(M, [4,4]);
  S6plus, S6minus := SiegelEisensteinPullback(M, [6,6]);
  forms := [* S4plus, S6plus, S4plus*S6plus, S4minus*S6minus *];
  tforms := ["S4plus", "S6plus", "S4plus*S6plus", "S4minus*S6minus"];
  for i->f in forms do
    B := Basis(Parent(f));
    LD := LinearDependence(B cat [f]);
    if #LD ne 1 then
      WriteStderr(Sprintf("#LD=%o for D=%o f=%o\n", #LD, D, tforms[i]));
      return false;
    end if;
  end for;
  return true;
end function;


ds := [];
possible_ds := [d : d in [1..100] | IsFundamentalDiscriminant(d) and ClassNumber(d) eq 1];
t := Time();
for counter in [1..20] do
    d := Random(possible_ds);
    while d in ds do
        d := Random(possible_ds);
    end while;
    Append(~ds, d);
    printf "%o ", d;
    assert TestIgusa(d);
end for;
