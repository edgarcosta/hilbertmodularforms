N := 9;
GG := Gamma1(N);
cusps_magma := Cusps(GG);
F<nu> := RationalsAsNumberField();
ZF := Integers(F);
Cl, mp := ClassGroup(F);
bb := mp(Cl.0);
cusps_raw := Cusps(N*ZF, bb : GammaType := "Gamma1");
cusps_test := [];
for c in cusps_raw do
  u,v := Explode(IntegralCoordinates(c));
  Append(~cusps_test, Cusp(u,v));
end for;

pairs := [];
for i := 1 to #cusps_magma do
  for j := 1 to #cusps_test do
    if IsEquivalent(GG,cusps_magma[i],cusps_test[j]) then
      Append(~pairs, <i,j>);
    end if;
  end for;
end for;
