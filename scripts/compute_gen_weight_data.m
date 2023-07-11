// run in the hilbertmodularforms directory by loading config.m and then 
// load "ModFrmHilD/CanonicalRing/compute_gen_weight_data.m";
path_to_data := "../hilbertmodularsurfacesdata/CanonicalRingEquations";
files := Split(Pipe(Sprintf("ls %o", path_to_data), ""), "\n");
print files;
quads := [];
for f in files do
  F_lab, NN_lab, _, _ := Explode(Split(f, "-"));
  F := LMFDBField(F_lab);
  NN := LMFDBIdeal(F, NN_lab);
  s := Read(Sprintf("%o/%o", path_to_data, f))*"return R, A, eqns, S;";
  R, A, eqns, S := eval s;
  quad := [Discriminant(F), Norm(NN), Max(VariableWeights(R)), Max([Degree(el) : el in eqns])];
  print quad;
  Append(~quads, quad);
  Sort(~quads);
end for;

for quad in quads do
  Write("ModFrmHilD/CanonicalRing/gen_weight_data.txt", Sprintf("%o", quad));
end for;
