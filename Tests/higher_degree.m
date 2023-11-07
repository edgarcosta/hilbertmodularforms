R<x> := PolynomialRing(RationalField());

F<a> := NumberField(x^2-5);
TotallyPositiveUnits(F);
gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 1;

F<a> := NumberField(x^3-x^2-2*x+1);
TotallyPositiveUnits(F);
gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 2;
