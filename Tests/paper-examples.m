printf "Verying examples 1-4 in A database of basic numerical invariants of Hilbert modular surfaces...";
// Examples 1, 2, 3
examples := [*
  // Example 1
  <"2.2.85.1-1.1-1.1-gl-0", <ArithmeticGenus, K2, getHZExceptionalNum>,  <4,-8,8>>,
  <"2.2.85.1-1.1-3.1-gl-0", <ArithmeticGenus, K2, getHZExceptionalNum>, <4,0,2>>,
  // Example 2
  <"2.2.44.1-1.1-1.1-sl-0", <ArithmeticGenus, K2, getHZExceptionalNum>, <2, -8, 8>>,
  <"2.2.44.1-1.1-2.1-sl-0", <ArithmeticGenus, K2, getHZExceptionalNum>, <3, -2, 2>>,
  //Example 3
  <"2.2.165.1-1.1-1.1-sl-0",<ArithmeticGenus, K2, getHZExceptionalNum>, <4, -20, 20>>,
  <"2.2.165.1-1.1-1.1-gl-0",<ArithmeticGenus, K2, getHZExceptionalNum>, <3, -10, 20>>,
  //Example 4
  <"2.2.17.1-1.1-1.1-sl-0", <ArithmeticGenus, RationalityCriterion>, <1, true>>
*];
for ex in examples do
  label, fns, expected := Explode(ex);
  G := LMFDBCongruenceSubgroup(label);
  assert <f(G) : f in fns> eq expected;
end for;
