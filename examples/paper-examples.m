// paper examples

// Example 1
labels := ["2.2.85.1-1.1-1.1-gl-0", "2.2.85.1-1.1-3.1-gl-0"];
for label in labels do
  G := LMFDBCongruenceSubgroup(label);
  ArithmeticGenus(G);
  // 4 // 4
  K2(G);
  // -8 // 0
  getHZExceptionalNum(G);
  // 8 // 2
end for;

// Example 2
labels := ["2.2.44.1-1.1-1.1-sl-0", "2.2.44.1-1.1-2.1-sl-0"];
for label in labels do
  G := LMFDBCongruenceSubgroup(label);
  ArithmeticGenus(G);
  // 2 // 3
  K2(G);
  // -8 // -2 
  getHZExceptionalNum(G);
  // 8 // 2
end for;


// Example 3
labels := ["2.2.165.1-1.1-1.1-sl-0", "2.2.165.1-1.1-1.1-gl-0"];
for label in labels do
  G := LMFDBCongruenceSubgroup(label);
  ArithmeticGenus(G);
  // 4 // 3
  K2(G);
  // -20 // -10 
  getHZExceptionalNum(G);
  // 20 // 20
end for;
