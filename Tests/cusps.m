
K := QuadraticField(40);
signs := [-1, -1];

// Extract components
cg, mp := NarrowClassGroup(K);
B := mp(cg.1); // The component with nontrivial signs.

// Cusp resolution call.
cusps := Cusps(1*MaximalOrder(K), B);
assert #cusps eq 2;
