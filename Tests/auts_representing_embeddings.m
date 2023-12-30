THRESHOLD := 10^-10;

procedure test(F, K)
  // F: A number field
  // k: A number field containing the Galois closure of F
  
  ZF := Integers(F);
  n := Degree(F);
  places := InfinitePlaces(F);

  v_0 := MarkedEmbedding(K);
  a := PrimitiveElement(F);

  auts := AutsOfKReppingEmbeddingsOfF(F, K);
  assert #auts eq n;

  r, s := Signature(F);
  for i in [1 .. r] do
    // test that the ith automorphism aut_i in auts satisfies v_1(aut_i(a)) = v_i(a)
    assert Abs(Evaluate(auts[i](a), v_0) - Evaluate(a, places[i])) lt THRESHOLD;
  end for;
  for i in [r+1 .. r+s] do
    assert Abs(Evaluate(auts[i](a), v_0) - Evaluate(a, places[i])) lt THRESHOLD;
    assert Abs(Evaluate(auts[i + s](a), v_0) - Conjugate(Evaluate(a, places[i]))) lt THRESHOLD;
  end for;
end procedure;

R<x> := PolynomialRing(Rationals());

// Galois quadratic Q(sqrt(3))
F := QuadraticField(3);
K := UnitCharField(F, [2,4]);
test(F, K);

k := [3,2];
K := UnitCharField(F, [3,2]);
test(F, K);

// totally imaginary field
F := CyclotomicField(7);
K := F;
test(F, K); 

// Galois cubic 3.3.494209.1
F<a> := NumberField(x^3 - x^2 - 234*x + 729);
K := UnitCharField(F, [1,2,3]);
// non-paritious weight
test(F, K);

// non-Galois cubic 3.3.148.1
F<a> := NumberField(x^3 - x^2 - 3*x + 1);

// paritious weight
K := UnitCharField(F, [100, 1000, 11110]);
test(F, K);
// non-paritious weight
K := UnitCharField(F, [1, 246, 1]);
test(F, K);

