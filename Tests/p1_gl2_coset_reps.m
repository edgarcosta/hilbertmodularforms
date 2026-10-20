// GL2CosetRepsTest.m
// Comprehensive tests for GL2 coset representatives

import "ModFrmHil/definite.m" : coset_rep_dict;

// Test the bijection between GL2/B and P1 for a given ideal
function TestGL2CosetReps(N)
  ZF := Order(N);
  F := NumberField(ZF);
  
  // Skip rationals (ProjectiveLine has issues there)
  if Degree(F) eq 1 then
    return true;
  end if;
  
  // Get projective line and coset representatives (new API returns dict keyed by P1)
  R, phi := quo<ZF | N>;
  P1, P1rep := ProjectiveLine(R : Type := "Matrix");
  coset_reps := coset_rep_dict(P1, P1rep, N, <R, phi>);
  
  // Handle trivial case
  if Minimum(N) eq 1 then
    return (#P1 eq 1) and (#Keys(coset_reps) eq 1);
  end if;
  
  // Check cardinalities: exactly one representative per P1 element
  if #P1 ne #Keys(coset_reps) then
    return false;
  end if;
  
  // Verify that for each key p = [b; d] in P1, the corresponding matrix g = [a b; c d]
  // indeed maps to the same projective point (up to scaling in R)
  for p in P1 do
    if not IsDefined(coset_reps, p) then
      return false;
    end if;
    g := coset_reps[p];
    b := phi(ZF!g[1,2]);  // upper right entry
    d := phi(ZF!g[2,2]);  // lower right entry
    // p is represented as a 2x1 matrix over R. Check projective equality:
    p_b := R!(p[1,1]);
    p_d := R!(p[2,1]);
    if p_b * d ne p_d * b then
      return false;
    end if;
  end for;
  
  return true;
end function;

// Run comprehensive tests
procedure RunAllTests()
  results := [];
  test_names := [];
  
  // Test 1: Q(√5) with ideal (2)
  K1<a> := QuadraticField(5);
  ZK1 := Integers(K1);
  N1 := ideal<ZK1 | 2>;
  result1 := TestGL2CosetReps(N1);
  Append(~results, result1);
  Append(~test_names, "Q(√5), (2)");
  
  // Test 2: Q(√-1) with ideal (1+i)
  K2<i> := QuadraticField(-1);
  ZK2 := Integers(K2);
  N2 := ideal<ZK2 | 1+i>;
  result2 := TestGL2CosetReps(N2);
  Append(~results, result2);
  Append(~test_names, "Q(√-1), (1+i)");
  
  // Test 3: Q(√2) with ideal (2)
  K3<b> := QuadraticField(2);
  ZK3 := Integers(K3);
  N3 := ideal<ZK3 | 2>;
  result3 := TestGL2CosetReps(N3);
  Append(~results, result3);
  Append(~test_names, "Q(√2), (2)");
  
  // Test 4: Cubic field with ideal (2)
  R<x> := PolynomialRing(Rationals());
  K4<c> := NumberField(x^3 + x + 1);
  ZK4 := Integers(K4);
  N4 := ideal<ZK4 | 2>;
  result4 := TestGL2CosetReps(N4);
  Append(~results, result4);
  Append(~test_names, "Cubic field, (2)");
  
  // Test 5: Q(√3) with ideal (3)
  K5<d> := QuadraticField(3);
  ZK5 := Integers(K5);
  N5 := ideal<ZK5 | 3>;
  result5 := TestGL2CosetReps(N5);
  Append(~results, result5);
  Append(~test_names, "Q(√3), (3)");
  
  passed := #[r : r in results | r];
  total := #results;
  
  if passed ne total then
    // Some tests failed
    assert 0 eq 1;
  end if;
end procedure;

// Run the tests
RunAllTests();
