// These higher levels need the final generator supplied by the Jacobian.
// The stored presentations check its normalization independently.
procedure check_higher_level_jacobian(d, bound, prec, weights, dim, stored, offset)
  F := QuadraticField(d);
  N := Factorization(2*Integers(F))[1][1];
  data, schemes, certified := HilbertModularVariety(F, N
      : GeneratorWeight := bound, RelationWeight := 2*bound,
        Precision := prec, JacobianGenerator := true);
  assert not certified;
  assert #Keys(data) eq 1 and #schemes eq 1;
  assert Dimension(schemes[1]) eq 2;
  gens := data[Representative(Keys(data))][1];
  R := ConstructWeightedPolynomialRing(gens);
  assert [WeightedDegree(R.i) : i in [1..Rank(R)]] eq weights;
  assert &and[&and[Level(f) eq N and Precision(f) eq prec : f in gens[k]] : k in Keys(gens)];
  lower := AssociativeArray();
  for k in Keys(gens) do
    if k lt bound then lower[k] := gens[k]; end if;
  end for;
  P := ConstructWeightedPolynomialRing(lower);
  products := EvaluateMonomials(lower, [m : m in MonomialsOfWeightedDegree(P, bound)]);
  assert Rank(CoefficientsMatrix(products)) eq dim - 1;
  assert Rank(CoefficientsMatrix(products cat gens[bound])) eq dim;
  assert Dimension(Parent(gens[bound][1])) eq dim;

  I := Ideal(schemes[1]);
  R := Generic(I);
  S := Generic(stored);
  assert VerifyGradedIsomorphism(I, stored,
      [S.1, S.2, S.3, S.4 + offset(S)], [R.1, R.2, R.3, R.4 - offset(R)]);
end procedure;

procedure test_jacobian_qsqrt2_prime_above_2()
  stored := LoadStoredCanonicalRing("2.2.8.1-2.1");
  check_higher_level_jacobian(2, 10, 490, [2, 2, 4, 10], 13, stored, func<A | A!0>);
end procedure;

procedure test_jacobian_qsqrt5_prime_above_2()
  // The stored weight-12 coordinate differs by this lower-weight polynomial.
  offset := func<A | 73/165888000000*(A.1 - A.2)^6
      + (-97*A.1^3 + 111*A.1^2*A.2 + 69*A.1*A.2^2 - 83*A.2^3)*A.3/864000
      + 6*A.3^2>;
  stored := LoadStoredCanonicalRing("2.2.5.1-4.1");
  check_higher_level_jacobian(5, 12, 480, [2, 2, 6, 12], 13, stored, offset);
end procedure;

// The Jacobian option declines over Q(sqrt(10)), whose ordinary class number is two,
// and returns the default presentation. These bounds stop below weight 8, the first
// weight with a Jacobian of three weight-2 generators, whose basis takes about a minute.
procedure test_jacobian_declined_over_class_number_two()
  F := QuadraticField(10);
  assert ClassNumber(F) eq 2;
  N := 1*Integers(F);
  M := GradedRingOfHMFs(F, 20);
  on := ConstructGeneratorsAndRelations(M, N, 2, 4 : JacobianGenerator := true);
  off := ConstructGeneratorsAndRelations(M, N, 2, 4);
  assert Keys(on[1]) eq {2} and Keys(off[1]) eq {2};
  assert Keys(on[2]) eq {4} and Keys(off[2]) eq {4};
  assert on[1][2] eq off[1][2] and on[2][4] eq off[2][4];
end procedure;

test_jacobian_qsqrt2_prime_above_2();
test_jacobian_qsqrt5_prime_above_2();
test_jacobian_declined_over_class_number_two();
