procedure test(K, b_actual)
  b, tau, F := IsCM(K);
  if b ne b_actual then
    assert 0 eq 1; 
  end if;

  if b and (not IsIsomorphic(FixedField(K, [tau]), F)) then
    // something's wrong with the automorphism or 
    // the totally real subfield
    assert 0 eq 1;
  end if;
end procedure;

R<x> := PolynomialRing(Rationals());

test(QuadraticField(5), false);
test(QuadraticField(-1), true);
test(NumberField(x^3-2), false);
test(CyclotomicField(8), true);
test(NumberField(x^4 - x^3 + 3*x^2 - 2*x + 4), true);
test(CyclotomicField(7), true);
