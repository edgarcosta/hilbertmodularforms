procedure test(K, b_actual)
  b, tau, F := IsCM(K);
  if b ne b_actual then
    assert 0 eq 1; 
  end if;

  if b then
    if (not IsIsomorphic(FixedField(K, [tau]), F)) then
      // something's wrong with the automorphism or 
      // the totally real subfield
      assert 0 eq 1;
    else
      // for a CM field we return units as the root of unity followed
      // by generators for the positive 
      U, mU := UnitGroup(K);
      units_K := UnitsGenerators(K : exclude_torsion:=false);
      assert IsRootOfUnity(units_K[1]);
      if #units_K gt 1 then
        assert &and[u in F : u in units_K[2 .. #units_K]];
      end if;
      assert U eq sub<U | [u @@ mU : u in units_K]>;
    end if;
  end if;
end procedure;

R<x> := PolynomialRing(Rationals());

test(QuadraticField(5), false);
test(QuadraticField(-1), true);
test(NumberField(x^3-2), false);
test(CyclotomicField(8), true);
test(NumberField(x^4 - x^3 + 3*x^2 - 2*x + 4), true);
test(CyclotomicField(7), true);
