import "ModFrmHilD/HMFGrossenchar.m" : eval_inf_type_at_rou_or_tot_real;

procedure test(K, b_actual, k_hmfs)
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
      // test that we return units of a CM field as the root of unity 
      // followed by generators for the units of the totally real subfield
      U, mU := UnitGroup(K);
      units_K := UnitsGenerators(K : exclude_torsion:=false);
      assert IsRootOfUnity(units_K[1]);
      if #units_K gt 1 then
        assert &and[u in F : u in units_K[2 .. #units_K]];
      end if;
      assert U eq sub<U | [u @@ mU : u in units_K]>;

      // test the custom infinity type evaluation for CM fields
      ZK := Integers(K);
      for k_hmf in k_hmfs do
        k := HeckeCharWeightFromWeight(K, F, k_hmf);
        X := cHMFGrossencharsTorsor(K, k, 1*ZK);
        epses := UnitsGenerators(K : exclude_torsion:=false);
        assert &and[eval_inf_type_at_rou_or_tot_real(X, eps) eq EvaluateNoncompactInfinityType(X, eps) :
          eps in epses];
      end for;
    end if;
  end if;
end procedure;

R<x> := PolynomialRing(Rationals());

test(QuadraticField(5), false, []);
test(QuadraticField(-1), true, []);
test(NumberField(x^3-2), false, []);
test(CyclotomicField(8), true, [[1, 1], [1, 3], [2, 4]]);
test(NumberField(x^4 - x^3 + 3*x^2 - 2*x + 4), true, [[1, 1], [1, 3], [2, 4]]);
test(CyclotomicField(7), true, [[1, 1, 1], [1, 1, 3], [2, 4, 4]]);
