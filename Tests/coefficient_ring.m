procedure TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name : default_fields := true)
  // M::ModFrmHilDGRng - Graded ring of HMFs
  // N::RngOrdIdl - Level 
  // k::SeqEnum[RngIntElt] - Weight
  // prec::RngIntElt - Precision
  // coeff_fields::Assoc - Maps bb to the coefficient field of the bb component
  // ground_truth::Assoc - Associative array of "correct answers"
  // test_name::String - Name of test
  // default_field::bool - If false, pass coeff_fields to the HMF constructor. 
  //                       If true, don't pass anything and let it use the default
  Mk := HMFSpace(M, N, k, chi);
  F := BaseField(M);
  MAX_DENOM := 71;

  bbs := NarrowClassGroupReps(M);

  coeffs := AssociativeArray();

  coeffs_gen := function(bb);
    return Random(coeff_fields[bb], MAX_DENOM);
  end function;

  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    reps := FunDomainRepsUpToNorm(M, bb, prec);
    for rep in reps do
      coeffs[bb][rep] := coeffs_gen(bb);
    end for;
  end for;

  if default_fields then
    f := HMF(Mk, coeffs);
  else
    f := HMF(Mk, coeffs : coeff_rings := coeff_fields);
  end if;

  for bb in bbs do
    if not IsIsomorphic(CoefficientRing(Components(f)[bb]), ground_truth[bb]) then
      printf "Failure at component %o\n", IdealOneLine(bb);
      printf "The level is %o, and the nebentypus was %o\n", IdealOneLine(N), chi;
      printf "The computed coefficient ring is %o\n", CoefficientRing(Components(f)[bb]);
      printf "The expected coefficient ring is %o\n", ground_truth[bb];
    end if;

    assert IsIsomorphic(CoefficientRing(Components(f)[bb]), ground_truth[bb]);
  end for;
  printf "coefficient_ring: Passed %o\n", test_name;
  // because functions need a return value apparently
  //return ""; 
end procedure;

///////////////////////  "UNIT" TESTS  /////////////////////// 

F<a> := QuadraticField(5);
R<x> := PolynomialRing(F);
ZF := Integers(F);
prec := 80;
M := GradedRingOfHMFs(F, prec);
coeff_fields := AssociativeArray();
ground_truth := AssociativeArray();

// UNIT 1
// class number 1
// rational coefficients
// trivial character
// parallel (even) weight

N := 1*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.0; // trivial character
k := [2,2];
coeff_fields[1*ZF] := Rationals();
ground_truth[1*ZF] := Rationals();
test_name := "'Unit' Test 1";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name);

// UNIT 2
// class number 1
// quadratic field (nondefault) coefficients 
// trivial character
// parallel (even) weight

N := 1*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.0; // trivial character
k := [2,2];
coeff_fields[1*ZF] := F;
ground_truth[1*ZF] := F;
test_name := "'Unit' Test 2";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name : default_fields := false);

// UNIT 3
// class number 1
// rational coefficients
// nontrivial character
// parallel (odd) weight

N := 23 * ZF;
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1; // character of order 22
k := [3,3];
coeff_fields[1*ZF] := Rationals();
ground_truth[1*ZF] := CyclotomicField(11);
test_name := "'Unit' Test 3";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name);

// UNIT 4
// class number 1
// quadratic field coefficients
// trivial character
// nonparallel paritious weight 

N := 1*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.0; // trivial character
k := [2,4];
coeff_fields[1*ZF] := F;
ground_truth[1*ZF] := F;
test_name := "'Unit' Test 4";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name);

// UNIT 5
// class number 1
// quadratic field coefficients
// nontrivial character
// nonparallel (nonparitious) weight 

N := 11*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1; // nontrivial order 10 character
k := [3,2];
coeff_fields[1*ZF] := F;
eps := TotallyPositiveUnitsGenerators(F)[1];
ground_truth[1*ZF] := CyclotomicField(10); // eps is a square
test_name := "'Unit' Test 5";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name);

////


F<a> := QuadraticField(3);
R<x> := PolynomialRing(F);
ZF := Integers(F);
prec := 80;
U, mU := UnitGroup(F);
M := GradedRingOfHMFs(F, prec);
bbs := NarrowClassGroupReps(M);
coeff_fields := AssociativeArray();
ground_truth := AssociativeArray();

// UNIT 6
// class number 2
// different coefficient fields
// nontrivial character
// parallel weight

N := 1*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.0; // trivial character
k := [2,2];
coeff_fields[bbs[1]] := Rationals();
coeff_fields[bbs[2]] := F;
ground_truth[bbs[1]] := Rationals();
ground_truth[bbs[2]] := F;
test_name := "'Unit' Test 6";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name : default_fields := false);

// "INTEGRATION" TEST

// TODO abhijitm I made this weaker, update
// and fix when you come back to it.
N := 23*ZF;  
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1*H.2; // character of order 11
k := [2,3];
eps := TotallyPositiveUnitsGenerators(F)[1];
coeff_fields[bbs[1]] := CyclotomicField(11);
coeff_fields[bbs[2]] := F;
ground_truth[bbs[1]] := Compositum(CyclotomicField(11), SplittingField(AbsoluteField(ext<F | x^2 - eps>)));
ground_truth[bbs[2]] := Compositum(CyclotomicField(11), SplittingField(AbsoluteField(ext<F | x^2 - eps>)));
test_name := "'Integration' Test 1";

TestCoefficientRing(M, N, chi, k, prec, coeff_fields, ground_truth, test_name);
