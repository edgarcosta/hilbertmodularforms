BOUND := 10;
TRIALS := 25;
PREC := 1;

function random_totally_positive(F, bound)
  // F: FldNum  
  // bound: RngIntElt -- a bound on how large a norm we allow
  
  // This is incredibly sketchy, but 
  // it's probably good enough??
  //
  // Takes a random element of F of norm at most
  // Sqrt(bound), squares it to get a totally positive 
  // element, and then subtracts a rational y that 
  // leaves x^2 - y totally positive. 

  DUMB := 7;
  x := 0;
  while x eq 0 do
    x := Random(F, Floor(Sqrt(bound)));
  end while;

  x2 := x^2;
  places := RealPlaces(F);
  min_coord := Floor(Min([Evaluate(x2, v) : v in places]));
  denom := Random([2 .. DUMB]);
  y := F!(min_coord/denom);
  z := x2 - y;
  assert IsTotallyPositive(z);
  return z;
end function;

// The usual Magma assert statement doesn't tell you
// what the two values were when an assertion fails. 
// This is an attempt to remedy that.
procedure assert_eq(x, y)
  // x: Any
  // y: Any
  if x cmpne y then
    print "Failure! %o is not equal to %o \n", x, y;
    assert x eq y;
  end if;
end procedure;

procedure test(F, K, k, bbps, idl_to_elt, elt_to_idl : bound := BOUND)
  // F: FldNum - number field
  // k: SeqEnum[RngIntElt] - weight (sequence of nonnegative integers)
  // idl_to_elt: UserProgram - a function taking a_nn and nu and computing a_nu
  // elt_to_idl: UserProgram - a function taking a_nu and nu and computing a_nn
  
  // TODO abhijitm is this the right field in general
  for _ in [1 .. BOUND] do
    a :=  Random(K, 100);
    nu := random_totally_positive(F, 100);
    bbp := Random(bbps);
    if not (a eq 0 or nu eq 0) then
      // TODO abhijitm decide whether or not there's a bbp dependence,
      // if not remove the bbp's everywhere in this test.
      x := IdlCoeffToEltCoeff(a, nu, k, K);
      y := EltCoeffToIdlCoeff(a, nu, k, K);
      assert_eq(x, idl_to_elt(a, nu, bbp));
      assert_eq(y, elt_to_idl(a, nu, bbp));
      assert_eq(EltCoeffToIdlCoeff(x, nu, k, K), a);
      assert_eq(IdlCoeffToEltCoeff(y, nu, k, K), a);
    end if;
  end for;
//  print "Passed test!";
//  return "";
end procedure;

/////// NARROW CLASS NUMBER 1

F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, PREC);
N := 1*ZF;
dd := Different(ZF);
bbps := M`NarrowClassGroupRepsToIdealDual;

// PARALLEL WEIGHT

k := [2, 2];
K := UnitCharField(F, k);
// because the weight is parallel
// and h+ = 1, a_nn = a_nu always
idl_to_elt := func<a, nu, bbp | a>;
elt_to_idl := func<a, nu, bbp | a>;
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

// K bigger than UnitCharField
K := Compositum(UnitCharField(F, k), CyclotomicField(7));
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

// EVEN PARITIOUS WEIGHT

k := [2, 4];
K := UnitCharField(F, k);
idl_to_elt := func<a, nu, bbp | a*nu^(-1)>;
elt_to_idl := func<a, nu, bbp | a*nu>;
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

k := [6, 2];
K := UnitCharField(F, k);
auts := AutsReppingEmbeddingsOfF(F, k);
idl_to_elt := func<a, nu, bbp | a*auts[2](nu^(-2))>;
elt_to_idl := func<a, nu, bbp | a*auts[2](nu^2)>;
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

// ODD PARITIOUS WEIGHT
// TODO abhijitm add if necessary

// NONPARITIOUS WEIGHT
// TODO abhijitm 


/////// NARROW CLASS NUMBER 2
F := QuadraticField(3);
ZF := Integers(F);
N := 1*ZF;
M := GradedRingOfHMFs(F, PREC);
dd := Different(ZF);
bbps := M`NarrowClassGroupRepsToIdealDual;

// PARALLEL WEIGHT

k := [2, 2];
K := UnitCharField(F, k);
elt_to_idl := func<a, nu, bbp | a>;
idl_to_elt := func<a, nu, bbp | a>;
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

// EVEN PARITIOUS WEIGHT

k := [2, 4];
K := UnitCharField(F, k);
idl_to_elt := func<a, nu, bbp | a*nu^(-1)>;
elt_to_idl := func<a, nu, bbp | a*nu>;
test(F, K, k, bbps, idl_to_elt, elt_to_idl);

// NONPARITIOUS WEIGHT
// TODO abhijitm
