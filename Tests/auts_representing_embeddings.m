THRESHOLD := 10^-10;

function find_level_and_chi(F, k)
  // F: A number field
  // k: A weight
  //
  // Returns a level N and nebentypus character
  // chi such that HMFSpace(M, N, k, chi)
  // won't throw any errors.
  n := Degree(F);
  for N in IdealsUpTo(100, F) do
    H := HeckeCharacterGroup(N, [1 .. n]);
    for chi in Elements(H) do
      if IsCompatibleWeight(chi, k) then
        return N, chi;
      end if;
    end for;
  end for;
end function;

procedure test(F, k)
  // F: A number field
  // k: A weight
  
  ZF := Integers(F);
  n := Degree(F);
  places := RealPlaces(F);

  K := UnitCharField(F, k);
  v_0 := DistinguishedPlace(K);
  a := PrimitiveElement(F);

  auts := AutsReppingEmbeddingsOfF(F, k);
  assert #auts eq n;

  for i in [1 .. n] do
    // test that the ith automorphism aut_i in auts satisfies v_1(aut_i(a)) = v_i(a)
    assert Abs(Evaluate(auts[i](a), v_0) - Evaluate(a, places[i])) lt THRESHOLD;
  end for;
end procedure;

R<x> := PolynomialRing(Rationals());

// TODO abhijitm there are lots of extra tests
// because at first I thought a more complicated thing
// was necessary in the nonparitious case. 
// I'm leaving these in for now in case it
// later becomes necessary, but once the nonparitious pipeline
// is running these should be deleted if they're not useful.

// Galois quadratic Q(sqrt(3)), h+/h = 2
F := QuadraticField(3);
test(F, [3,2]);

/*
// Galois cubic 3.3.494209.1, h+/h = 4
F<a> := NumberField(x^3 - x^2 - 234*x + 729);
// non-paritious weight
test(F, [1,2,3]);


// non-Galois cubic 3.3.148.1, h+/h = 1
F<a> := NumberField(x^3 - x^2 - 3*x + 1);

// paritious weight
test(F, [100, 1000, 11110]);
// non-paritious weight
test(F, [1, 246, 1]);

 
// Galois cubic 3.3.49.1, h+/h = 1
F<a> := NumberField(x^3 - x^2 - 2*x + 1);
// paritious weight
test(F, [2,2,4]);
// non-paritious weight
// because h+ = h all the positive units
// are squares and unit character field
// is the same as the splitting field of F
test(F, [3,5,4]);
*/

