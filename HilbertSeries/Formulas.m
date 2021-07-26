// formulas for Hilbert series of Hilbert modular surfaces
// Taken from Reid's paper Orbifold Riemann-Roch and Plurigenera

function InitialTerm(n, kX, plurigenera)
  // n is the dimension, kX is the canonical weight
  // Reid's Recipe 16
  // TODO: deal with case when c is negative
  c := kX + n + 1; // coindex
  c_floor := Floor(c/2);
  assert #plurigenera eq c_floor+1; // +1 for the 0th term; or maybe ge if we're less precise with input
  ZZ := Integers();
  R<t> := PolynomialRing(ZZ);
  A0 := R!0;
  for i := 0 to c_floor do
    A0 +:= plurigenera[i+1]*t^i;
  end for;
  A1 := (1-t)^(n+1)*A0;
  P_primes := [];
  for i := 0 to c_floor do
    Append(~P_primes, Coefficient(A1,i));
  end for;
  A := R!0;
  for i := 0 to c_floor do
     A +:= P_primes[i+1]*t^i;
  end for;
  for i := 0 to (Ceiling(c/2)-1) do
     A +:= P_primes[i+1]*t^(c-i);
  end for;
  return A;
end function;

function Porb(n,k,r,as)
// r is the 1/r in the orbifold singularity
// k is the canonical weight kX
// as is the list of a_i in the orbifold singularity

  ZZ := Integers();
  R<t> := PolynomialRing(ZZ);
  A := (1-t^r) div (1-t);
  C := 1;
  for i := 1 to #as do
    C*:= (1-t^(as[i]));
  end for;
  C div (1-t^n);
  return A,C;
end function;
