CC_THRESHOLD := 10^-10;

procedure test(a, K1, K2)
  // a::FldElt - Element of K1
  // K1::Fld  
  // K2::Fld 
  assert a in K1;
  b := StrongCoerce(K2, a); 

  a_eval := (K1 ne Rationals()) select Evaluate(a, MarkedEmbedding(K1)) else a;
  b_eval := (K2 ne Rationals()) select Evaluate(b, MarkedEmbedding(K2)) else b;
  assert Abs(a_eval - b_eval) lt CC_THRESHOLD;

  c := StrongCoerce(K1, b);
  assert c eq a;
end procedure;


Q := RationalField();
F := QuadraticField(5);
R<x> := PolynomialRing(Rationals());
K := NumberField(x^3 - x^2 - 2*x + 1);
L := CyclotomicField(5);
H := Compositum(F, L);
M := Compositum(K, L);

// FldRat <-> FldRat
test(163/1729, Q, Q);

// FldRat <-> FldQuad
test(163/1729, Q, F);

// FldRat <-> FldCyc
test(163/1729, Q, L);

// FldQuad <-> FldNum
test(163 + 1729*F.1, F, H);

// FldQuad <-> FldCyc
// TODO abhijitm we omit this test for now because if x is in K
// and L is a cyclotomic field containing K, then
// L!x will succeed but K!(L!x) will fail

// FldCyc <-> FldNum
test(16 + 3*L.1 + 17*L.1^2 + 2*L.1^3 + 9*L.1^4, L, H);

// FldNum <-> FldNum
test(163 + 17*K.1 + 29*K.1^2, K, M);

// StrongMultiply
assert StrongMultiply(M, [* K.1, L.1^3, K.1^-1, L.1^-3, 18/41 *]) eq 18/41;

v_K := MarkedEmbedding(K);
v_L := MarkedEmbedding(L);
w := MarkedEmbedding(M);
a := K.1;
b := L.1;
c := StrongMultiply(M, [* a, b *]);
assert Abs(Evaluate(c, w) - Evaluate(a, v_K) * Evaluate(b, v_L)) lt CC_THRESHOLD;
