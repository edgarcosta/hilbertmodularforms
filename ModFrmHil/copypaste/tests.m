freeze;


///////////////////////////////////////////////////////////////////////
//   Test routines for the Hilbert modular forms package             //
//   Steve Donnelly, started November 2008                           //
///////////////////////////////////////////////////////////////////////

// Several tests of correctness are built into the main Hilbert code.
// HeckeOperator automatically checks commutativity (with stored Heckes);
// NewSubspace checks there's a basis where the Heckes are over the base field;
// NewformDecomposition checks the eigenvalues fields are totally real or CM.

profile := false; // should be false, except for personal use

function random_large_split_prime(K)
  OK := Integers(K);
  while true do
    p := PreviousPrime(Random(Round(2^(B - 1)), Round(2^B))) where B is 23.5;
    if AbsoluteDiscriminant(OK) mod p eq 0 then continue; end if;
    if exists(P){tup[1] : tup in Factorization(p*OK) | AbsoluteNorm(tup[1]) eq p} then
      return P; end if;
  end while;
end function;

function getM(K, N, k)
  OK := Integers(K); _<a> := K; Kxx := PolynomialRing(K); xx := Kxx.1;
  if Type(N) eq RngIntElt then N := N*OK; end if;
  if Type(k) eq RngIntElt then k := [k : i in [1..Degree(K)]]; end if;
  M := HilbertCuspForms(K, N, k); 
  return M, K, OK, N, k, Kxx;
end function;

procedure HMFTestDimension(K, N, k : Bound:=1000)
  M, K, OK, N, k := getM(K, N, k);

  printf "\n\n/////////////////////\n  HMFTestDimension:\n\n%o\n\n", M; 
  print "Seed:", GetSeed(); "";
  
  // Use formula
  weight2 := Seqset(k) eq {2};
  if weight2 then
    // formula is implemented
    printf "Computing the formula ... "; time
    d1 := Dimension(M : UseFormula);
    printf "Dimension = %o\n", d1;
    delete M`Dimension;
    if d1 gt Bound then
      "Dimension is too big ==> do not compute the space";
      return;
    end if;
  end if;
  
  // Compute space
  printf "Computing the space ..... "; time
  d := Dimension(M : UseFormula:=false);
  printf "Dimension = %o\n", d;
  if weight2 then
    assert d eq d1; 
    "Dimensions agree!";
  end if;
end procedure;

// This computes some Hecke operators on the full cuspidal space

procedure HMFTestHecke(K, N, k : Bound:=50, MaxDim:=50, TestCharPoly:=false)

  if profile then ProfileReset(); SetProfile(true); end if;

  M, K, OK, N, k, Kxx := getM(K, N, k);

  printf "\n\n/////////////////////\n  HMFTestHecke:\n\n%o\n\n", M; 
  print "Seed:", GetSeed(); "";
  
  d := Dimension(M); 
  if d eq 0 then "Dimension zero, nothing to do"; 
    if profile then ProfilePrintByTotalTime(:Max:=40); end if;
    return; 
  end if; 
  
  TPs_red := [];

  A := Algebra(QuaternionOrder(M)); 
  "    Quaternion algebra = <", A.1^2, A.2^2, ">";
  print "Seed:", GetSeed(); "";

  for P in PrimesUpTo(Bound, K) do 
    if not IsDefinite(M) and P + Level(M) ne 1*OK then continue; end if;
    "\nP =",P; TP := HeckeOperator(M,P); 

    // Check commutativity modulo a large prime Q
    if IsEmpty(TPs_red) then // choose Q
      F := BaseRing(TP);
      Q := random_large_split_prime(F); 
      k, res := ResidueClassField(Q);
    end if;
    printf "Reducing Hecke matrix modulo prime of norm %o ... ", AbsoluteNorm(Q); time
    try
      TPred := Matrix(k, Nrows(TP), [res(a) : a in Eltseq(TP)]); 
    catch ERR
      TPred := Matrix(k, Nrows(TP), [res(Numerator(a))/res(Denominator(a)) : a in Eltseq(TP)]);
    end try;
    Append(~TPs_red, TPred); 
    printf "Checking commutativity modulo prime of norm %o ... ", AbsoluteNorm(Q); time
    for T in TPs_red do assert T eq TPred or T*TPred eq TPred*T; end for;

    if TestCharPoly or Dimension(M) le 30 then 
      chi := CharacteristicPolynomial(TP); 
      bool,chiK := IsCoercible(Kxx,chi); assert bool; Factorization(chiK); 
    end if;
  end for;

  if profile then ProfilePrintByTotalTime(:Max:=40); end if;
end procedure;

// Runs the main stuff: NewSubspace + NewformDecomposition + Eigenform

procedure HMFTestEigenforms(K, N, k : Bound:=30, MaxDim:=50)

  if profile then ProfileReset(); SetProfile(true); end if;

  OK := Integers(K);
  xx := PolynomialRing(K).1;
  if Type(N) eq RngIntElt then N := N*OK; end if;
  if Type(k) eq RngIntElt then k := [k : i in [1..Degree(K)]]; end if;
  M := HilbertCuspForms(K, N, k); 

  printf "\n\n/////////////////////\n  HMFTestEigenforms:\n\n%o\n\n", M; 
  print "Seed:", GetSeed(); "";
  
  if IsEven(Degree(K)) and Dimension(M) gt 2*MaxDim then 
    "Dimension =", Dimension(M), "is too big!"; return; end if;
  time Mnew := NewSubspace(M);
  time dnew := Dimension(Mnew); Mnew:Minimal;
  A := Algebra(QuaternionOrder(Mnew)); "Quaternion algebra = <", A.1^2, A.2^2, ">";
  if dnew gt MaxDim then "New space is too big!"; return; 
  elif dnew eq 0 then return; end if;
  "SetRationalBasis ... "; time SetRationalBasis(Mnew);
  "NewformDecomposition: "; time nf := NewformDecomposition(Mnew); nf:Minimal;
  Primes := PrimesUpTo(Bound, K); 
  for P in Primes do "\nP =", P;
    chi := CharacteristicPolynomial(HeckeOperator(Mnew, P)); Factorization(chi);
    assert chi eq &* [CharacteristicPolynomial(HeckeOperator(MM,P)) : MM in nf];
  end for;
  "Hecke eigenvalues:"; 
  for f in Eigenforms(Mnew) do 
    L := BaseField(f); if Type(L) ne FldRat then L<w> := L; end if;
    f:Maximal; d := Dimension(Parent(f)); 
    for P in Primes do t := HeckeEigenvalue(f,P); if d le 10 then t; end if; end for; 
  end for;

  if profile then ProfilePrintByTotalTime(:Max:=40); end if;
end procedure;

// Checks that newforms over Q show up over quadratic fields

procedure HMFTestQNewforms(K, level, k : Bound:=50, MaxDim:=100)

  if profile then ProfileReset(); SetProfile(true); end if;

  OK := Integers(K);
  assert Type(level) eq RngIntElt;
  if Type(k) eq RngIntElt then k := [k : i in [1..Degree(K)]]; end if;
  error if &or [k[i] ne k[1] : i in [1..Degree(K)]], "Weight is not parallel!";
  if not &and [tup[2] eq 1 : tup in Factorization(level*OK)] then
    "The level is not squarefree"; return; end if;
  
  ps := []; Ps := [];
  for p in PrimesUpTo(Bound) do 
    fact := Factorization(p*OK);
    if Norm(fact[1][1]) eq p and fact[1][2] eq 1 then
      Append(~ps,p); Append(~Ps,fact[1][1]); end if; end for;

  MQ := CuspForms(level,k[1]); 
  if Dimension(MQ) gt 2*MaxDim then 
    "Dimension of classical space =", Dimension(MQ), "is too big!"; return; end if;
  printf "Computing newforms in %o ... ", MQ; time
  newformsQ := [*f[1] : f in Newforms(MQ) | BaseRing(Parent(f[1])) eq Rationals() *];
  if #newformsQ eq 0 then "No rational newforms over Q"; return; end if;
  eigenvaluesQ := [[K!Coefficient(f,p) : p in ps] : f in newformsQ]; eigenvaluesQ;
  
  M := HilbertCuspForms(K, level*OK, k); 
  if Dimension(M) gt MaxDim then "Dimension =", Dimension(M), "is too big!"; return; end if;
  "Running HMFTestQNewforms to test whether rational newforms over Q of level", level, "show up in"; M;
  print "Seed:", GetSeed(); "";
  nf := [N: N in NewformDecomposition(NewSubspace(M)) | Dimension(N) eq 1]; assert #nf gt 0;

  eigenvalues := [[HeckeEigenvalue(Eigenform(N),P) : P in Ps] : N in nf]; eigenvalues;
  for seq in eigenvaluesQ do assert seq in eigenvalues; end for; "Okay!\n";

  if profile then ProfilePrintByTotalTime(:Max:=40); end if;
end procedure;

// Checks that we get dimension zero, in cases where this holds for trivial reasons

procedure HMFTestDimensionZero( : Bound:=15)

  if profile then ProfileReset(); SetProfile(true); end if;

  squarefrees := [n : n in [2..Bound] | IsSquarefree(n)];

  // Definite over Q, odd weight
  "\nTesting newforms over Q\n";
  QQ := NumberField(Polynomial([-1,1]) : DoLinearExtension);
  ZZ := Integers(QQ);
  for n in squarefrees, k in [3,5] do n, k; 
    M := HilbertCuspForms(QQ, n*ZZ, [k]); M;
    Mnew := NewSubspace(M); assert IsDefinite(Mnew); Mnew;
    time dim := Dimension(Mnew); assert dim eq 0; 
  end for;

  // Over quadratic field with unit of norm -1
  for d in squarefrees do 
    K := QuadraticField(d);
    if Norm(FundamentalUnit(K)) eq 1 then continue; end if; 
    "\nTesting x^2 -", d; "";
    for level in PrimesUpTo(10,K), weight in [[3,3],[3,5]] do
      M := HilbertCuspForms(K, level, weight); M;
      time dim := Dimension(M); assert dim eq 0;
  end for; end for;

  if profile then ProfilePrintByTotalTime(:Max:=40); end if;
end procedure;

// Check both algorithms get the same dimension and Hecke

x := PolynomialRing(Rationals()).1;
totally_real_cubics := 
[
    x^3 - x^2 - 2*x + 1,
    x^3 - 9*x + 9,
    x^3 - 4*x + 2,
    x^3 + 2*x^2 - 3*x - 5,
    x^3 - 4*x - 1,
    x^3 + 2*x^2 - 3*x - 1,
    x^3 + 2*x^2 - 3*x - 2,
    x^3 + 2*x^2 - 3*x - 3,
    x^3 + x^2 - 6*x - 7,
    x^3 + x^2 - 12*x - 4,
    x^3 + x^2 - 6*x + 2,
    x^3 - 9*x + 4,
    x^3 + 3*x^2 - 4*x - 1,
    x^3 + x^2 - 6*x + 1,
    x^3 + x^2 - 6*x - 5,
    x^3 + x^2 - 12*x + 8
];
discs := [ 49, 81, 148, 169, 229, 257, 316, 321, 361, 469, 568, 621, 697, 761, 785, 892 ];

procedure HMFTestCubicsBothAlgorithms( : NUM:=Infinity() )

end procedure;
