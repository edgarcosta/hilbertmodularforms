function hecke_eigs(F, N, k, MD)
  /***
   * F::FldNum - Base field of HMFs
   * N::RngOrdideal - Level 
   * k::SeqEnum[RngIntElt] - Weight
   * MD::ModFrmHilDGRng - A graded ring of HMFs (our version)
   ***/
  M := HilbertCuspForms(F, N, k);
  H := HeckeCharacterGroup(N, [1,2]);
  triv := H!1;
  New := NewSubspace(M);
  ND := NewformDecomposition(New);
  // this function should be called on
  // (F, N, k) tuples which have a unique
  // eigenform for consistency
  assert #ND eq 1;
  eig := Eigenform(ND[1]);

  ideals := Ideals(MD);
  primes := PrimeIdeals(MD);
  
  hecke_eig_dict := AssociativeArray();
  for pp in primes do
    hecke_eig_dict[pp] := HeckeEigenvalue(eig, pp);
  end for;

  ZF := Integers(MD);
  hecke_eig_dict[0*ZF] := 0;
  hecke_eig_dict[1*ZF] := 1;

  ExtendMultiplicatively(~hecke_eig_dict, N, k, triv, primes, ideals : factorization:=func<n|Factorization(MD, n)>);
  return hecke_eig_dict;
end function;

F := QuadraticField(5);
ZF := Integers(F);
prec := 200;
M := GradedRingOfHMFs(F, prec);
nns := Ideals(M);

N := 7*ZF;
k := [2, 4];

hecke_eigs_dict := hecke_eigs(F, N, k, M);
K := Parent(hecke_eigs_dict[2*ZF]);

f1_elt_coeffs := AssociativeArray();
f2_elt_coeffs := AssociativeArray();

bb := 1*ZF;
f1_elt_coeffs[bb] := AssociativeArray();
f2_elt_coeffs[bb] := AssociativeArray();

reps := FunDomainRepsUpToNorm(M, bb, prec);

for nn in Ideals(M) do
  nu := IdealToRep(M)[bb][nn];
  f1_idl_coeff := Trace(K!hecke_eigs_dict[nn]);
  f2_idl_coeff := Trace(K.1 * hecke_eigs_dict[nn]);
  if nu eq 0 then
    f1_elt_coeffs[bb][nu] := F!0;
    f2_elt_coeffs[bb][nu] := F!0;
  else
    f1_elt_coeffs[bb][nu] := F!f1_idl_coeff * (nu)^(-1);
    f2_elt_coeffs[bb][nu] := F!f2_idl_coeff * (nu)^(-1);
  end if;
end for;

M24 := HMFSpace(M, N, k);
B24 := CuspFormBasis(M24); // two conjugate (over F) eigenforms
B24_true := [HMF(M24, f1_elt_coeffs), HMF(M24, f2_elt_coeffs)];

// Bases should be linearly independent 
assert #LinearDependence(B24) eq 0;
assert #LinearDependence(B24_true) eq 0;

// Computed basis should agree with the true basis
assert #LinearDependence(B24 cat B24_true) eq 2;

M22 := HMFSpace(M, N, [2, 2]);
M46 := HMFSpace(M, N, [4, 6]);
M48 := HMFSpace(M, N, [4, 8]);

// there is exactly one [2,2] form of this level
h := CuspFormBasis(M22)[1];
B46 := CuspFormBasis(M46);
B48 := CuspFormBasis(M48);

// Bases should be linearly independent 
assert #LinearDependence(B46) eq 0;
assert #LinearDependence(B48) eq 0;

// if h is a [2,2] form, S24*h should be contained in S48
h_times_B24 := [h*f : f in B24];
assert #LinearDependence(B46 cat h_times_B24) eq #B24;

// the square of S24 should be contained in S48
B24_squared := [f^2 : f in B24];
assert #LinearDependence(B48 cat B24_squared) eq #B24;
