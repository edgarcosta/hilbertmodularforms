// Global verbose flag
VERBOSE := false;

// Test coefficient-based Eigenbasis functionality
if VERBOSE then printf "Testing coefficient-based Eigenbasis functionality...\n"; end if;

// Test 1: Compare default Eigenbasis with coefficient-based approach for [2,4] forms
if VERBOSE then printf "Test 1: Comparing Eigenbasis methods for weight (2,4)...\n"; end if;

F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 150);

k := [2, 4];
N := Factorization(41*ZF)[1][1];
Mk := HMFSpace(M, N, k);
Sk := CuspFormBasis(Mk);

if #Sk gt 0 then
  if VERBOSE then printf "  Found %o cusp forms of weight (2,4) at level %o\n", #Sk, N; end if;
  
  // Get eigenforms using default method (ideal-based for paritious forms)
  eigs_default := Eigenbasis(Mk, Sk);
  if VERBOSE then printf "  Computed %o eigenforms using default method\n", #eigs_default; end if;
  
  // Get eigenforms using coefficient-based method
  eigs_coeff := Eigenbasis(Mk, Sk : use_coeff:=true);
  if VERBOSE then printf "  Computed %o eigenforms using coefficient method\n", #eigs_coeff; end if;
  
  // The two sets of eigenforms should span the same space after normalization
  assert #eigs_default eq #eigs_coeff;
  
  // Normalize eigenforms using built-in function
  eigs_default_norm := [DivideByFirstNonzeroIdlCoeff(f) : f in eigs_default];
  eigs_coeff_norm := [DivideByFirstNonzeroIdlCoeff(f) : f in eigs_coeff];
  
  // Check that the two normalized eigenbases span the same space
  all_eigs := eigs_default_norm cat eigs_coeff_norm;
  lindep_count := #LinearDependence(all_eigs);
  expected_lindep := #eigs_default; // Should have exactly this many dependencies
  
  assert lindep_count eq expected_lindep;
  
  if VERBOSE then printf "  Normalized eigenbases span the same space!\n"; end if;
  if VERBOSE then printf "  Eigenbasis comparison test passed!\n"; end if;
end if;

// Test 2: Test eigenvalue-coefficient consistency for [2,2,3] forms
if VERBOSE then printf "Test 2: Testing eigenvalue-coefficient consistency for weight (2,2,3)...\n"; end if;

// Use the same setup as nonparitious_cubic.m
R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

N := ideal<ZF | [43, 0, 0], [15, 1, 0]>;
k := [2,2,3];
H := HeckeCharacterGroup(N, [1,2,3]);
chi := H.1;
assert Order(chi) eq 2;
assert HeckeCharLabel(chi) eq "1.-2.-1.1_43.2_2u1u1.2.3u";

M := GradedRingOfHMFs(F, 111);
Mk := HMFSpace(M, N, k, chi);
Sk := CuspFormBasis(Mk);
assert #Sk eq 2;

if #Sk gt 0 then
  if VERBOSE then printf "  Found %o cusp forms of weight (2,2,3)\n", #Sk; end if;
  
  // Get eigenforms
  eigs := Eigenbasis(Mk, Sk);
  if VERBOSE then printf "  Computed %o eigenforms\n", #eigs; end if;
  
  // Test eigenvalue-coefficient consistency for each eigenform
  for i := 1 to #eigs do
    f := eigs[i];
    if VERBOSE then printf "  Testing eigenform %o...\n", i; end if;
    
    // Test with a few small primes
    for pp in PrimesUpTo(12, F : coprime_to:=N) do
      b, pi := IsNarrowlyPrincipal(pp);
      if b and IsTotallyPositive(pi) then
        if VERBOSE then printf "    Testing prime %o with generator %o\n", pp, pi; end if;
        
        // Apply HeckeOperatorCoeff
        Tp_f := HeckeOperatorCoeff(f, pi);
        
        // Check if it's an eigenform (should be scalar multiple of f)
        lindep := LinearDependence([f, Tp_f]);
        if #lindep eq 1 then
          eigenvalue := -lindep[1][1] / lindep[1][2];
          
          // Get the coefficient a_pi (normalized appropriately)
          dinv_F := IdealToRep(M, 1*ZF);
          a_pi := Coefficient(f, 1*ZF, pi * dinv_F) / Coefficient(f, 1*ZF, dinv_F);
          
          if VERBOSE then printf "      Eigenvalue: %o, Coefficient: %o\n", eigenvalue, a_pi; end if;
          assert eigenvalue eq a_pi;
        end if;
      end if;
    end for;
  end for;
  
  if VERBOSE then printf "  Eigenvalue-coefficient consistency test passed!\n"; end if;
end if;

if VERBOSE then printf "All coefficient-based Eigenbasis tests passed!\n"; end if;
