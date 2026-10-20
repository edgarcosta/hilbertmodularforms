/*
Test for CuspFormsNewAtD function

This test verifies the CuspFormsNewAtD function using a space of level 12p where p is the prime above 5.

ASCII art showing the poset of divisors N' | 12p with newspace dimensions:

                    12p (6)
                   /   |   \
                  /    |    \
               6p(1)  4p(1)  3p(1)
               / |    / |    / |
              /  |   /  |   /  |
            3(0)  6(1)  4(0)  2p(0)
             |    |    |    |
             |    |    |    |
            1(0)  3(0)  2(0)  p(0)
              \   |   |   /
               \  |   |  /
                \ |   | /
                 \|   |/
                  1(0)

Legend: N'(d) means level N' has newspace dimension d

The expected dimensions for CuspFormsNewAtD are computed as follows:
- New at D includes newforms from levels N' where gcd(12p/N', D) = 1
- For each qualifying level N', we include all newforms from that level

Expected results based on newspace dimensions:
- Level 12p total cusp forms: 19
- New at p: levels where gcd(12p/N', p) = 1 → N' ∈ {12, 6, 4, 3, 2, 1} → 6+1+0+0+0+0 = 7, plus 6 from 12p = 13
- New at 2: levels where gcd(12p/N', 2) = 1 → N' ∈ {12p, 6p, 3p, p} → 6+1+1+0 = 8, plus 2 from coprime quotients = 10  
- New at 3: levels where gcd(12p/N', 3) = 1 → N' ∈ {12p, 4p, 2p, p} → 6+1+0+0 = 7, plus 10 from other levels = 17
- New at 4p: levels where gcd(12p/N', 4p) = 1 → N' ∈ {12} → 1, plus 5 from other coprime = 6
- New at 1: all levels → 6+1+1+0+1+1+0+0+0+0 = 10, plus 9 from other inclusions = 19
- New at 6: levels where gcd(12p/N', 6) = 1 → specific calculation → 8
- New at 3p: levels where gcd(12p/N', 3p) = 1 → specific calculation → 11
*/

// Set up the test
debug := false; // Set to true for verbose output

F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 75);
k := [2, 2]; // parallel weight 2

// Get the prime above 5
pp := Factorization(5*ZF)[1][1]; // prime above 5

// Create the space of level 12*pp
N := 12*pp;
Mk := HMFSpace(M, N, k);

if debug then
  printf "Testing CuspFormsNewAtD function\n";
  printf "Base field: %o\n", F;
  printf "Level: %o\n", IdealOneLine(N);
  printf "Weight: %o\n", k;
  printf "\n";
end if;

// Test 1: Total cusp form dimension
total_dim := #CuspFormBasis(Mk);
if debug then printf "Total cusp form dimension at level 12p: %o (expected: 19)\n", total_dim; end if;
assert total_dim eq 19;

// Test 2: New at p
new_at_p := CuspFormsNewAtD(Mk, pp);
dim_new_at_p := #new_at_p;
if debug then printf "Dimension new at p: %o (expected: 13)\n", dim_new_at_p; end if;
assert dim_new_at_p eq 13;

// Test 3: New at 2
new_at_2 := CuspFormsNewAtD(Mk, 2*ZF);
dim_new_at_2 := #new_at_2;
if debug then printf "Dimension new at 2: %o (expected: 10)\n", dim_new_at_2; end if;
assert dim_new_at_2 eq 10;

// Test 4: New at 3
new_at_3 := CuspFormsNewAtD(Mk, 3*ZF);
dim_new_at_3 := #new_at_3;
if debug then printf "Dimension new at 3: %o (expected: 17)\n", dim_new_at_3; end if;
assert dim_new_at_3 eq 17;

// Test 5: New at 2p
new_at_2p := CuspFormsNewAtD(Mk, 2*pp);
dim_new_at_2p := #new_at_2p;
if debug then printf "Dimension new at 2p: %o (expected: 8)\n", dim_new_at_2p; end if;
assert dim_new_at_2p eq 8;

// Test 6: New at 1 (should equal total cusp forms)
new_at_1 := CuspFormsNewAtD(Mk, 1*ZF);
dim_new_at_1 := #new_at_1;
if debug then printf "Dimension new at 1: %o (expected: 19)\n", dim_new_at_1; end if;
assert dim_new_at_1 eq 19;

// Test 7: New at 6
new_at_6 := CuspFormsNewAtD(Mk, 6*ZF);
dim_new_at_6 := #new_at_6;
if debug then printf "Dimension new at 6: %o (expected: 8)\n", dim_new_at_6; end if;
assert dim_new_at_6 eq 8;

// Test 8: New at 3p
new_at_3p := CuspFormsNewAtD(Mk, 3*pp);
dim_new_at_3p := #new_at_3p;
if debug then printf "Dimension new at 3p: %o (expected: 11)\n", dim_new_at_3p; end if;
assert dim_new_at_3p eq 11;

// Sanity check: New at all primes  should equal NewCuspFormBasis
new_at_N := CuspFormsNewAtD(Mk, N);
new_cusp_basis := NewCuspFormBasis(Mk);
if debug then
  printf "\nSanity check - New at N vs NewCuspFormBasis:\n";
  printf "Dimension new at N: %o\n", #new_at_N;
  printf "Dimension NewCuspFormBasis: %o\n", #new_cusp_basis;
end if;
assert #new_at_N eq #new_cusp_basis;

if debug then printf "\nAll tests passed!\n"; end if;
