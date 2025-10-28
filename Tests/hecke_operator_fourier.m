// Global verbose flag
VERBOSE := false;

// Helper function to test HeckeOperatorCoeff consistency
procedure TestHeckeOperatorCoeffConsistency(f, N, M, k : MAX_PRIME:=20)
  if VERBOSE then 
    weight_str := "(" cat Join([IntegerToString(w) : w in k], ",") cat ")";
    printf "Testing weight %o level %o eigenforms...\n", weight_str, N; 
  end if;
  
  F := BaseField(Parent(Parent(f)));
  ZF := Integers(F);
  
  // Test with a few small primes
  for pp in PrimesUpTo(MAX_PRIME, F : coprime_to:=N) do
    // Get totally positive generator for HeckeOperatorCoeff
    b, pi := IsNarrowlyPrincipal(pp);
    if b and IsTotallyPositive(pi) then
      if VERBOSE then printf "  Testing prime %o with generator %o\n", pp, pi; end if;
      
      // Apply both operators
      Tpf_ideal := HeckeOperator(f, pp);
      Tpf_coeff := HeckeOperatorCoeff(f, pi);
      
      // They should be equal for paritious forms
      if IsZero(Tpf_ideal) then
        assert IsZero(Tpf_coeff);
      else
        lindep := LinearDependence([Tpf_ideal, Tpf_coeff]);
        assert #lindep eq 1;
        
        // inverse codifferent
        dinv_F := IdealToRep(M, 1*ZF);
        // For eigenforms, Tp(f) should be a scalar multiple of f
        lindep_eigen := LinearDependence([f, Tpf_coeff]);
        assert #lindep_eigen eq 1;
        eigenvalue := -lindep_eigen[1][1] / lindep_eigen[1][2];
        
        // The eigenvalue should be the coefficient associated to pi,
        // but normalized by the coefficient at d_F^-1. 
        a_pi := Coefficient(f, 1*ZF, pi * dinv_F) / Coefficient(f, 1*ZF, dinv_F);
        
        assert eigenvalue eq a_pi;
      end if;
    end if;
  end for;
end procedure;

// Test HeckeOperatorCoeff consistency with HeckeOperator on paritious forms
if VERBOSE then printf "Testing HeckeOperatorCoeff consistency on paritious weight forms...\n"; end if;

// Test for weight (2,2) forms
F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 200);

// Create eigenforms of weight (2,2) at level 7
N := Factorization(7*ZF)[1][1];
k := [2, 2];
Mk := HMFSpace(M, N, k);
Sk := CuspFormBasis(Mk);

assert #Sk eq 1;
f := Sk[1];
TestHeckeOperatorCoeffConsistency(f, N, M, k);

// Test for weight (2,4) forms  
k := [2, 4];
N := Factorization(11*ZF)[1][1];
Mk := HMFSpace(M, N, k);
Sk := CuspFormBasis(Mk);
assert #Sk eq 1;
f := Sk[1];
TestHeckeOperatorCoeffConsistency(f, N, M, k);

if VERBOSE then printf "HeckeOperatorCoeff consistency tests passed!\n"; end if;

if VERBOSE then printf "Testing HeckeOperatorCoeff on a nonparitious weight space...\n"; end if;

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

// we want the space to be stable under Hecke operators
for pp in PrimesUpTo(10, F) do
  TpSk := [HeckeOperator(f, pp) : f in Sk];
  // in principle TpSk can be lower dimensional but I don't think it is
  // for these primes at least
  assert #Intersection(Sk, TpSk) eq #Sk;
end for;
