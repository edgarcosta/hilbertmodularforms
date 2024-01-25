MAX_N_NORM := 1000;
MAX_D := 100;
NUM_TRIALS := 10;

function RandomIntegralIdl(F)
    ZF := Integers(F);
    all_ideals := IdealsUpTo(MAX_N_NORM, ZF);
    n := Random(all_ideals);
    return n;
end function;

function test_chi(chi)
  N_f, N_inf := Modulus(chi);
  full_chi_label := HeckeCharLabel(chi);
  _, _, chi_label := Explode(Split(full_chi_label, "_"));
  chi_2 := ChiLabelToHeckeChar(chi_label, N_f);
  chi_3 := FullChiLabelToHeckeChar(full_chi_label);
  // check that the two characters are the same
  assert chi eq chi_2;
  assert chi_2 eq chi_3;
  return chi_label;
end function;

d := Random(1, MAX_D);
K := CyclotomicField(d);
exps := [DiscreteLogDict(K)[K.1^j] : j in [1 .. d]];

// check that the discrete log dict is computed correctly
assert exps eq [1 .. d-1] cat [0];

F := QuadraticField(5);
N := RandomIntegralIdl(F);
rcg_gens := CanonicalRayClassGenerators(N, [1 .. Degree(F)]);
rcg_gens_2 := CanonicalRayClassGenerators(N, [1 .. Degree(F)]);

// check that the algorithm is deterministic
assert rcg_gens eq rcg_gens_2;

G, mp := RayClassGroup(N, [1 .. Degree(F)]);
// the rcg gens need to generate the whole group
assert #sub<G | [gen @@ mp : gen in rcg_gens]> eq #G;

// this is some choice of N where the chi
// can change a lot in different runs
ZF := Integers(F);
N := ideal<ZF | -88*ZF.2 - 48>;
H := HeckeCharacterGroup(N, [1,2]);
chi := ChiLabelToHeckeChar("6u2.4.1.2u1.2u", N);
correct_cond := ideal<ZF | 152, 16*$.2 + 64>;
// fixed "external consistency" check 
assert Conductor(chi) eq correct_cond;

// test trivial character on nontrivial ray class group
assert test_chi(H.0) eq "1u0.0.0.0u1.2u";

// test trivial ray class group
N := 1*ZF;
H := HeckeCharacterGroup(N, []);
assert test_chi(H.0) eq "1uuu";


// random internal consistency check
for _ in [1 .. NUM_TRIALS] do
  N := RandomIntegralIdl(F);
  H := HeckeCharacterGroup(N, [1,2]);
  chi := Random(Elements(H));
  _ := test_chi(chi);
end for;
