/***************************************************
* There should be (h_K - h_K[2])/2 Grossencharacters
* coming from K/F if F has narrow class number 1 and 
* we require the conductor of the induced HMFs to be 
* a prime ideal.
***************************************************/

for d in [5, 13] do
  F := QuadraticField(d);  
  if NarrowClassNumber(F) eq 1 then
    for P in PrimesUpTo(150, F) do
      for K in QuadraticExtensionsWithConductor(P, [1,2]) do
        k := [1,1];
        HF := HeckeCharacterGroup(P, [1,2]);
        AH := 0;
        for chi in Elements(HF) do
          AH := AH + #PossibleGrossencharsOfRelQuadExt(K, P, k, chi);
        end for;
        G := ClassGroup(AbsoluteField(K));
        AM := (#G - #quo<G | 2*G>)/2; 
        assert AH eq AM;
      end for;
    end for;
  end if;
end for;

/***************************************************
* Tests computation of a dihedral form in the weight 
* [1,3] case and ensures it agrees with the form 
* obtained via Hecke stability.
***************************************************/

F := QuadraticField(5);
ZF := Integers(F);
N := Factorization(41*ZF)[1][1];
k := [1,3];
GRng := GradedRingOfHMFs(F, 150);
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;
Mk := HMFSpace(GRng, N, k, chi);
psis := PossibleGrossenchars(Mk);

// there should only be one Grossencharacter
assert #psis eq 1;

Dk := DihedralBasis(Mk);
assert #Dk eq 1;
f := Dk[1];
g := CuspFormBasis(Mk)[1];

// f and g should be the same (up to scaling)
assert #LinearDependence([f, g]) eq 1;
