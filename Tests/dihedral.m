for d in [5, 13] do
    F := QuadraticField(d);  

    for P in PrimesUpTo(500, F) do
        for K in QuadraticExtensionsWithConductor(P, [1,2]) do
            HF := HeckeCharacterGroup(P);
            chi := HF ! 1;
            AH := #PossibleHeckeCharacters(F, P, K, chi);
            G := ClassGroup(AbsoluteField(K));
            AM := (#G - #quo<G | 2*G>)/2; 
            assert AH eq AM;
        end for;
    end for;
end for;