for d in [5, 13] do
  F := QuadraticField(d);  

  for P in PrimesUpTo(500, F) do
    for K in QuadraticExtensionsWithConductor(P, [1,2]) do
      HF := HeckeCharacterGroup(P, [1,2]);
      AH := 0;
      for chi in Elements(HF) do
        AH := AH + #PossibleHeckeCharactersOfK(F, P, K, chi);
      end for;
      G := ClassGroup(AbsoluteField(K));
      AM := (#G - #quo<G | 2*G>)/2; 
      assert AH eq AM;
    end for;
  end for;
end for;
