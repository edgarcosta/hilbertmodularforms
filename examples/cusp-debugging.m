discs := [d : d in [1..100] | IsFundamental(d)];
bad := [];
for d in discs do
  printf "testing disc = %o\n", d;
  K<nu> := QuadraticField(d);
  primes := PrimesUpTo(20,K);
  for P,Q in primes do
    NNs := [P, P*Q, P^2, P^2*Q];
    printf "testing conductors %o\n", NNs;
    for NN in NNs do
      if not CuspSanityCheck(NN : GammaType := "Gamma1") then
        printf "sanity check failed for K = %o, NN = %o\n", K, NN;
        Append(~bad, [* K, NN *]);
      end if;
    end for;
  end for;
end for;
