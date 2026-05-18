// TODO: indefinite HeckeMatrix2 fails when h+ > 1 (here h+ = 2 for
// F = Q[w]/(w^3-4w-1), LMFDB 3.3.229.1). Then HeckeMatrix1 is called
// with ind != indp, so Gamma_datum != Gammap_datum, and InducedH1
// builds the cocycle kernels from different coset reps and weight-rep
// blocks over a field; Htildep * M is no longer in Domain(mH)
// (level.m ~L774). Upstream keeps both kernels in a common Z-lattice
// by using integer coset-permutation matrices in InducedH1 and
// applying the weight twist separately via Zp in HeckeMatrix1.

// Test Hecke and AtkinLehner, verifying definite vs indefinite,
// over cubic field

SetVerbose("ModFrmHil", 1);
SetVerbose("Shimura", 1);

F<w> := NumberField(Polynomial([-1,-4,0,1]));
Z_F := Integers(F);

SetStoreModularForms(F, true);

M := HilbertCuspForms(F, 1*Z_F);
assert Dimension(M) eq 0;

O := QuaternionOrder(M);

NNs := [ideal<Z_F | [26, 675*w^2 + 675]>,
        ideal<Z_F | [29, 29, w + 13]>,
        ideal<Z_F | [49, 7, 2*w^2 - w - 4]>,
        ideal<Z_F | [94, 94, 8835*w^2 + 8835*w + 8668]>];

Ps := PrimesUpTo(10, F);

for NN in NNs do

  M := HilbertCuspForms(F, NN);
  time "Space of level", Norm(NN), "has dimension", Dimension(M);

  // indefinite
  S := NewSubspace(M : QuaternionOrder := O);
  indefcharpolys := [ <Norm(pp), CharacteristicPolynomial(HeckeOperator(S,pp))> : pp in Ps];
  print indefcharpolys;

  // definite
  Odef := MaximalOrder(QuaternionAlgebra(Factorization(NN)[1,1], InfinitePlaces(F)));
  Sdef := NewSubspace(M : QuaternionOrder := Odef);
  defcharpolys := [ <Norm(pp), CharacteristicPolynomial(HeckeOperator(Sdef,pp))> : pp in Ps];
  print defcharpolys;

  assert forall{i : i in [1..#defcharpolys] | defcharpolys[i] eq indefcharpolys[i]};

  D := Discriminant(QuaternionOrder(Sdef));
  for pp in [pp[1] : pp in Factorization(NN)] do
    print Norm(pp), AtkinLehnerOperator(S, pp);
    if Valuation(D,pp) eq 0 then
      assert CharacteristicPolynomial(AtkinLehnerOperator(Sdef, pp)) eq
             CharacteristicPolynomial(AtkinLehnerOperator(S, pp));
    end if;
  end for;

end for;

