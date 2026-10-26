// Regression: the definite diamond operator must apply the nebentypus character
// twist (ModFrmHil/diamond.m, DiamondOperatorDefiniteBig), mirroring the twist
// that HeckeOperatorDefiniteBig applies. Without it, for a nontrivial Dirichlet
// nebentypus <J> is a plain permutation of the Gamma-orbits that ignores the
// character: it does not commute with the character-twisted Hecke operators, and
// gives the wrong order relation (<J>^2 = +1 rather than chi(J^2) = -1 for an
// order-2 central character).
//
// Distinct from the CFD indexing test (diamond_definite_contributing_orbits.m):
// here parallel weight [2,2] has #FD = #CFD and each weight block is the 1x1
// identity, so the twist factor is the only nontrivial content of the block,
// isolating the twist path.
//
// Case: Q(sqrt 10), narrow class number 2 (fundamental unit has norm -1), level
// N = the split prime of norm 13 (so (ZF/N)^* = F_13^* is nontrivial), weight
// [2,2], chi an order-2 nebentypus with nontrivial Dirichlet part. twist_factor
// = -1 on 8 of the diamond blocks.

import "ModFrmHil/diamond.m" : HeckeCharacterSubspace;

F := QuadraticField(10);
ZF := Integers(F);
assert ClassNumber(F) eq 2;           // narrow class number is also 2 here, so diamonds are built
N := Factorization(13 * ZF)[1][1];    // split prime of norm 13; (ZF/N)^* nontrivial => twist can fire
assert Norm(N) eq 13;
k := [2, 2];

// Pick an order-2 nebentypus whose Dirichlet (finite) part is nontrivial, so the
// twist actually fires. With parallel weight 2 the only compatible characters of
// interest are the quadratic ones.
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.0;
found := false;
for c in Elements(H) do
  dc := DirichletRestriction(c);
  if not IsTrivial(dc) and Order(dc) eq 2 and IsCompatibleWeight(c, k) then
    chi := c;
    found := true;
    break;
  end if;
end for;
assert found;
assert Order(DirichletRestriction(chi)) eq 2;

M := HilbertCuspForms(F, N, chi, k);
assert IsDefinite(M);
assert Dimension(M) eq 16;

Cl, mcl := ClassGroup(ZF);
J := mcl(Cl.1);
J := CoprimeRepresentative(J, N) * J;
dJ := DiamondOperator(M, J);
R := BaseRing(dJ);
Id := IdentityMatrix(R, Nrows(dJ));

// A genuine diamond operator is finite order, hence semisimple and invertible.
assert IsSquarefree(MinimalPolynomial(dJ));
assert Determinant(dJ) ne 0;

// J generates the (order-2) class group, J^2 is principal, and the order-2
// central character sends it to -1, so <J>^2 = -1 (not +1).
assert dJ^2 eq -Id;
assert dJ^2 ne Id;

// <J> must commute with the character-twisted Hecke operators.
nc := 0;
for pp in PrimesUpTo(7, F) do
  if Norm(N + pp) ne 1 then continue; end if;   // skip primes dividing the level
  Tp := HeckeOperator(M, pp);
  assert dJ * Tp eq Tp * dJ;
  nc +:= 1;
end for;
assert nc ge 3;
