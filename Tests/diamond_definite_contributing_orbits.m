// Regression: contributing-orbit (CFD) indexing in DiamondOperatorDefiniteBig
// (ModFrmHil/diamond.m).
//
// For a class-number-2 real quadratic field at a nonparallel higher weight, some
// Gamma-orbits on P^1(ZF/N) are non-contributing (#FD > #CFD): the stabilizer has
// no invariant vectors in the weight module. The diamond must iterate the
// contributing orbits with column offsets numbered by contributing orbits, else a
// non-contributing orbit's block overruns the next ideal class and <J> is not a
// genuine (semisimple, invertible, finite-order) diamond operator.
//
// Q(sqrt 10) (class number 2), level norm 4, weight [2,4].

import "ModFrmHil/diamond.m" : HeckeCharacterSubspace;

F := QuadraticField(10);
ZF := Integers(F);
assert ClassNumber(F) eq 2;        // need class number > 1 so diamonds are built at all
N := 2*ZF;                         // 2 ramifies; level of norm 4
k := [2, 4];                       // nonparallel higher weight => non-easy path with
                                   // non-contributing orbits (this is what triggered the bug)
M := HilbertCuspForms(F, N, k);
assert IsDefinite(M);
New := NewSubspace(M);
assert Dimension(New) eq 4;

// A genuine diamond operator <J> is finite order, hence semisimple and invertible.
// J generates the class group (order 2), so <J>^2 = 1 (trivial central character here).
Cl, mcl := ClassGroup(ZF);
assert #Cl eq 2;
J := mcl(Cl.1);
J := CoprimeRepresentative(J, N) * J;
dJ := DiamondOperator(New, J);
assert IsSquarefree(MinimalPolynomial(dJ));                  // semisimple
assert Determinant(dJ) ne 0;                                 // invertible (a unit)
assert dJ^2 eq IdentityMatrix(BaseRing(dJ), Nrows(dJ));      // order 2 => involution

// HeckeCharacterSubspace succeeds and the central-character eigenspaces partition
// the new space.
SetRationalBasis(New);
dims := [];
for chi in Elements(HeckeCharacterGroup(N, [1, 2])) do
  if IsCompatibleWeight(chi, k) then
    Append(~dims, Dimension(HeckeCharacterSubspace(New, chi)));
  end if;
end for;
assert &+dims eq Dimension(New);
assert Sort([d : d in dims | d ne 0]) eq [2, 2];
