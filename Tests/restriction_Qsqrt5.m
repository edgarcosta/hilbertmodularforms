printf "Testing restriction to diagonal in Q(sqrt(5))...";
// Example we use Bruinier, van der Geer, Harder, Zagier - The 1-2-3 of Modular Forms, page 124
// We know that in Q(sqrt(5)) s6 is the delta function, the unique normalized cusp form of weight 12 for SL2(Z).
// s6 = 67·(25 ·33 ·52)−1 ·(g23 −g6),
F:=QuadraticField(5);
ZF:=Integers(F);
prec := 100;
M:=GradedRingOfHMFs(F, prec);
M2:=HMFSpace(M, [2,2]);
M6:=HMFSpace(M, [6,6]);

X:=HeckeCharacterGroup(1*ZF);
triv:=X!1;


E2:=EisensteinSeries(M2, triv, triv);
E6:=EisensteinSeries(M6, triv, triv);

assert RestrictionToDiagonal(E2, M, 1*ZF) eq Basis(ModularForms(Gamma0(1), 4))[1];
coeffs := RestrictionToDiagonal(E2, M, 1*ZF : AsCoefficients := true);
assert coeffs[1] eq 1;

half := RestrictionToDiagonal(E2/2, M, 1*ZF);
assert half eq Basis(BaseExtend(ModularForms(Gamma0(1), 4), Rationals()))[1]/2;
half_coeffs := RestrictionToDiagonal(E2/2, M, 1*ZF : AsCoefficients := true);
assert half_coeffs eq [c/2 : c in coeffs];
assert [Coefficient(qExpansion(half, #half_coeffs), j) : j in [0..#half_coeffs-1]] eq half_coeffs;

f := 67*(2^5*3^3*5^2)^(-1)*(E2^3-E6);
delta:= RestrictionToDiagonal(f,M,1*ZF);

modForms := ModularForms(Gamma0(1),12);
R<q> := PowerSeriesRing(Rationals());
assert 2*modForms.2 eq delta;
