// Algebraic comparison for component 2.1, not a literature certificate.
// The Theorem 10 candidate uses an assumed sign action, coefficient 4 in
// equation (13), and a -3 twist. The action and rational descent remain
// unidentified geometrically. Keep eval-loaded data flat for run_tests.m.
SetNthreads(4);

label := "2.2.24.1-1.1";
components := LoadStoredCanonicalRings(label);
sane, report := VerifyCanonicalRingComponents(label, components);
assert sane;
assert &and[row[2] : row in report];
matches := [i : i in [1..#components] | components[i][1] eq "2.1"];
assert #matches eq 1;
J := components[matches[1]][2];
T := Generic(J);
X := T.1; Y := T.2; C := T.3; Z := T.4;
litfile := "Verification/LiteratureEquations/2.2.24.1-1.1-vdGeer-corrected-twist.m";
LitData := eval(Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation, storedSHA256, componentLabel := LitData(T, T);
assert componentLabel eq components[matches[1]][1];
storedfile := "Verification/CanonicalRingEquations/2.2.24.1-1.1-gl-0.m";
assert Split(Pipe("sha256sum " cat storedfile, ""), " ")[1] eq storedSHA256;

// Completing the square makes the branch intrinsic to this weighted double cover.
// The two weight-2 factors are X,L; the two weight-4 factors are C,D.
g := SmallBasis(J)[1];
assert #Basis(J) eq 1 and Degree(g,4) eq 2;
quad := MonomialCoefficient(g,Z^2);
lin := Coefficient(g,4,1);
U := Z+lin/(2*quad);
H := lin^2/(4*quad^2)-Coefficient(g,4,0)/quad;
assert g eq quad*(U^2-H);
L := X+Y/8;
D := X*Y+8*C;
Qt := X^4-X^3*Y/64-13*X^2*C/8+5*X*Y*C/32-Y^2*C/512+2*C^2;
branch := X*L*C*D*Qt;
mon := Monomials(branch)[1];
scale := MonomialCoefficient(H,mon)/MonomialCoefficient(branch,mon);
assert scale ne 0 and H eq scale*branch;

// Odd exponents of distinct linear factors in each discriminant prove that
// Qs and Qt remain irreducible over the algebraic closure of the constants.
A<p,a,c> := PolynomialRing(Rationals(),[2,2,4]);
Qs := 256*c^2-128*c*a^2+16*a^4+144*c*a*p-27*c*p^2-4*a^3*p;
discS := Coefficient(Qs,3,1)^2-4*Coefficient(Qs,3,2)*Coefficient(Qs,3,0);
discT := Coefficient(Qt,3,1)^2-4*Coefficient(Qt,3,2)*Coefficient(Qt,3,0);
for pair in [* <discS,p*(p-32/9*a)^3>, <discT,L*(X-Y/56)^3> *] do
    mon := Monomials(pair[2])[1];
    scale := MonomialCoefficient(pair[1],mon)/MonomialCoefficient(pair[2],mon);
    assert scale ne 0 and pair[1] eq scale*pair[2];
    assert not IsSquare(pair[1]);
end for;

// For printed (13), d-12*c=a*(9*p-a) must map to a multiple of X*Y.
// Matching the weight-2 factors forces a=X, p=L/9, up to grading scale.
// The weight-4 factors c,d can map to C,D in either order; these are both cases.
for swap in [false,true] do
    pImage := L/9;
    aImage := X;
    cImage := swap select -D/96 else C/12;
    dImage := 9*pImage*aImage-aImage^2+12*cImage;
    assert dImage eq (swap select -C else D/8);
    quarticImage := Evaluate(Qs,[pImage,aImage,cImage]);
    scale := MonomialCoefficient(quarticImage,X^3*Y)/MonomialCoefficient(Qt,X^3*Y);
    assert quarticImage ne scale*Qt;
end for;
print "Q(sqrt6) component 2.1: branch obstruction for printed equation (13) under the assumed sign action.";

// The coefficient-4 correction changes the middle term to -4*sigma4*sigma2^2.
// vdG p. 175 describes six nodes and twelve cusps on the octic factor.
// The printed coefficient has Jacobian length 6; coefficient 4 gives length 30.
R<s,t,u> := PolynomialRing(Rationals(),3);
v := -s-t-u;
sigma2 := s*t+s*u+s*v+t*u+t*v+u*v;
sigma3 := s*t*u+s*t*v+s*u*v+t*u*v;
sigma4 := s*t*u*v;
octics := [9*sigma3^2*sigma2-k*sigma4*sigma2^2+12*sigma4^2 : k in [1,4]];
for i in [1..2] do
    jac := ideal<R | [Derivative(octics[i],j) : j in [1..3]]>;
    assert IsHomogeneous(jac) and Dimension(jac) eq 1;
    assert Degree(jac) eq [6,30][i];
    assert Degree(Radical(jac)) eq [6,18][i];
end for;

// All corrected singular points are rational over Q(sqrt(-2)). A rank-2
// Hessian gives an A1 node; rank 1 and a nonzero cubic along its kernel give
// an A2 cusp. This checks local types as well as the scheme length.
B<z> := PolynomialRing(Rationals());
K<h> := NumberField(z^2+2);
P := ProjectiveSpace(K,2);
S := Scheme(P,[Evaluate(f,[P.1,P.2,P.3]) : f in Basis(jac)]);
points := Points(S);
assert #points eq 18;
B<x,y> := PolynomialRing(K,2);
nodes := 0; cusps := 0;
for point in points do
    coords := Eltseq(point);
    index := [i : i in [1..3] | coords[i] ne 0][1];
    coords := [c/coords[index] : c in coords];
    free := [i : i in [1..3] | i ne index];
    localcoords := [B!c : c in coords];
    localcoords[free[1]] +:= x;
    localcoords[free[2]] +:= y;
    f := Evaluate(octics[2],localcoords);
    assert Evaluate(f,[0,0]) eq 0;
    assert &and[Evaluate(Derivative(f,i),[0,0]) eq 0 : i in [1..2]];
    hessian := Matrix(K,2,2,[Evaluate(Derivative(Derivative(f,i),j),[0,0])
        : i,j in [1..2]]);
    if Rank(hessian) eq 2 then
        assert &and[Evaluate(Derivative(octics[1],i),coords) eq 0 : i in [1..3]];
        nodes +:= 1;
    else
        assert Rank(hessian) eq 1;
        assert &or[Evaluate(Derivative(octics[1],i),coords) ne 0 : i in [1..3]];
        direction := Eltseq(Basis(Nullspace(hessian))[1]);
        cubic := &+[B | MonomialCoefficient(f,m)*m : m in Monomials(f) | TotalDegree(m) eq 3];
        assert Evaluate(cubic,direction) ne 0;
        cusps +:= 1;
    end if;
end for;
assert nodes eq 6 and cusps eq 12;
assert Degree(jac) eq nodes+2*cusps;
print "Coefficient-4 octic: six A1 nodes and twelve A2 cusps; Jacobian length 6*1 + 12*2 = 30 (printed: 6).";

// The corrected branch has ratio -4/243 to the stored completed square.
// Multiplying it by -3 gives 4/81, with the stored map w -> 2*U/9.
pImage := PhiImages[1]; aImage := PhiImages[2]; cImage := PhiImages[3];
correctedBranch := pImage*aImage*(9*aImage*pImage-4*aImage^2+12*cImage)*cImage
    *Evaluate(Qs,[pImage,aImage,cImage]);
assert correctedBranch eq -4/243*H;
assert not IsSquare(Rationals()!(-4/243));
assert -3*correctedBranch eq 4/81*H;
assert PhiImages[4] eq 2/9*U;
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt6) component %o: algebraic isomorphism with %o; sign action and rational descent not derived geometrically.\n",
    componentLabel, citation;
