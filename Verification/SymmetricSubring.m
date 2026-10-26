function SymmetricActionIsValid(I, images)
    R := Generic(I);
    if BaseRing(R) cmpne Rationals() or
        &or[w le 0 : w in VariableWeights(R)] or
        not IsHomogeneous(I) or R!1 in I or #images ne Rank(R) then
        return false;
    end if;
    for i in [1..#images] do
        ok, f := IsCoercible(R, images[i]);
        if not ok then return false; end if;
        if f ne 0 and (not IsHomogeneous(f) or
            WeightedDegree(f) ne WeightedDegree(R.i)) then
            return false;
        end if;
    end for;
    tau := hom<R -> R | images>;
    return &and[tau(f) in I : f in Basis(I)] and
        &and[tau(tau(R.i))-R.i in I : i in [1..Rank(R)]];
end function;

// Solve in a whole graded piece of R/I, including relations in generator weights.
function SymmetricExpression(I, images, f)
    R := Generic(I);
    f := NormalForm(f, I);
    if IsEmpty(images) then
        return f eq 0, Rationals()!0;
    end if;
    P := PolynomialRing(Rationals(), [WeightedDegree(g) : g in images]);
    if f eq 0 then return true, P!0; end if;
    w := WeightedDegree(f);
    mons := Setseq(MonomialsOfWeightedDegree(P, w));
    ambient := Setseq(MonomialsOfWeightedDegree(R, w));
    rows := [NormalForm(Evaluate(m, images), I) : m in mons];
    mat := Matrix(Rationals(), #rows, #ambient,
        &cat[[MonomialCoefficient(g, m) : m in ambient] : g in rows]);
    rhs := Vector(Rationals(), [MonomialCoefficient(f, m) : m in ambient]);
    ok, sol := IsConsistent(mat, rhs);
    if not ok then return false, P!0; end if;
    expression := &+[P | sol[i]*mons[i] : i in [1..#mons]];
    assert Evaluate(expression, images)-f in I;
    return true, expression;
end function;

function SymmetricGraphKernel(I, P, images)
    R := Generic(I);
    T := PolynomialRing(Rationals(), Rank(R)+Rank(P), "lex");
    target := hom<R -> T | [T.i : i in [1..Rank(R)]]>;
    graph := ideal<T | [target(g) : g in Basis(I)] cat
        [T.(Rank(R)+i)-target(images[i]) : i in [1..Rank(P)]]>;
    E := EliminationIdeal(graph, Rank(R));
    project := hom<T -> P | [P!0 : i in [1..Rank(R)]] cat
        [P.i : i in [1..Rank(P)]]>;
    return ideal<P | [project(g) : g in Basis(E)]>;
end function;

// Averaging an equivariant polynomial presentation shows that these elements
// generate the fixed ring, even when the action on the original variables is nonlinear.
function SymmetricClassicalGenerators(R, tau)
    plus := [R.i+tau(R.i) : i in [1..Rank(R)]];
    minus := [R.i-tau(R.i) : i in [1..Rank(R)]];
    return plus cat [minus[i]*minus[j] : j in [i..Rank(R)], i in [1..Rank(R)]];
end function;

intrinsic VerifySymmetricSubringPresentation(I::RngMPol, SwapImages::SeqEnum,
    K::RngMPol, InclusionImages::SeqEnum) -> BoolElt
{Certify that the inclusion has kernel K and image equal to the fixed ring of
 the supplied graded rational involution. The action is checked modulo I.}
    R := Generic(I); P := Generic(K);
    if not SymmetricActionIsValid(I, SwapImages) or
        BaseRing(P) cmpne Rationals() or not IsHomogeneous(K) or
        &or[w le 0 : w in VariableWeights(P)] or
        #InclusionImages ne Rank(P) then
        return false;
    end if;
    images := [R | ];
    tau := hom<R -> R | SwapImages>;
    for i in [1..Rank(P)] do
        ok, f := IsCoercible(R, InclusionImages[i]);
        if not ok then return false; end if;
        if f ne 0 and (not IsHomogeneous(f) or
            WeightedDegree(f) ne WeightedDegree(P.i)) then
            return false;
        end if;
        if tau(f)-f notin I then return false; end if;
        Append(~images, f);
    end for;
    if SymmetricGraphKernel(I, P, images) ne K then return false; end if;
    nonzero := [f : f in images | f ne 0];
    for f in SymmetricClassicalGenerators(R, tau) do
        ok, expression := SymmetricExpression(I, nonzero, f);
        if not ok then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic SymmetricSubringPresentation(I::RngMPol, SwapImages::SeqEnum)
    -> RngMPol, SeqEnum, FldFunRatUElt
{Return the fixed-ring ideal, its inclusion images in Generic(I), and its exact
 rational Hilbert series for a graded rational involution modulo I.
 The fixed algebra must have a positive-degree generator.}
    require SymmetricActionIsValid(I, SwapImages):
        "Expected a proper homogeneous rational ideal, positive weights, and a graded involution modulo the ideal";
    R := Generic(I);
    tau := hom<R -> R | SwapImages>;
    lifts := [R | ]; signs := [];
    for w in Sort(Setseq(Seqset(VariableWeights(R)))) do
        // Reynolds projections select an eigenbasis on indecomposables modulo
        // the subalgebra already generated in lower weights.
        for sign in [1,-1] do
            for i in [j : j in [1..Rank(R)] | WeightedDegree(R.j) eq w] do
                f := (R.i+sign*tau(R.i))/2;
                ok, expression := SymmetricExpression(I, lifts, f);
                if not ok then
                    assert tau(f)-sign*f in I;
                    Append(~lifts, f); Append(~signs, sign);
                end if;
            end for;
        end for;
    end for;
    reconstruction := [];
    for i in [1..Rank(R)] do
        ok, expression := SymmetricExpression(I, lifts, R.i);
        assert ok;
        Append(~reconstruction, expression);
    end for;
    fixed := [lifts[i] : i in [1..#lifts] | signs[i] eq 1];
    skew := [lifts[i] : i in [1..#lifts] | signs[i] eq -1];
    candidates := fixed cat [skew[i]*skew[j] : j in [i..#skew], i in [1..#skew]];
    images := [R | ];
    for w in Sort(Setseq({WeightedDegree(f) : f in candidates | f ne 0})) do
        for f in [g : g in candidates | g ne 0 and WeightedDegree(g) eq w] do
            ok, expression := SymmetricExpression(I, images, f);
            if not ok then Append(~images, f); end if;
        end for;
    end for;
    // Retain exact reconstruction certificates before forming the graph ideal.
    witnesses := candidates cat SymmetricClassicalGenerators(R, tau);
    certificates := [];
    for f in witnesses do
        ok, expression := SymmetricExpression(I, images, f);
        assert ok;
        Append(~certificates, expression);
    end for;
    require not IsEmpty(images): "The fixed algebra has no positive-degree generators";
    P := PolynomialRing(Rationals(), [WeightedDegree(f) : f in images]);
    K := SymmetricGraphKernel(I, P, images);
    assert &and[Evaluate(reconstruction[i], lifts)-R.i in I : i in [1..Rank(R)]];
    assert &and[Evaluate(certificates[i], images)-witnesses[i] in I :
        i in [1..#witnesses]];
    H := FunctionField(Rationals());
    return K, images, H!HilbertSeries(K);
end intrinsic;
