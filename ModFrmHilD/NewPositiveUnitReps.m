///////////////////////////////////////////////////
//                                               //
//         The log Minkowski embedding           //
//                                               //
///////////////////////////////////////////////////

intrinsic LogMinkowski(M :: ModFrmHilDGrng, nu :: FldNumElt, prec :: RngIntElt
    ) -> SeqEnum

{Returns the log-Minkowski embedding of nu as a point of R^n}

    return [Log(Evaluate(nu, pl)): pl in Places(M)];
end intrinsic;

intrinsic InverseLogMinkowski(M :: ModFrmHilDGRng, prec :: RngIntElt
    ) -> Mtrx

{Returns m^(-1), where m is the matrix whose first (n-1) lines are the
log-Minkowski values of the totally positive unit basis of F, whose last line is
(1,...,1)}

    if not assigned M`InverseLogMinkowski or M`InverseLogMinkowskiPrec lt prec then
        F := BaseField(M);
        n := Degree(F);
        epses := TotallyPositiveUnitGenerators(F);
        lines := [LogMinkowski(eps): eps in epses] cat [[1: i in [1..n]]];
        M`InverseLogMinkowski := Matrix(lines)^(-1);
        M`InverseLogMinkowskiPrec := prec;
    end if;

    return M`InverseLowMinkowskiPrec;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         The fundamental domain                //
//                                               //
///////////////////////////////////////////////////

/* In the future, we may want these functions to take a subgroup of totally
   positive units as input. */

intrinsic FunDomainRep(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, nu :: FldNumElt
                       : CheckIfPresent := true, Precision := 100
    ) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. If CheckIfPresent is true (default), the function
will check whether nu is listed in FunDomainReps(M)[bb].}

    if CheckIfPresent then
        if nu in FunDomainReps(M)[bb] then
            return nu, BaseField(M)!1;
        end if;
    end if;

    F := BaseField(M);
    if IsZero(nu) then
        return F!0, F!1;
    end if;

    /* Get nu' such that Log(nu') = x(1,..,1) + \sum \lambda_i Log(\eps_i) with
       -1/2 <= \lambda_i <= 1/2. We use inexact arithmetic and pray for the best */
    epses := TotallyPositiveUnitsGenerators(F);
    prec := Precision;
    THRESHOLD := 10^-10;

    mat := InverseLogMinkowski(M, prec);
    val := LogMinkowski(M, nu, prec);
    lambdas := val * mat;

    unit := F!1;
    for i in [1..(n-1)] do
        m := Log(1 + Abs(lambdas[i])) / Log(10);
        if m gt (prec / 2) then
            error "Insufficient precision in FunDomainRep";
        end if;
        exp_i := Floor(lambdas[i] + 1/2 + THRESHOLD);
        unit := unit * epses[i] ^ exp_i;
    end for;

    nuprime := nu/eps;
    return nuprime, eps;
end intrinsic;

intrinsic FunDomainRep(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, nu :: FldOrdElt
                       : CheckIfPresent := true
    ) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. This version of FunDomainRep is a no-op if nu is
part of FunDomainReps(M)[bb].}

    return FunDomainRep(M, bb, BaseField(M)!nu : CheckIfPresent := CheckIfPresent);
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Computing exponents                   //
//                                               //
///////////////////////////////////////////////////

intrinsic ExpToNuMatrices(M :: ModFrmHilDGRng) -> Assoc

{Returns an associative array indexed by component ideals: for each bb,
ExpToNuMatrices(M)[bb] is the inverse of NuToExpMatrices(M)[bb]}

    if not assigned M`NuToExpMatrices then
        M`ExpToNuMatrices := AssociativeArray();
        for bb in NarrowClassGroupReps(M) do
            a := TotallyPositiveBasis(bb^(-1));
            e := DualBasis(a);
            M`ExpToNuMatrices[bb] := Matrix(Rationals(), [Eltseq(x): x in e]);
        end for;
    end if;

    return M`ExpToNuMatrices;
end intrinsic;

intrinsic NuToExpMatrices(M :: ModFrmHilDGRng) -> Assoc

{Returns an associative array indexed by component ideals: for each bb,
NuToExpMatrices(M)[bb] contains a matrix m such that for each totally positive
nu in bbpinv, m*Eltseq(nu) has integral, nonnegative entries.}

    if not assigned M`NuToExpMatrices then
        invs := ExpToNuMatrices(M);
        M`NuToExpMatrices := AssociativeArray();
        for bb in NarrowClassGroupReps(M) do
            M`NuToExpMatrices[bb] := invs[bb]^(-1);
        end for;
    end if;

    return M`NuToExpMatrices;
end intrinsic;

intrinsic TotallyPositiveBasis(M :: ModFrmHilDGRng, bb :: RngOrdIdl
                               : bound := 20
    ) -> SeqEnum[FldNumElt]

{Returns a QQ-basis of elements of F that belong to bb and are totally
positive.}

    // Other idea: use reduced basis for trace form, then add multiples of 1?
    F := BaseField(M);
    map := (M`NarrowClassGroupMap)^(-1); //Ideals -> Narrow class group
    target := map(bb)^(-1);
    idls := IdealsUpTo(bound, F);
    gens := [];
    for nn in idls do
        if map(nn) eq target then
            nu := TotallyPositiveGenerator(nn * bb);
            Append(~gens, nu);
        end if;
    end for;
    mat := Matrix(Rationals(), [Eltseq(nu): nu in gen]);
    if Rank(mat) lt n then
        //try a higher bound
        return TotallyPositiveBasis(M, bb : bound := 2 * bound);
    end if;
    return [gens[i]: i in PivotRows(mat)];

end intrinsic;

intrinsic DualBasis(a :: SeqEnum[FldNumElt]) -> SeqEnum[FldNumElt]

{Given a QQ-basis a of F, returns its dual basis for the trace pairing.}

    F := Parent(a[1]);
    n := Degree(F);
    qform := TraceMatrix(F);
    lat := LatticeWithBasis(n, &cat[Eltseq(x): x in a], qform);
    dual_basis := Basis(DualBasisLattice(lat));
    return [F ! Eltseq(x): x in dual_basis];

end intrinsic;

intrinsic Exponent(M :: ModFrmHilGRng, bb :: RngOrdIdl, nu :: FldNumElt) -> SeqEnum[RngIntElt]

{Internal function: get exponent in Fourier expansion attached to nu}

    exp := Eltseq(nu) * NuToExpMatrices(M)[bb];
    return [Integers() ! exp[i]: i in [1..n]];
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate FunDomainReps array          //
//                                               //
///////////////////////////////////////////////////

intrinsic NewPopulateFunDomainRepsArrays(M :: ModFrmHilDGRng)

{Internal function: populate M`FunDomainReps}

    // Get ideals
    prec := Precision(M);
    F := BaseField(M);
    n := Degree(F);
    ZF := Integers(F);
    dd := Different(ZF);
    idls := IdealsUpTo(prec, ZF); //TODO: use M`Ideals (already computed?)
    idl_info := AssociativeArray();

    // Initialize empty arrays
    M`FunDomainReps := AssociativeArray();
    M`FunDomainRepsPrecisions := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        M`FunDomainReps[bb] := AssociativeArray();
        M`FunDomainRepsPrecisions[bb] := [0];
    end for;

    // Collect precisions
    for nn in idls do
        bb := IdealToNarrowClassRep(M, nn);
        p := Norm(nn);
        idl_info[nn] := <bb, p>;
        if not p in M`FunDomainRepsPrecisions[bb] then
            Append(~(M`FunDomainRepsPrecisions[bb]), p);
        end if;
    end for;

    // Initialize arrays in FunDomainReps with zero ideal
    for bb in M`NarrowClassGroupReps do
        for p in M`FunDomainRepsPrecisions[bb] do
            M`FunDomainReps[bb][p] := AssociativeArray();
        end for;
        M`FunDomainReps[bb][0][F ! 0] := [0: i in [1..n]];
    end for;

    // Collect representatives and exponents
    for nn in idls do
        bb, p := idl_info[nn];
        bbp := M`NarrowClassGroupRepsToIdealDual[bb];
        _, nu := IsNarrowlyPrincipal(nn * bbp);
        nu, _ := FunDomainRep(M, bb, nu : CheckIfPresent := false);
        M`FunDomainReps[bb][p][nu] := Exponent(M, bb, nu);
    end for;

end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate Shadow array                 //
//                                               //
///////////////////////////////////////////////////

intrinsic PopulateShadowArray(M :: ModFrmHilGRng : Precision := 100)

{Internal function: populate M`Shadows}

    M`NewShadows := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        M`NewShadows[bb] := AssociativeArray();
        for p in M`PrecisionsByComponent[bb] do
            for nu->exp in M`FunDomainReps[bb][p] do
                M`NewShadows[bb][nu] := AssociativeArray();
            end for;
        end for;
    end for;

    n := Degree(BaseField(F));
    if n eq 2 then
        PopulateShadowArrayQuadratic(M : Precision := Precision);
    else
        PopulateShadowArrayGen(M : Precision := Precision);
    end if;

end intrinsic;

intrinsic PopulateShadowArrayQuadratic(M :: ModFrmHilGRng : Precision := 100)
{}
    prec := Precision;
    F := BaseField(M);
    eps := TotallyPositiveUnitsGenerators(F)[1];
    v := Evaluate(eps, Places(M)[1] : Precision := Precision);
    if v lt 1 then
        v := v^(-1);
    end if;
    logv := Log(v);
    THRESHOLD = 10^(-10);

    for bb in NarrowClassGroupReps(M) do
        m1 := 0;
        m2 := 0;
        // Compute real embeddings, m1, m2
        for p in M`PrecisionsByComponent[bb] do
            values := AssociativeArray();
            for nu in FunDomainReps(M)[bb][p] do
                values[nu] := [Evaluate(nu, pl : Precision := Precision): pl in Places(M)];
                m1 := Max(m1, values[nu][1]);
                m2 := Max(m2, values[nu][2]);
            end for;
        end for;
        logm1 := Log(m1);
        logm2 := Log(m2);
        // Enumerate units
        for p in M`PrecisionsByComponent[bb] do
            for nu in FunDomainReps(M)[bb][p] do
                lbound := (- logm2 + Log(values[nu][2])) / logv - THRESHOLD;
                ubound := (logm1 - Log(values[nu][1])) / logv + THRESHOLD;
                if Log(-lbound)/Log(10) gt prec / 2 or Log(ubound)/Log(10) gt prec / 2 then
                    error "Insufficient precision";
                end if;
                for j in [Ceil(lbound)..Floor(ubound)] do
                    M`NewShadows[bb][nu][eps^j] := Exponent(M, bb, nu * eps^j);
                end for;
            end for;
        end for;
    end for;
end intrinsic;

intrinsic PopulateShadowArrayGen(M :: ModFrmHilGRng : Precision := 100)
{}
    prec := Precision;
    RR := RealField(prec);
    THRESHOLD := 10^(-10);
    V := VectorSpace(RR, n);

    B := Precision(M);
    F := BaseField(F);
    n := Degree(F);
    epses := TotallyPositiveUnitsGenerators(F);
    log_epses := [V ! LogMinkowski(M, eps, prec): eps in epses];
    /* Get standard basis of R^n */
    etas := [];
    for i in [1..n] do
        v := [0: j in [1..n]];
        v[i] := j;
        Append(~etas, V ! v);
    end for;
    /* Get lambda vectors */
    lambdas := [];
    for v in VectorSpace(GF(2), n-1) do
        Append(~lambdas, [(Integers()!(v[i])) - 1/2: i in [1..(n-1)]]);
    end for;
    logb := Log(RR ! B);

    for bb in NarrowClassGroupReps(M) do
        for p in M`PrecisionsByComponent[bb] do
            for nu in FunDomainReps(M)[bb][p] do
                // Construct points in polytope
                points := [];
                lognu := Log(RR ! Norm(nu));
                pt0 := 1/n * V ! [logb : i in [1..n]];
                pt0 := pt0 - V ! LogMinkowski(M, nu, prec);
                for eta in etas do
                    pt1 := pt0 - (logb - lognu) * eta;
                    for lambda in lambdas do
                        pt := pt1;
                        for i in [1..(n-1)] do
                            pt := pt + (1 + THRESHOLD) * lambda[i] * log_epses[i];
                        end for;
                        Append(~points, pt);
                    end for;
                end for;
                // Construct polytope
                vertices := [];
                for pt in points do
                    vertex := pt * InverseLogMinkowski(M);
                    vertex := Eltseq(vertex)[1..(n-1)];
                    Append(~vertices, Rationalize(vertex));
                end for;
                P := Polytope(vertices);
                // Get units
                for pt in Points(P) do
                    unit := F!1;
                    for i in [1..(n-1)] do
                        unit := unit * epses[i] ^ pt[i];
                    end for;
                    M`NewShadows[bb][nu][unit] := Exponent(M, bb, unit * nu);
                end for;
            end for;
        end for;
    end for;
end intrinsic;
