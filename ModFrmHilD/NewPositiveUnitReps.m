///////////////////////////////////////////////////
//                                               //
//         The log Minkowski embedding           //
//                                               //
///////////////////////////////////////////////////

intrinsic LogMinkowski(M :: ModFrmHilDGRng, nu :: RngElt, prec :: RngIntElt
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
        epses := TotallyPositiveUnitsGenerators(F);
        lines := [LogMinkowski(M, eps, prec): eps in epses] cat [[1: i in [1..n]]];
        M`InverseLogMinkowski := Matrix(lines)^(-1);
        M`InverseLogMinkowskiPrec := prec;
    end if;

    return M`InverseLogMinkowski;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         The fundamental domain                //
//                                               //
///////////////////////////////////////////////////

/* In the future, we may want these functions to take a subgroup of totally
   positive units as input. */

intrinsic NewFunDomainRep(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, nu :: FldNumElt
                       : Precision := 100, CheckIfPresent := true
    ) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. We first check whether nu is listed in
FunDomainReps(M)[bb], in which case eps = 1.}

    F := BaseField(M);
    if CheckIfPresent then
        if IsDefined(FunDomainReps(M)[bb], nu) then
            return nu, F!1;
        end if;
    elif IsZero(nu) then
        return F!0, F!1;
    end if;

    /* Get nu' such that Log(nu') = x(1,..,1) + \sum \lambda_i Log(\eps_i) with
       -1/2 <= \lambda_i <= 1/2. We use inexact arithmetic and pray for the best */
    epses := TotallyPositiveUnitsGenerators(F);
    prec := Precision;
    THRESHOLD := 10^-10;

    mat := InverseLogMinkowski(M, prec);
    val := LogMinkowski(M, nu, prec);
    lambdas := Vector(val) * mat;

    unit := F!1;
    n := Degree(F);
    for i in [1..(n-1)] do
        m := Log(1 + Abs(lambdas[i])) / Log(10);
        if m gt (prec / 2) then
            error "Insufficient precision in FunDomainRep";
        end if;
        exp_i := Floor(lambdas[i] + 1/2 + THRESHOLD);
        unit := unit * epses[i] ^ exp_i;
    end for;

    nuprime := nu/unit;
    return nuprime, unit;
end intrinsic;

intrinsic NewFunDomainRep(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, nu :: FldOrdElt
                          : CheckIfPresent := true
    ) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. We first check whether nu is listed in
FunDomainReps(M)[bb], in which case eps = 1.}

    return NewFunDomainRep(M, bb, BaseField(M)!nu : CheckIfPresent := CheckIfPresent);
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
            a := TotallyPositiveBasis(M, bb^(-1));
            e := DualBasis(BaseField(M), a);
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

intrinsic TotallyPositiveBasis(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl
                               : bound := 20
    ) -> SeqEnum[FldNumElt]

{Returns a QQ-basis of elements of F that belong to bb and are totally
positive.}

    // Other idea: use reduced basis for trace form, then add multiples of 1?
    F := BaseField(M);
    n := Degree(F);
    map := (M`NarrowClassGroupMap)^(-1); //Ideals -> Narrow class group
    target := - map(bb); //inverse in abelian group
    idls := IdealsUpTo(bound, F);
    gens := [];
    for nn in idls do
        if map(nn) eq target then
            _, nu := IsNarrowlyPrincipal(nn * bb);
            Append(~gens, nu);
        end if;
    end for;
    mat := Matrix(Rationals(), [Eltseq(nu): nu in gens]);
    if Rank(mat) lt n then
        //try a higher bound
        return TotallyPositiveBasis(M, bb : bound := 2 * bound);
    end if;
    return [gens[i]: i in PivotRows(mat)];

end intrinsic;

intrinsic DualBasis(F :: FldNum, a :: SeqEnum) -> SeqEnum[FldNumElt]

{Given a QQ-basis a of F, returns its dual basis for the trace pairing.}

    n := Degree(F);
    qform := TraceMatrix(F);
    lat := LatticeWithBasis(n, &cat[Eltseq(x): x in a], qform);
    dual_basis := Basis(DualBasisLattice(lat));
    return [F ! Eltseq(x): x in dual_basis];

end intrinsic;

intrinsic Exponent(M :: ModFrmHilDGRng, bb :: RngOrdIdl, nu :: FldNumElt) -> SeqEnum[RngIntElt]

{Internal function: get exponent in Fourier expansion attached to nu}

    exp := Vector(Eltseq(nu)) * NuToExpMatrices(M)[bb];
    return [Integers() ! e: e in Eltseq(exp)];
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate FunDomainReps array          //
//                                               //
///////////////////////////////////////////////////

intrinsic NewPopulateFunDomainRepsArrays(M :: ModFrmHilDGRng)

{Internal function: populate M`FunDomainReps and associated arrays}

    // Get ideals
    prec := Precision(M);
    F := BaseField(M);
    n := Degree(F);
    ZF := Integers(F);
    dd := Different(ZF);
    idls := IdealsUpTo(prec, ZF); //TODO: use M`Ideals (already computed?)
    idl_info := AssociativeArray();

    // Initialize empty arrays
    M`PrecisionsByComponent := AssociativeArray();
    M`FunDomainReps := AssociativeArray();
    M`FunDomainRepsOfPrec := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        M`FunDomainReps[bb] := AssociativeArray();
        M`FunDomainRepsOfPrec[bb] := AssociativeArray();
        M`PrecisionsByComponent[bb] := [0];
    end for;

    // Collect precisions
    for nn in idls do
        bb := IdealToNarrowClassRep(M, nn);
        p := Norm(nn);
        idl_info[nn] := <bb, p>;
        if not p in M`PrecisionsByComponent[bb] then
            Append(~(M`PrecisionsByComponent[bb]), p);
        end if;
    end for;

    // Initialize arrays in FunDomainReps with zero ideal
    for bb in M`NarrowClassGroupReps do
        for p in M`PrecisionsByComponent[bb] do
            M`FunDomainRepsOfPrec[bb][p] := AssociativeArray();
        end for;
        M`FunDomainReps[bb][F ! 0] := 0;
        M`FunDomainRepsOfPrec[bb][0][F ! 0] := [0: i in [1..n]];
    end for;

    // Collect representatives and exponents
    for nn in idls do
        bb, p := Explode(idl_info[nn]);
        bbp := M`NarrowClassGroupRepsToIdealDual[bb];
        _, nu := IsNarrowlyPrincipal(nn * bbp);
        nu, _ := NewFunDomainRep(M, bb, nu : CheckIfPresent := false);
        M`FunDomainReps[bb][nu] := p;
        M`FunDomainRepsOfPrec[bb][p][nu] := Exponent(M, bb, nu);
    end for;

end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate Shadow array                 //
//                                               //
///////////////////////////////////////////////////

intrinsic PopulateShadowArray(M :: ModFrmHilDGRng : Precision := 100)

{Internal function: populate M`Shadows}

    M`NewShadows := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        M`NewShadows[bb] := AssociativeArray();
        for nu->p in M`FunDomainReps[bb] do
            M`NewShadows[bb][nu] := AssociativeArray();
        end for;
    end for;

    n := Degree(BaseField(M));
    if n eq 2 then
        PopulateShadowArrayQuadratic(M : Precision := Precision);
    else
        PopulateShadowArrayGen(M : Precision := Precision);
    end if;

end intrinsic;

intrinsic PopulateShadowArrayQuadratic(M :: ModFrmHilDGRng : Precision := 100)
{}
    prec := Precision;
    F := BaseField(M);
    eps := TotallyPositiveUnitsGenerators(F)[1];
    v := Evaluate(eps, Places(M)[1] : Precision := Precision);
    if v lt 1 then
        v := v^(-1);
    end if;
    logv := Log(v);
    THRESHOLD := 10^(-10);

    for bb in NarrowClassGroupReps(M) do
        m1 := 0;
        m2 := 0;
        // Compute real embeddings, m1, m2
        values := AssociativeArray();
        for nu->p in M`FunDomainReps[bb] do
            values[nu] := [Evaluate(nu, pl : Precision := Precision): pl in Places(M)];
            m1 := Max(m1, values[nu][1]);
            m2 := Max(m2, values[nu][2]);
        end for;
        logm1 := Log(m1);
        logm2 := Log(m2);
        // Enumerate units
        for nu->p in M`FunDomainReps[bb] do
            if p eq 0 then
                continue;
            end if;
            lbound := (- logm2 + Log(values[nu][2])) / logv - THRESHOLD;
            ubound := (logm1 - Log(values[nu][1])) / logv + THRESHOLD;
            if Log(-lbound)/Log(10) gt prec / 2 or Log(ubound)/Log(10) gt prec / 2 then
                error "Insufficient precision";
            end if;
            for j in [Ceiling(lbound)..Floor(ubound)] do
                M`NewShadows[bb][nu][eps^j] := Exponent(M, bb, nu * eps^j);
            end for;
        end for;
    end for;
end intrinsic;

intrinsic PopulateShadowArrayGen(M :: ModFrmHilDGRng : Precision := 100)
{}

    B := Precision(M);
    F := BaseField(M);
    n := Degree(F);

    prec := Precision;
    RR := RealField(prec);
    THRESHOLD := 10^(-10);
    V := VectorSpace(RR, n);

    epses := TotallyPositiveUnitsGenerators(F);
    log_epses := [V ! LogMinkowski(M, eps, prec): eps in epses];
    /* Get standard basis of R^n */
    etas := [];
    for i in [1..n] do
        v := [0: j in [1..n]];
        v[i] := 1;
        Append(~etas, V ! v);
    end for;
    /* Get lambda vectors */
    lambdas := [];
    for v in VectorSpace(GF(2), n-1) do
        Append(~lambdas, [(Integers()!(v[i])) - 1/2: i in [1..(n-1)]]);
    end for;
    logb := Log(RR ! B);

    for bb in NarrowClassGroupReps(M) do
        for nu in M`FunDomainReps[bb] do
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
end intrinsic;
