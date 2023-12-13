
/* The log Minkowski embedding */

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

/* Fundamental domain representatives. In the future, we may want these
   functions to take a subgroup of totally positive units as input. */

intrinsic FunDomainRep(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, nu :: FldNumElt
    : CheckIfPresent := true, Precision := 100) -> FldNumElt, FldNumElt

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
    : CheckIfPresent := true) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. This version of FunDomainRep is a no-op if nu is
part of FunDomainReps(M)[bb].}

    return FunDomainRep(M, bb, BaseField(M)!nu : CheckIfPresent := CheckIfPresent);
end intrinsic;

/* Populating FunDomainRep arrays */

intrinsic NewPopulateFunDomainRepsArrays(M :: ModFrmHilDGRng)

{Internal function: populate M`FunDomainReps}

    prec := M`Precision;
    F := BaseField(M);
    ZF := Integers(F);
    dd := Different(ZF);
    idls := IdealsUpTo(prec, ZF);

    // The zero ideal lies in every component
    for bb in NarrowClassGroupReps(M) do
        M`FunDomainReps[bb] := [F!0];
    end for;

    for nn in idls do
        bb := IdealToNarrowClassRep(M, nn);
        bbp := bb * dd^-1;
        _, nu := IsNarrowlyPrincipal(nn * bbp);
        nu, _ := FunDomainRep(M, bb, nu : CheckIfPresent := false);
        Append(M`FunDomainReps[bb], nu);
    end for;

end intrinsic;

/* Populating shadow arrays */

intrinsic HMFPopulateShadowArrays(M :: ModFrmHilGRng : Precision := 100)

{Internal function: populate M`Shadows}

    n := Degree(BaseField(F));
    if n eq 2 then
        HMFPopulateShadowArrayQuadratic(M : Precision := Precision);
    else
        HMFPopulateShadowArrayGen(M : Precision := Precision);
    end if;

end intrinsic;

intrinsic HMFPopulateShadowArraysQuadratic(M :: ModFrmHilGRng : Precision := 100)
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
        // Compute real embeddings
        values := AssociativeArray();
        for nu in FunDomainReps(M)[bb] do
            values[nu] := [Evaluate(nu, pl : Precision := Precision): pl in Places(M)];
        end for;
        m1 := 0;
        m2 := 0;
        // Compute log(M1), log(M2)
        for nu in FunDomainReps(M)[bb] do
            m1 := Max(m1, values[nu][1]);
            m2 := Max(m2, values[nu][2]);
        end for;
        logm1 := Log(m1);
        logm2 := Log(m2);
        // Enumerate units
        for nu in FunDomainReps(M)[bb] do
            lbound := (- logm2 + Log(values[nu][2])) / logv - THRESHOLD;
            ubound := (logm1 - Log(values[nu][1])) / logv + THRESHOLD;
            if Log(-lbound)/Log(10) gt prec / 2 or Log(ubound)/Log(10) gt prec / 2 then
                error "Insufficient precision in HMFPopulateShadowArraysQuadratic";
            end if;
            jmax := Floor(ubound);
            jmin := Ceil(lbound);
            M`NewShadows[bb][nu] := [eps^j : j in [jmin..jmax]];
        end for;
    end for;
end intrinsic;

intrinsic HMFPopulateShadowArraysGen(M :: ModFrmHilGRng : Precision := 100)
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
        for nu in FunDomainReps(M)[bb] do
            M`NewShadows[bb][nu] := [];
            // Construct points in polytope
            points := [];
            lognu := Log(RR ! Norm(nu));
            pt0 := 1/n * V ! [logb : i in [1..n]];
            pt0 := pt0 - V ! LogMinkowski(M, nu, prec);
            for eta in etas do
                pt1 := pt0 - (logb - lognu) * eta;
                for lambda in lambdas do
                    pt := pt0;
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
                Append(~M`NewShadows[bb][nu], unit);
            end for;
        end for;
    end for;
end intrinsic;
