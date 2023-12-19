///////////////////////////////////////////////////
//                                               //
//         The log Minkowski embedding           //
//                                               //
///////////////////////////////////////////////////

intrinsic LogMinkowski(M :: ModFrmHilDGRng, nu :: RngElt, prec :: RngIntElt
    ) -> SeqEnum

{Returns the log-Minkowski embedding of nu as a point of R^n}

    return [Log(Evaluate(nu, pl : Precision := prec)): pl in Places(M)];
end intrinsic;

intrinsic InverseLogMinkowski(M :: ModFrmHilDGRng, prec :: RngIntElt) -> Mtrx

{Returns m^(-1), where m is the matrix whose first (n-1) lines are the
log-Minkowski values of the totally positive unit basis of F, and whose last
line is (1,...,1)}

    if not assigned M`InverseLogMinkowski or M`InverseLogMinkowskiPrec lt prec then
        F := BaseField(M);
        n := Degree(F);
        epses := TotallyPositiveUnitsGenerators(F);
        lines := [LogMinkowski(M, eps, prec): eps in epses] cat [[1: i in [1..n]]];
        M`InverseLogMinkowski := Matrix(lines)^(-1);
        M`InverseLogMinkowskiPrec := prec;
        return M`InverseLogMinkowski;
    else
        n := Degree(BaseField(M));
        return MatrixAlgebra(RealField(prec), n) ! M`InverseLogMinkowski;
    end if;

end intrinsic;

intrinsic InverseLogMinkowskiSqr(M :: ModFrmHilDGRng, prec :: RngIntElt) -> Mtrx

{Returns m^(-1), where m is the matrix whose first (n-1) lines are the
log-Minkowski values of a basis of square units in F, and whose last line is
(1,...,1)}

    if not assigned M`InverseLogMinkowskiSqr or M`InverseLogMinkowskiSqrPrec lt prec then
        F := BaseField(M);
        n := Degree(F);
        epses := [x^2: x in UnitsGenerators(F)];
        lines := [LogMinkowski(M, eps, prec): eps in epses] cat [[1: i in [1..n]]];
        M`InverseLogMinkowskiSqr := Matrix(lines)^(-1);
        M`InverseLogMinkowskiSqrPrec := prec;
        return M`InverseLogMinkowskiSqr;
    else
        n := Degree(BaseField(M));
        return MatrixAlgebra(RealField(prec), n) ! M`InverseLogMinkowskiSqr;
    end if;

end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         The fundamental domain                //
//                                               //
///////////////////////////////////////////////////

/* In the future, we may want these functions to take a subgroup of totally
   positive units as input. */

intrinsic FunDomainRep(M :: ModFrmHilDGRng, nu :: RngElt
                       : Precision := 100, CheckComponent := false, Squares := false
    ) -> FldNumElt, FldNumElt

{Returns an element nu' in the fundamental domain and a totally positive unit
eps such that nu = eps * nu'. We first check whether nu is listed in
M`FunDomainReps[bb], in which case eps = 1.}

    F := BaseField(M);
    nu := F ! nu;
    if not CheckComponent cmpeq false then
        bb := CheckComponent;
        if IsDefined(M`FunDomainReps[bb], nu) then
            return nu, F!1;
        end if;
    elif IsZero(nu) then
        return F!0, F!1;
    end if;

    /* Get nu' such that Log(nu') = x(1,..,1) + \sum \lambda_i Log(\eps_i) with
       -1/2 <= \lambda_i <= 1/2. We use inexact arithmetic and pray for the best */
    prec := Precision;
    THRESHOLD := 10^-10;
    if Squares then
        epses := [x^2: x in UnitsGenerators(F)];
        mat := InverseLogMinkowskiSqr(M, prec);
    else
        epses := TotallyPositiveUnitsGenerators(F);
        mat := InverseLogMinkowski(M, prec);
    end if;

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

//Another version of TotallyPositiveBasis, not as good
intrinsic TotallyPositiveBasisSmallNorm(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl
                                        : bound := 20
    ) -> SeqEnum[FldNumElt]

{Returns a QQ-basis of elements of F that belong to bb and are totally
positive.}

    F := BaseField(M);
    n := Degree(F);
    map := (M`NarrowClassGroupMap)^(-1); //Ideals -> Narrow class group
    target := - map(bb); //inverse in abelian group
    idls := IdealsUpTo(bound, F);
    gens := [];
    for nn in idls do
        if map(nn) eq target then
            _, nu := IsNarrowlyPrincipal(nn * bb);
            Append(~gens, F ! nu);
        end if;
    end for;
    mat := Matrix(Rationals(), [Eltseq(nu): nu in gens]);
    if Rank(mat) lt n then
        //try a higher bound
        return TotallyPositiveBasis(M, bb : bound := 2 * bound);
    end if;
    return [gens[i]: i in PivotRows(mat)];

end intrinsic;

intrinsic TotallyPositiveBasis(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl
    ) -> SeqEnum[FldNumElt]

{Returns a QQ-basis of elements of F that belong to bb and are totally
positive.}

    require not IsZero(bb): "Cannot find totally positive basis of zero ideal";
    F := BaseField(M);
    n := Degree(F);
    basis := [F!x : x in Basis(bb)];
    d := Denominator(bb);
    a := Norm(d * bb) / d; // lies in bb\cap QQ and is positive

    //arrange that a lies in the basis
    if not F!a in basis then
        mat := Matrix(Rationals(), [Eltseq(F ! a)] cat [Eltseq(x) : x in basis]);
        basis := [F ! mat[i]: i in PivotRows(mat)];
        assert F!a in basis;
    end if;
    //add multiples of a to other basis vectors if needed
    for i in [1..n] do
        vec := EmbedNumberFieldElement(basis[i]);
        m := Ceiling(Min([v/a: v in EmbedNumberFieldElement(basis[i])])) - 1;
        if m lt 0 then
            basis[i] := basis[i] - m * a;
        end if;
    end for;
    assert Rank(Matrix(Rationals(), [Eltseq(x) : x in basis])) eq n;

    return basis;
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
    exp := [Integers() ! e: e in Eltseq(exp)];
    assert &and[x ge 0: x in exp];
    return exp;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate FunDomainReps array          //
//                                               //
///////////////////////////////////////////////////

intrinsic PopulateFunDomainReps(M :: ModFrmHilDGRng)

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
        nu, _ := FunDomainRep(M, nu);
        M`FunDomainReps[bb][nu] := p;
        M`FunDomainRepsOfPrec[bb][p][nu] := Exponent(M, bb, nu);
    end for;

end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Populate LowerSet array               //
//                                               //
///////////////////////////////////////////////////

intrinsic PopulateLowerSet(M :: ModFrmHilDGRng : Precision := 100)

{Internal function: populate M`LowerSet}

    F := BaseField(M);
    ZF := Integers(F);
    n := Degree(F);
    M`LowerSet := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        M`LowerSet[bb] := AssociativeArray();
        for nu->p in M`FunDomainReps[bb] do
            M`LowerSet[bb][nu] := AssociativeArray();
        end for;
        //Add zero on each component
        M`LowerSet[bb][F!0] := AssociativeArray();
        M`LowerSet[bb][F!0][ZF!1] := [0: i in [1..n]];
    end for;

    n := Degree(BaseField(M));
    if n eq 2 then
        PopulateLowerSetArrayQuadratic(M : Precision := Precision);
    else
        PopulateLowerSetArrayGen(M : Precision := Precision);
    end if;

end intrinsic;


intrinsic PopulateLowerSetArrayQuadratic(M :: ModFrmHilDGRng : Precision := 100)
{}
    F := BaseField(M);
    eps := TotallyPositiveUnitsGenerators(F)[1];
    v := Evaluate(eps, Places(M)[1] : Precision := Precision);
    //force v > 1
    if v lt 1 then
        eps := eps^(-1);
        v := v^(-1);
    end if;
    logv := Log(v);
    THRESHOLD := 10^(-10);

    for bb in NarrowClassGroupReps(M) do
        m1 := 10^-Precision;
        m2 := 10^-Precision;
        // Compute real embeddings, m1, m2
        values := AssociativeArray();
        for nu->p in M`FunDomainReps[bb] do
            values[nu] := [Evaluate(nu, pl : Precision := Precision): pl in Places(M)];
            m1 := Max(m1, values[nu][1]);
            m2 := Max(m2, values[nu][2]);
        end for;
        if m1 eq 0 then m1 := eps; end if;
        if m2 eq 0 then m2 := eps; end if;
        logm1 := Log(m1);
        logm2 := Log(m2);
        // Enumerate units
        for nu->p in M`FunDomainReps[bb] do
            if p eq 0 then
                continue;
            end if;
            lbound := (- logm2 + Log(values[nu][2])) / logv - THRESHOLD;
            ubound := (logm1 - Log(values[nu][1])) / logv + THRESHOLD;
            if Log(-lbound)/Log(10) gt Precision / 2 or Log(ubound)/Log(10) gt Precision / 2 then
                error "Insufficient precision";
            end if;
            for j in [Ceiling(lbound)..Floor(ubound)] do
                M`LowerSet[bb][nu][eps^j] := Exponent(M, bb, nu * eps^j);
            end for;
        end for;
    end for;
end intrinsic;

intrinsic PopulateLowerSetArrayGen(M :: ModFrmHilDGRng : Precision := 100)
{}

    B := M`Precision;
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
        for nu->p in M`FunDomainReps[bb] do
            if p eq 0 then
                continue;
            end if;
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
                vertex := pt * InverseLogMinkowski(M, prec);
                vertex := Eltseq(vertex)[1..(n-1)];
                Append(~vertices, Rationalize(vertex));
            end for;
            P := Polytope(vertices);
            // Get units
            for pt in Points(P) do
                unit := F!1;
                for i in [1..(n-1)] do
                    unit := unit * epses[i] ^ Eltseq(pt)[i];
                end for;
                M`LowerSet[bb][nu][unit] := Exponent(M, bb, unit * nu);
            end for;
        end for;
    end for;
end intrinsic;

intrinsic Rationalize(A::SeqEnum[FldReElt] : Precision := 100) -> SeqEnum[FldRatElt]

{Returns a sequence of rational numbers that are reasonable approximations to
the given real numbers.}

    return [BestApproximation(A[i], 10^(Precision - 1)) : i in [1 .. #A]];
end intrinsic;

intrinsic Rationalize(v::ModTupFldElt : Precision := 100) -> SeqEnum[FldRatElt]

{Returns a sequence of rational numbers that is a reasonable approximation to
the given tuple of real numbers.}

  return Rationalize(ElementToSequence(v) : Precision := Precision);
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Access representatives                //
//                                               //
///////////////////////////////////////////////////


intrinsic FunDomainReps(M::ModFrmHilDGRng) -> Assoc

{Returns an associative array indexed by component ideals, whose values are
SetEnums. This is not M`FunDomainReps, which is an associative array of
associative arrays}

    res := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
        res[bb] := [* x: x in Keys(M`FunDomainReps[bb]) *];
    end for;
    return res;
end intrinsic;

intrinsic FunDomainRepsOfPrec(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, prec :: RngIntElt
    ) -> SeqEnum

{Returns the set of fundamental domain representatives of precision prec}

    return SetToSequence(Keys(M`FunDomainRepsOfPrec[bb][prec]));
end intrinsic;

intrinsic FunDomainRepsUpToPrec(M :: ModFrmHilDGRng, bb :: RngOrdFracIdl, prec :: RngIntElt
    ) -> SeqEnum

{Returns the list of nus to the specified precision. Deprecated: use
M`FunDomainReps[bb][p] instead}

    precs := [p : p in M`PrecisionsByComponent[bb] | p le prec];
    reps := [];
    for p in precs do
        reps := reps cat SetToSequence(Keys(M`FunDomainRepsOfPrec[bb][p]));
    end for;
    return reps;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Deprecated computation of Mpairs      //
//                                               //
///////////////////////////////////////////////////

intrinsic EmbedNumberFieldElement(nu::FldNumElt : Precision := 100) -> SeqEnum
{}
    F := Parent(nu);
    return [Evaluate(nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic EmbedNumberFieldElement(nu::RngOrdElt : Precision := 100) -> SeqEnum
{}
    F := NumberField(Parent(nu));
    return EmbedNumberFieldElement(F ! nu : Precision := Precision);
end intrinsic;

intrinsic IsDominatedBy(alpha::FldNumElt, beta::FldNumElt) -> BoolElt
  {
    input:
      alpha: an element of a totally real number field F
      beta: an element of a totally real number field F
   returns:
      true if and only if every coordinate of the embedding of alpha in R^n
      is less than or equal to corresponding coordinate in the embedding of
      beta in R^n
  }
  n := Degree(Parent(alpha));
  alpha_embed := EmbedNumberFieldElement(alpha);
  beta_embed := EmbedNumberFieldElement(beta);
  return &and[alpha_embed[i] le beta_embed[i]: i in [1..n]];
end intrinsic;

intrinsic ComputeMPairs(M::ModFrmHilDGRng, bb::RngOrdFracIdl) -> Any
{temporary function, just to ensure compatibility}
    MPairs_bb := AssociativeArray();
    for nu in Keys(M`FunDomainReps[bb]) do
        MPairs_bb[nu] := [];
        for nu1 in Keys(M`FunDomainReps[bb]) do
            for eps1 in Keys(M`LowerSet[bb][nu1]) do
                if IsDominatedBy(eps1 * nu1, nu) then
                    nu2eps2 := nu - eps1 * nu1;
                    nu2, eps2 := FunDomainRep(M, nu2eps2);
                    Append(~MPairs_bb[nu], [<nu1, eps1>, <nu2, eps2>]);
                end if;
            end for;
        end for;
    end for;
    return MPairs_bb;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Deprecated? Conversion idl<->rep      //
//                                               //
///////////////////////////////////////////////////

 intrinsic IdealToRep(M::ModFrmHilDGRng) -> Assoc
  {getter}
  return M`IdealToRep;
end intrinsic;

intrinsic RepToIdeal(M::ModFrmHilDGRng) -> Assoc
  {getter}
  return M`RepToIdeal;
end intrinsic;

intrinsic IdealToRep(M::ModFrmHilDGRng, nn::RngOrdIdl) -> FldNumElt
  {
    inputs: 
      M: A graded ring of Hilbert modular forms
      nn: A integral ideal of the base field of M
      bb: A narrow class representative
    returns:
      An totally positive element nu in the fundamental domain 
      corresponding to the ideal nn.
  }

  if IsZero(nn) then 
    return BaseField(M)!0;
  end if;

  require Norm(nn) le Precision(M) : "Beyond known precision, sorry!";

  bb := IdealToNarrowClassRep(M, nn);
  return M`IdealToRep[bb][nn];
end intrinsic;

intrinsic RepToIdeal(M::ModFrmHilDGRng, nu::FldNumElt, bb::RngOrdFracIdl) -> RngOrdIdl
  {
    inputs:
      M: A graded ring of Hilbert modular forms
      nu: A fundamental domain representative field element
      bb: A narrow class representative
    returns:
      An integral ideal nn corresponding to the representative nu on the component bb.
  }

  return M`RepToIdeal[bb][nu];
end intrinsic;

intrinsic RepIdealConversion(M::ModFrmHilDGRng) -> Assoc, Assoc
  {
    inputs:
      M: A graded ring of Hilbert modular forms
    returns:
      Two 2D associative arrays,
        - IdealToRep
        - RepToIdeal,
      which cache the conversion of nn to nu. 
      Precisely, for each nn in the ideal class 
      [bbp]^-1, the ideal nn * bbp is narrowly
      principal, and we can use FunDomainRep
      to get a totally positive generator.
      We have IdealToRep[bb][nu] = nn
      and RepToIdeal[bb][nu] = nn

      // TODO we could combine this function into
      // FunDomainRepsUpToPrec and maybe save a loop
      // or two, but because narrow principalizing
      // is probably the most expensive step anyways
      // I figured code readability/cleanliness was
      // worth more. There is a known optimization here
      // if this step is too slow though. 
  }
  
  if assigned M`IdealToRep and M`RepToIdeal then
    return M`RepToIdeal, M`IdealToRep;
  end if;

  M`IdealToRep := AssociativeArray();
  M`RepToIdeal := AssociativeArray();

  F := BaseField(M);
  ZF := Integers(M);
  dd := Different(ZF);

  for bb in NarrowClassGroupReps(M) do
    M`IdealToRep[bb] := AssociativeArray();
    M`RepToIdeal[bb] := AssociativeArray();

    // dealing with the zero ideal, which lives
    // on every component
    M`IdealToRep[bb][0*ZF] := F!0;
    M`RepToIdeal[bb][F!0] := 0*ZF;
  end for;

  for nn in IdealsUpTo(M`Precision, ZF) do
    // we've already dealt with the zero ideal
    if IsZero(nn) then
      continue;
    end if;
    bb := IdealToNarrowClassRep(M, nn);
    bbp := bb * dd^-1;
    _, nu := IsNarrowlyPrincipal(nn * bbp);
    nu, _ := FunDomainRep(M, nu : CheckComponent := bb);
    M`IdealToRep[bb][nn] := nu;
    M`RepToIdeal[bb][nu] := nn;
  end for;

  return M`RepToIdeal, M`IdealToRep;
end intrinsic;
