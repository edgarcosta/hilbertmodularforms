freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hecke operators with level structure for Indefinite Algorithm
// January 2009, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import !"Geometry/ModFrmHil/proj1.m" : residue_class_reps;
import !"Geometry/ModFrmHil/indefinite.m" : ElementOfNormMinusOne, LeftIdealGens;
import !"Algebra/AlgQuat/enumerate.m" :
             EnumerativeSearchInternal, ReducedBasisInternal;
import !"Geometry/GrpPSL2/GrpPSL2Shim/domain.m" : Vertices;
import "weight_rep.m" : GetOrMakeP1, matrix_of_action, matrix_of_induced_action, weight_rep_dim;
import "ideal_datum.m" : induced_module_mtrxs_of_gens;

declare attributes GrpPSL2 : LevelCosets_new, H1s, ShimGroupSidepairsQuats, HeckeMatrixoo_new, HardHeckeMatrices_new, P1s_dict;
declare attributes AlgQuat : NarrowClassGroup, NarrowClassGroupMap;

forward HeckeMatrix1;

//-------------
//
// Interface with fundamental domain algorithm.
//
//-------------

// Given a word rel as a product of powers of generators and inverse generators,
// InducedRelations produces a (#Generators(Gamma) x dim W_k) by dim W_k matrix
// that when multiplied by the (#Generators(Gamma) x dim W_k) length row vector
// representing a cocycle (or candidate cocycle) f, returns the dim W_k length
// row vector representing f(rel).
InducedRelation := function(rel, mtrxs_of_gens : IsTrivialCoefficientModule:=false);
  // set parameters based on an arbitrary element 
  rpa1 := mtrxs_of_gens[Rep(Keys(mtrxs_of_gens))];
  R    := BaseRing(rpa1);
  nr   := Nrows(rpa1);

  // the number of keys of mtrxs_of_gens is equal to twice the number of generators
  mats := [SparseMatrix(R, nr, nr) : i in [1..(#Keys(mtrxs_of_gens) div 2)]];
  I := IdentitySparseMatrix(R, nr);

  // if the coefficient module is trivial then
  // we can avoid some of the computation.
  if IsTrivialCoefficientModule then
    for i := 1 to #rel do
      absi := Abs(rel[i]);
      if rel[i] lt 0 then
        mats[absi] -:= I;
      else
        mats[absi] +:= I;
      end if;
    end for;
  else
    g := I;
    for i := #rel to 1 by -1 do
      absi := Abs(rel[i]);
      if rel[i] lt 0 then
        // this is because if f is a cocycle,
        // f(x^-1) = -f(x)x^-1, 
        // so the tail we multiply by has one less element than it would 
        // in the other case.
        mats[absi] -:= mtrxs_of_gens[rel[i]]*g;
        g := mtrxs_of_gens[rel[i]]*g;
      else
        mats[absi] +:= g;
        g := mtrxs_of_gens[absi]*g;
      end if;
    end for;
  end if;
  return VerticalJoin(mats), rel;
end function;

CompleteRelationFromUnit := function(X, alpha, k : IsTrivialCoefficientModule:=false);
  // this expresses alpha in terms of the generators of Gamma
  // TODO abhijitm - this may not be a problem, but I don't think these generators
  // need to agree with the generators produced by Generators(Group(Gamma)).
  // I think these come from the side pairing.
  reldata := ShimuraReduceUnit(X`FuchsianGroup!alpha);
  assert IsScalar(Quaternion(reldata[1]));
  rel := reldata[3];

  mat, rel := InducedRelation(rel, induced_module_mtrxs_of_gens(X, k)
           : IsTrivialCoefficientModule:=IsTrivialCoefficientModule);
  return mat, rel;
end function;

//-------------
//
// Cohomology module.
//
//-------------

function InducedH1Internal(X, k);
  Gamma := X`FuchsianGroup;
  if not assigned Gamma`LevelH1s then
    Gamma`H1s := AssociativeArray();
  end if;

  if IsDefined(Gamma`H1s, <X`Ideal, k, X`Character>) then
    return Explode(Gamma`H1s[<X`Ideal, k, X`Character>]);
  end if;

  U, _, m := Group(Gamma);
  d := #Generators(U);
  gammagens := [m(U.i) : i in [1..d]];

  mtrxs_of_gens := induced_module_mtrxs_of_gens(X, k);
  R := HorizontalJoin(
    [InducedRelation(Eltseq(LHS(rel)), mtrxs_of_gens) : rel in Relations(U)]);
  Z := Kernel(R);

  I := IdentitySparseMatrix(BaseRing(mtrxs_of_gens[1]), Nrows(mtrxs_of_gens[1]));
  // the keys of mtrxs_of_gens are [-t, -(t-1), .., -1, 1, ..., t],
  // and the negative keys store inverses of generators. We only want the
  // generators themselves here.
  coB := HorizontalJoin([mtrxs_of_gens[i] - I : i in [1 .. (#mtrxs_of_gens div 2)]]);
  coB := [Z!coB[i] : i in [1..Nrows(coB)]];
  ZcoB := sub<Z | coB>;

  H, mH := quo<Z | ZcoB>;

  ZB := Basis(Z);
  S := EchelonForm(Matrix(coB));
  RemoveZeroRows(~S);
  piv := [Min(Support(S[i])): i in [1..Nrows(S)]];
  assert #SequenceToSet(piv) eq #piv;
  Htilde := [ZB[i] : i in [1..#ZB] | 
                        Min(Support(ZB[i])) notin piv];
  if #Htilde gt 0 then
    mHtilde := Matrix([mH(h) : h in Htilde]);
    assert Abs(Norm(Determinant(mHtilde))) eq 1;
    Htilde := mHtilde^(-1)*Matrix(Htilde);
    Htilde := [Htilde[i] : i in [1..Nrows(Htilde)]];
  end if;

  Gamma`H1s[<X`Ideal, k, X`Character>] := <Htilde, mH>;
  return Htilde, mH;
end function;

function InducedH1(X, Xp, k);
  Htilde, mH := InducedH1Internal(X, k);
  Htildep, mHp := InducedH1Internal(Xp, k);

  return Htildep, mH;
end function;

//-------------
//
// Utility
//
//-------------

function eichlerize(alpha, X)
  // inputs:
  //   alpha::AlgAssVOrdElt - An element of a maximal order O of a quaternion algebra
  //     B/F whose discriminant D does not divide some level N
  //   X::IdealDatum
  //
  // returns: 
  //   an element beta in O_0(N) such that there is a c in X`CosetReps for which
  //   beta = c * alpha. 
  //
  // TODO abhijitm explain why it's useful, maybe copy from the comments you wrote later
  iota_alpha := X`ResidueMap(alpha);
  v := [iota_alpha[2,1], -iota_alpha[1,1]];
  _, v := X`P1Rep(v, false, false);
  c := X`CosetReps[Index(X`P1Elements, v)];
  // replace alpha with c * alpha which now lives in O_o(N)
  return c * alpha;
end function;

//-------------
//
// Main loop.
//
//-------------

FindGammas := function(Ol, Gamma : Bound := 100);
  D := Parent(Gamma`ShimFDDisc[1]);
  mU := Gamma`ShimFDSidepairsDomain;
  i := 1;
  while i lt #mU do
    if mU[i] eq mU[i+1] then
      Remove(~mU,i);
    end if;
    i +:= 1;
  end while;

  O := BaseRing(Gamma);

  frontier := [O!1];
  cosets := [O!1];
  foundgammas := [];

  while frontier ne [] and #foundgammas lt Bound do
    newfrontier := [];
    for delta in frontier do
      for g in mU do
        gamma := delta*g;

        fffound := false;
        for c in cosets do
          cgamma := c^(-1)*gamma;  
          if cgamma in Ol then
            fffound := true;
            if not IsScalar(cgamma) then
              Append(~foundgammas, cgamma);
            end if;
            break c;
          end if;
        end for;
        if not fffound and gamma notin newfrontier then
          Append(~cosets, gamma);
          Append(~newfrontier, gamma);
        end if;
      end for;
    end for;
    frontier := newfrontier;
  end while;

  return foundgammas, cosets;
end function;

intrinsic HeckeMatrix2(Gamma::GrpPSL2, N, ell, weight, chi : UseAtkinLehner := false) -> AlgMatElt
  {Computes the matrix of the Hecke operator T_ell acting on H^1 of the 
   induced module from level N.}

  O := Gamma`BaseRing;
  B := Algebra(O);
  F := BaseRing(B);

  Z_F := MaximalOrder(F);

  FeqQQ := F cmpeq Rationals();
  elleqoo := ell cmpeq "Infinity";

  if not assigned Gamma`HeckeMatrixoo_new then
    Gamma`HeckeMatrixoo_new := AssociativeArray();
  end if;

  if not assigned Gamma`HardHeckeMatrices_new then
    Gamma`HardHeckeMatrices_new := AssociativeArray();
  end if;

  if elleqoo and IsDefined(Gamma`HeckeMatrixoo_new, <N, weight, chi>) then
    vprint ModFrmHil, 2: "Recalling saved matrix! ...... ";
    return Gamma`HeckeMatrixoo_new[<N, weight, chi>];
  elif (not elleqoo) and IsDefined(
      Gamma`HardHeckeMatrices_new, <N, weight, chi, ell, UseAtkinLehner>) then
    vprint ModFrmHil, 2: "Recalling saved matrix! ...... ";
    return Gamma`HardHeckeMatrices_new[<N, weight, chi, ell, UseAtkinLehner>];
  end if;
    
  require not UseAtkinLehner or Valuation(Discriminant(O)*N, ell) gt 0 :
    "Atkin-Lehner involution only applies when ell divides D*N";
  if not elleqoo and Valuation(Discriminant(B),ell) gt 0 then
    require UseAtkinLehner : 
      "Hecke operator not defined when ell divides D; use Atkin-Lehner operator instead";
  end if;

  if not assigned B`NarrowClassGroup then
    vprintf ModFrmHil: "Computing narrow class group of F .................... ";
    vtime ModFrmHil:
    ClF, mClF := NarrowClassGroup(Z_F);

    B`NarrowClassGroup := ClF;
    B`NarrowClassGroupMap := mClF;
  else
    ClF := B`NarrowClassGroup;
    mClF := B`NarrowClassGroupMap;
  end if;

  if not assigned Gamma`ShimFDSidepairsDomain then
    vprintf ModFrmHil: "Computing group structure (fundamental domain) ....... \n";
    vtime ModFrmHil:
    _ := Group(Gamma);
  end if;

  if not assigned O`RightIdealClasses or &or[not assigned Ol`FuchsianGroup : Ol in O`RightIdealClasses[1][3]] then
    vprintf ModFrmHil: "Computing ideal classes, orders, and groups .......... \n";
    time0 := Cputime();
    
    IndentPush();

    if FeqQQ then
      O`RightIdealClasses := [* [* [1*Integers()], [rideal<O | 1>], [O], true *] *]; 
    else
      _ := RightIdealClasses(O : Strict := true);
    end if;
    leftOrders := O`RightIdealClasses[1][3];

    D := Parent(Gamma`ShimFDDisc[1]);

    for ilo := 2 to #leftOrders do 
      vprintf ModFrmHil: "Computing group (fd) for right ideal class %o ..... \n", ilo;

      time1 := Cputime();
      
      Ol := leftOrders[ilo];
      if Ol eq leftOrders[ilo-1] then
        Ol`FuchsianGroup := leftOrders[ilo-1]`FuchsianGroup;
        vprint ModFrmHil: "same!";
        continue;
      end if;

      Gammal := FuchsianGroup(Ol : TotallyPositive := true);

      foundgammas := FindGammas(Ol, Gamma);
      foundgammas := foundgammas[1..Min(#foundgammas,200)];
      _ := FundamentalDomain(Gammal, D : StartDomain := foundgammas);
      _ := Group(Gammal);

      vprintf ModFrmHil: "Time: %o \n", Cputime(time1);
    end for;

    IndentPop();
    vprint ModFrmHil: "Time:", Cputime(time0);
  end if;

  if FeqQQ then
    ClFelts := [ClF!0];
  else
    ClFelts := [Norm(Is[i])@@mClF : i in [1..#Is]] where Is := O`RightIdealClasses[1][2];
  end if;

  rids := O`RightIdealClasses[1];
  assert rids[4];

  ridsbasis := 0;
  if elleqoo then
    fakell := 1*Z_F;
  else
    fakell := ell;
  end if;

  for kk := #O`RightIdealClasses to 1 by -1 do
    if &and[Gcd(Integers()!Norm(O`RightIdealClasses[kk][1][i]),Integers()!Norm(N)) eq 1 : i in [1..#ClFelts]] then
      ridsbasis := kk;
      break kk;
    end if;
  end for;

  if ridsbasis ne 0 then
    vprintf ModFrmHil, 3: "Using ridsbasis %o...\n", ridsbasis;
  else
    // none of the existing ridsbases are coprime to the level,
    // so we need to compute a new one
    function newIdealClassRep(J, Gamma);
      Jinv := LeftInverse(J);
      ZBJ := ZBasis(Jinv);

      D := Parent(Gamma`ShimFDDisc[1]);
      S := RealPlaces(F);
      NJ := Norm(J);
      Lbasis, L := ReducedBasisInternal(ZBJ, B : q0 := D!0);
      m := 0;
      SVP := ShortVectorsProcess(L, 1);
      while true do
        v := NextVector(SVP);
        if IsZero(v) then
          m +:= 1;
          SVP := ShortVectorsProcess(L, m, (m+1));
          continue;
        end if;
        delta := &+[Round(v[i])*ZBJ[i] : i in [1..4*Degree(F)]];
        if Gcd(Integers()!Norm(Norm(delta)*NJ),Integers()!Norm(fakell*N)) eq 1 and IsTotallyPositive(Norm(delta)) then
          return delta*J, delta;
        end if;
      end while;
    end function;

    vprintf ModFrmHil: "Ideal class representative not coprime to ell, recomputing using 1... \n";

    ridsold := O`RightIdealClasses[1];
    for i := 1 to #ClFelts do
      Jold := ridsold[2][i];
      Oold := ridsold[3][i];
      Gammaold := Oold`FuchsianGroup;
      if i ne 1 and Gcd(Integers()!Norm(Norm(Jold)), Norm(N*fakell)) ne 1 then
        Jnew, delta := newIdealClassRep(Jold, Gammaold); 
      else
        Jnew := Jold;
        delta := Oold!1;
      end if;

      if N ne 1*Z_F then
        // Make sure delta is trivial at N prime to the index.
        Nprimefacts := [ Nfact[1]^Nfact[2] : Nfact in Factorization(N) | Valuation(Norm(Jold),Nfact[1]) eq 0];
        if #Nprimefacts ne 0 then
          Nprime := &*Nprimefacts;
          X_old := cIdealDatum(Oold`FuchsianGroup, Nprime);
          cosetsold := X_old`CosetReps;
          // TODO abhijitm - no clue why we do two inverses, but this is how it was 
          delta := eichlerize(delta^(-1), X_old)^(-1);
        end if;
      end if;

      Onew := Order([delta*x*delta^(-1) : x in ZBasis(Oold)]);
      assert Onew eq LeftOrder(Jnew);
      assert O eq RightOrder(Jnew);
      assert Gcd(Integers()!Norm(Discriminant(Onew meet O)/Discriminant(O)), Norm(N*fakell)) eq 1;
      Gammanew := FuchsianGroup(Onew);

      if assigned Oold`ElementOfNormMinusOne then
        Onew`ElementOfNormMinusOne := delta*Oold`ElementOfNormMinusOne*delta^(-1);
      end if;

      Ooldtonew := map<Oold -> Onew | x :-> Onew!(delta*x*delta^(-1)), y :-> Oold!(delta^(-1)*y*delta)>;
      domainold := Gammaold`ShimFDGens;
      domainnew := [Ooldtonew(gamma) : gamma in domainold];

      Dold := Parent(Gammaold`ShimFDDisc[1]);
      z0 := (Gammaold!delta)*Center(Dold);

      c1,r1 := IsometricCircle(Gammaold!domainold[1], Dold);
      c2,r2 := IsometricCircle(Gammaold!domainold[2], Dold);
      v0 := InternalIntersection(c1,r1,c2,r2, Dold);

      Dnew := UnitDisc( : Center := z0, Precision := Dold`prec);
      c1new,r1new := IsometricCircle(Gammanew!domainnew[1], Dnew);
      c2new,r2new := IsometricCircle(Gammanew!domainnew[2], Dnew);
      v0new := InternalIntersection(c1new,r1new,c2new,r2new, Dnew);
      
      arg := Argument(ComplexValue(v0)) - Argument(ComplexValue(v0new));
      Dnew := UnitDisc( : Center := z0, Rotation := arg, Precision := Dnew`prec);

      _ := FundamentalDomain(Gammanew, Dnew : StartDomain := domainnew, AssertDomain := true);
      _ := Group(Gammanew);

      ridsnew := ridsold;
      ridsnew[1][i] := Norm(Jnew);
      ridsnew[2][i] := Jnew;
      ridsnew[3][i] := Onew;
    end for;

    ridsnew[3][1]`pMatrixRings := <>;
    Isupport := &*ridsnew[1];
    for j := 1 to #O`RightIdealClasses do
      for pmat in O`RightIdealClasses[j][3][1]`pMatrixRings do
        existinglevels := [pmat[1] : pmat in ridsnew[3][1]`pMatrixRings];
        if pmat[1] notin existinglevels and Valuation(Isupport, pmat[1]) eq 0 then
          Append(~ridsnew[3][1]`pMatrixRings, pmat);
        end if;
      end for;
    end for;

    Append(~O`RightIdealClasses, ridsnew);
    vprintf ModFrmHil: "Added new right ideal classes, total of %o... \n", #O`RightIdealClasses;
    ridsbasis := #O`RightIdealClasses;

    inSupport := &or[O`RightIdealClasses[ridsbasis][1][i] + fakell 
                     ne 1*Z_F : i in [1..#ClFelts]];
    assert not inSupport;
  end if;

  if elleqoo then
    alpha := ElementOfNormMinusOne(O);
    t := ideal<Z_F | Norm(alpha)>@@mClF;
  elif UseAtkinLehner and ell + Discriminant(O)*N eq ell then
    t := Valuation(Discriminant(O)*N,ell)*(ell@@mClF);
  else
    t := ell@@mClF;
  end if;

  inNormSupport := Gcd(Integers()!Norm(&*O`RightIdealClasses[ridsbasis][1]), Integers()!Norm(fakell)) ne 1;

  assert inNormSupport or #O`RightIdealClasses[ridsbasis][3] eq 1 or
           &*[Discriminant(O`RightIdealClasses[ridsbasis][3][1] meet O`RightIdealClasses[ridsbasis][3][i]) : 
                                      i in [2..#O`RightIdealClasses[ridsbasis][3]]] + fakell eq 1*Z_F;
  if not elleqoo and Valuation(Discriminant(B),ell) eq 0 then
    P1ell, P1ellrep := GetOrMakeP1(Gamma, ell);

    if not inNormSupport then
      leftOrders := O`RightIdealClasses[ridsbasis][3];
      M2ell, phiell, mFell := pMatrixRing(leftOrders[1], ell);
      if Valuation(N,ell) gt 0 then
        _, iotaell := ResidueMatrixRing(leftOrders[1], ell^Valuation(N,ell));
      else
      _, iotaell := ResidueMatrixRing(leftOrders[1], ell);
      end if;
      for i := 1 to #leftOrders do
        if not assigned leftOrders[i]`pMatrixRings then
          leftOrders[i]`pMatrixRings := <>;
        end if;
        _ell := FeqQQ select Generator(ell) else ell;
        if forall{ pmat : pmat in leftOrders[i]`pMatrixRings | pmat[1] ne _ell } then
          Append(~leftOrders[i]`pMatrixRings, <_ell, M2ell, phiell, mFell>);
        end if;
        X_ell := cIdealDatum(leftOrders[i]`FuchsianGroup, ell);
        ellcosets := X_ell`CosetReps;
      end for;
    else
      iotaell := [];
    end if;
  else
    iotaell := [];
  end if;

  // Complete harmonizing pMatrixRings for level structure.
  leftOrders := O`RightIdealClasses[ridsbasis][3];
  assert N + &*O`RightIdealClasses[ridsbasis][1] eq 1*Z_F;
  for ellq in [pp[1] : pp in Factorization(N)] do
    M2ellq, phiellq, mFellq := pMatrixRing(leftOrders[1], ellq);
    for i := 1 to #leftOrders do
      if not assigned leftOrders[i]`pMatrixRings then
        leftOrders[i]`pMatrixRings := <>;
      end if;
      _ellq := FeqQQ select Generator(ellq) else ellq;
      if forall{ pmat : pmat in leftOrders[i]`pMatrixRings | pmat[1] ne _ellq } then
        Append(~leftOrders[i]`pMatrixRings, <_ellq, M2ellq, phiellq, mFellq>);
      end if;
    end for;
  end for;

  for i := 1 to #ClFelts do
    indp := Index(ClFelts, ClFelts[i]);
    ind := Index(ClFelts, ClFelts[i]+t);
    if inNormSupport then
      leftOrder := O`RightIdealClasses[ridsbasis][3][ind];
      M2ell, phiell, mFell := pMatrixRing(leftOrder, ell);
      _, iotaell := ResidueMatrixRing(leftOrder, ell);
    end if;
    Mblock := HeckeMatrix1(O, N, ell, ind, indp, ridsbasis, iotaell, weight, chi : ellAL := UseAtkinLehner);
    if Mblock cmpeq [] then
      // Zero-dimensional space!
      return Matrix(Rationals(), 0, 0, []), PolynomialRing(Rationals())!0;
    end if;
    Z := ZeroMatrix(BaseRing(Mblock), Nrows(Mblock), #ClFelts*Ncols(Mblock));
    InsertBlock(~Z, Mblock, 1, (ind-1)*Nrows(Mblock)+1);
    if i eq 1 then
      M := Z;
    else
      M := VerticalJoin(M, Z);
    end if;
  end for;

  if elleqoo then
    Gamma`HeckeMatrixoo_new[<N, weight, chi>] := M;
  elif UseAtkinLehner or (ell + Discriminant(O)/Discriminant(B)*N eq ell) then
    Gamma`HardHeckeMatrices_new[<N, weight, chi, ell, UseAtkinLehner>] := M;
  end if;

  return M, CharacteristicPolynomial(M);
end intrinsic;

HeckeMatrix1 := function(O_mother, N, ell, ind, indp, ridsbasis, iotaell, weight, chi : ellAL := false);
  // Initialization.
  Gamma_mother := O_mother`FuchsianGroup;
  assert O_mother`RightIdealClasses[ridsbasis][4];
  rids := O_mother`RightIdealClasses[ridsbasis];

  B := Algebra(O_mother);
  F := BaseRing(B);

  O := rids[3][ind];
  Op := rids[3][indp];
  Gamma := O`FuchsianGroup;
  Gammap := Op`FuchsianGroup;

  J := rids[2][ind];
  Jp := rids[2][indp];

  FeqQQ := F cmpeq Rationals();

  if FeqQQ then 
    JJp := Jp;
  else
    JJp := Jp*LeftInverse(J);
  end if;

  elleqoo := ell cmpeq "Infinity";
  ellU := not elleqoo and ell + Discriminant(O)/Discriminant(B)*N eq ell;
  inNormSupport := not elleqoo and (iotaell cmpeq [] or 
    Gcd(Integers()!Norm(ell),Integers()!Norm(rids[1][ind]*rids[1][indp])) ne 1);

  U, _, m := Group(Gamma);

  Uside := Gamma`ShimGroupSidepairs;
  mside := Gamma`ShimGroupSidepairsMap;
  n := #Generators(U);
  lifts := [m(U.i) : i in [1..n]];

  IsLevelOne := Norm(N) eq 1;

  // Check or precompute level structure.
  Gamma_datum := cIdealDatum(Gamma, N : chi:=chi);
  Gammap_datum := cIdealDatum(Gammap, N : chi:=chi);
  cosets := Gamma_datum`CosetReps;
  cosetsp := Gammap_datum`CosetReps;

  D := Parent(Gamma`ShimFDDisc[1]); 

  // There are two methods to compute the Hecke operator.
  // One works in the situation when ell is coprime to N and the support of the
  // right ideal classes; it runs zippily.
  // In the other situations, one must "work hard", which means unpacking 
  // Shapiro's lemma and dealing with many issues of normalizations.

  // If ell = oo, we need to decide if we have to work hard or not.
  if elleqoo then
    P1ell := [Infinity()];
    numP1 := 1;
    ellcosets := [B!1];

    if FeqQQ then
      alphap := ElementOfNormMinusOne(O);
    else
      _, alphap := IsPrincipal(JJp, Gammap : Strict := false);
      if not (-1 in RealSigns(Norm(alphap))) then
        assert ind eq indp;
        alphap := ElementOfNormMinusOne(O);
        assert alphap in O and IsUnit(IntegerRing(Gammap_datum)!Norm(alphap)) and
               -1 in RealSigns(Norm(alphap));
      end if;
    end if;

    alphap := eichlerize(alphap, Gammap_datum);

    lambda := alphap;
    alphas := [lambda];
    NNlambda := Norm(Norm(lambda));
    NNlambda := Numerator(NNlambda)*Denominator(NNlambda);

    ooinNormSupport := Gcd(NNlambda,Integers()!Norm(rids[1][ind]*rids[1][indp])) ne 1;
  else
    ooinNormSupport := false;
  end if;

  // Catch the cases where we work hard:
  // (1) ell = oo and the representative element of negative norm is not coprime;
  // (2) ell divides N (but not ell divides D)--this includes the Hecke operator case
  //     ellU and the Atkin-Lehner case ellAL.
  if (elleqoo and ooinNormSupport) or (ellAL and Valuation(N,ell) gt 0) or ellU then
    if elleqoo then
      numP1 := 1;
    elif ellAL then
      numP1 := 1;
    elif ellU then
      numP1 := Norm(ell);
    end if;

    // Work from the definition to find lambdas.
    // If ell = oo, we already have lambda.  
    if ellAL then
      ee := Valuation(Discriminant(O)*N, ell);
      lambda := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell : Slow := true, ALval := ee)[1];

      alphas := [];
      _, iotapNell := ResidueMatrixRing(O, N/ell^ee);
      iotap := Gammap_datum`ResidueMap;
      for c := 1 to #cosetsp do
        if Valuation(iotap(cosetsp[c]*lambda)[2,1],ell) ge ee and
           Valuation(iotap(cosetsp[c]*lambda)[2,2],ell) ge ee and
           iotapNell(cosetsp[c]*lambda)[2,1] in N/ell^ee then
          Append(~alphas, cosetsp[c]*lambda);
        end if;
      end for;
      assert #alphas eq 1;
    elif ellU then
      X_ell_full := cIdealDatum(Gamma, ell);
      ellcosetsfull := X_ell_full`CosetReps;
      ooind := 1;
      P1ellfull := X_ell_full`P1Elements;
      while ooind le #P1ellfull do
        if Valuation(P1ellfull[ooind][1],ell) gt 0 then // Should be infinity, in fact!
          break;
        end if;
      end while;
      P1ell := [P1ellfull[c] : c in [1..#P1ellfull] | c ne ooind];
      ellcosets := [ellcosetsfull[c] : c in [1..#P1ellfull] | c ne ooind];

      lambda := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell);
      
      // alphas will ultimately store the elements alpha_j such that
      // Gamma lambda Gamma = \sqcup Gamma alpha_j.
      //
      // alphas_og is the initial assignment, computed as 
      // alpha_j = lambda * gamma_j where gamma_j are the cosets 
      // of Gamma(l) \ Gamma(1). However, these alpha_j need not
      // be in O_o(N), and this is something we want. Thus, we multiply
      // on the left by appropriate coset representatives of Gamma(N) \ Gamma(1)
      // in order to obtain our final alphas.
      alphas := [lambda*ellcosets[c] : c in [1..numP1]];
      alphas := [eichlerize(alpha, Gammap_datum) : alpha in alphas];
    end if;

    Y_U := [];
    W_dim := weight_rep_dim(weight);

    vprintf ModFrmHil: "Computing operator the hard way ...................... ";
    vtime ModFrmHil:

    for i in [1..n] do
      G := [];
      for k in [1..#cosets] do
        Gk := [];
        alpha := lifts[i] * cosets[k]^(-1);
        liftsik := O!eichlerize(alpha, Gamma_datum);
        Y_Opi := [];

        for j in [1..numP1] do
          if elleqoo or ellAL then
            c := 1;
          else
            iotadelta := iotaell(alphas[j]*liftsik);
            bl, v := X_ell_full`P1Rep(iotadelta[1], false, false);
            c := Index(P1ell, v);
          end if;
          y := Op!(alphas[j]*liftsik*alphas[c]^(-1));
          y, _ := CompleteRelationFromUnit(Gammap_datum, y, weight : IsTrivialCoefficientModule := false);
          y := ColumnSubmatrix(y, 1, W_dim);
          y := y * matrix_of_action(alphas[c], weight, Gammap_datum);
          Append(~Gk, y);
        end for;

        Append(~G, Gk);
      end for;
      Append(~Y_U, G);
    end for;

    Htilde, mH := InducedH1(Gamma_datum, Gammap_datum, weight);

    if #Htilde eq 0 then
      return [];
    else
      M := HorizontalJoin([ HorizontalJoin([ &+[ Y_U[i][k][j] : j in [1..numP1]] : k in [1..#cosets]]) : i in [1..n] ]);
      MH := Matrix(Htilde)*M;
      if &and[MH[i] in Domain(mH) : i in [1..#Htilde]] then
        MM := Matrix([mH(MH[i]) : i in [1..#Htilde]]);
        return MM;
      else
        error "!?!?!?!?!?  This is a serious error; please report.";
      end if;
    end if;
  end if;

  // We've ruled out some "work hard" cases; we'll try to use as much optimization as possible.
  // We still have to do some extra computing if ell is in the support of the ideal classes.
  // First, if ell <> oo, we need to get our lambdas.
  if not elleqoo then
    if ellAL then
      numP1 := 1;
    else
      numP1 := Norm(ell)+1;
    end if;

    if ellAL or inNormSupport then
      if ellAL then
        // We've covered the case when ell divides N, so this is only the case ell divides D;
        // hence ell exactly divides D.

        // lambdas has length 1
        lambdas := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell : Slow := true, ALval := 1);
      elif inNormSupport then
        // lambdas has length numP1
        lambdas := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell : Slow := true);
      end if;

      // Ensure lambda is trivial at N.
      if not IsLevelOne then
        alphas := [eichlerize(lambda, Gammap_datum)
                : lambda in lambdas];
      else
        alphas := lambdas;
      end if;
    else // Go for the fast code.
      lambda := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell);
      X_ell := cIdealDatum(Gamma, ell);
      P1ell := X_ell`P1Elements;
      P1ellrep := X_ell`P1Rep;
      ellcosets := X_ell`CosetReps;

      // Ensure lambda is trivial at N.
      if not IsLevelOne then
        alphas := [eichlerize(lambda * ellcoset, Gammap_datum)
               : ellcoset in ellcosets];
      else
        alphas := [lambda * ellcoset : ellcoset in ellcosets];
      end if;
    end if;
  end if;


  vprintf ModFrmHil: "Computing conjugation actions ........................ ";
  vtime ModFrmHil:
  if not IsLevelOne then
    Zp := [matrix_of_induced_action(alpha, weight, Gamma_datum) : alpha in alphas];
  end if;


  Y_Op := [];
  X := [];
  vprintf ModFrmHil: "Defining maps for relations from units ............... ";
  vtime ModFrmHil:
  for i in [1..n] do
    Y_Opi := [];
    Xi := [];
    if elleqoo then
      Append(~Xi, 1);
      Append(~Y_Opi, Op!(lambda*lifts[i]*lambda^(-1)));
    else
      if inNormSupport then
        // Work hard
        for j in [1..#alphas] do
          for c in [1..#alphas] do
            if alphas[j]*lifts[i]*(alphas[c])^(-1) in Op then
              Append(~Xi, c);
              Append(~Y_Opi, Op!(alphas[j]*lifts[i]*alphas[c]^(-1)));
              break c;
            end if;
          end for;
        end for;
      else
        for j in [1..numP1] do
          iotadelta := iotaell(ellcosets[j]*lifts[i]);
          _, v := P1ellrep(iotadelta[2], false, false);
          c := Index(P1ell, v);
          Append(~Xi, c);
          Append(~Y_Opi, Op!(alphas[j] * lifts[i] * alphas[c]^(-1)));
        end for;
      end if;
    end if;
    Append(~X, Xi);
    Append(~Y_Op, Y_Opi);
  end for;


  Y_U := [];
  vprintf ModFrmHil: "Reducing %4o units of Gamma ......................... ", n*numP1;
  vtime ModFrmHil:
  for i in [1..n] do
    G := [];

    for j in [1..numP1] do
      y := CompleteRelationFromUnit(Gammap_datum, Y_Op[i][j], weight : IsTrivialCoefficientModule := IsLevelOne);
      if not IsLevelOne then
        y := y*Zp[X[i][j]];
      end if;
      Append(~G, y);
    end for;
    Append(~Y_U, G);
  end for;


  vprintf ModFrmHil: "Computing H1 (coinduced) ............................. ";
  vtime ModFrmHil:
  Htilde, mH := InducedH1(Gamma_datum, Gammap_datum, weight);
  
  if #Htilde eq 0 then
    return [];
  else
    M := HorizontalJoin([ &+[ Y_U[i][j] : j in [1..numP1]] : i in [1..n] ]);
    MH := Matrix(Htilde)*M;
    MM := Matrix([mH(MH[i]) : i in [1..#Htilde]]);
    return MM;
  end if;
end function;
