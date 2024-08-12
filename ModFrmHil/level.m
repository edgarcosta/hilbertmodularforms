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
import "weight_rep.m" : GetOrMakeP1, Gamma0Cosets, RightPermutationActions;
import "hecke.m" : pseudo_inverse;

declare attributes GrpPSL2 : LevelCosets_new, LevelRPAs_new, LevelCPAs_new, LevelH1s, ShimGroupSidepairsQuats, HeckeMatrixoo, HardHeckeMatrices, P1s_dict;
declare attributes AlgQuat : NarrowClassGroup, NarrowClassGroupMap;

forward HeckeMatrix1;

//-------------
//
// Right action functions.
//
//-------------

ConjugationPermutationActions := function(Gamma, N, Z_FN, iota, P1N, cosets, P1Nrep);
  if not assigned Gamma`LevelCPAs_new then
    Gamma`LevelCPAs_new := AssociativeArray();
  end if;

  if IsDefined(Gamma`LevelCPAs_new, N) then
    return Explode(Gamma`LevelCPAs_new[N]);
  end if;

  Z_F := BaseRing(BaseRing(Gamma));
  bas, n_seq := residue_class_reps(N);
  Rset:=[[s[m]: m in [1..#s]]: s in Set(CartesianProduct(<[0..n_seq[l]-1]: l in [1..#n_seq]>))];

  iotaalphavs := [];
  for alphai in cosets do
    _, v := P1Nrep(iota(alphai)[2], false, false);
    Append(~iotaalphavs, [Z_F!t : t in Eltseq(v)]);
  end for;

  qcnt := 0;
  CPAs1bas := [];
  for q in bas do
    qcnt +:= 1;
    perm := [];
    for w in iotaalphavs do
      _, v := P1Nrep([w[1], w[1]*q + w[2]], false, false);
      Append(~perm, Index(P1N, v));
    end for;
    perm := SymmetricGroup(#cosets)!perm;
    Append(~CPAs1bas, perm);
  end for;

  Z_FNstar, mZ_FNstar := UnitGroup(Z_FN);
  basmult := [Z_F!mZ_FNstar(Z_FNstar.i) : i in [1..#Generators(Z_FNstar)]];
  qcnt := 0;
  CPAs2bas := [];
  for q in basmult do
    qcnt +:= 1;
    perm := [];
    for w in iotaalphavs do
      _, v := P1Nrep([w[1], q*w[2]], false, false);
      Append(~perm, Index(P1N, v));
    end for;
    perm := SymmetricGroup(#cosets)!perm;
    Append(~CPAs2bas, perm);
  end for;
  
  Q1 := [Z_FN!x : x in Rset];
  CPAs1 := [];
  for i := 1 to #Rset do
    perm := &*[CPAs1bas[j]^Rset[i][j] : j in [1..#CPAs1bas]];
    Append(~CPAs1, perm);
  end for;
  ChangeUniverse(~Q1, Z_FN);

  Q2 := [];
  CPAs2 := [];
  for i := 1 to #Rset do
    z := Z_FN!Rset[i];
    if IsUnit(z) then
      perm := &*[CPAs2bas[j]^zseq[j] : j in [1..#CPAs2bas]] where zseq is Eltseq(z@@mZ_FNstar);
      Append(~CPAs2, perm);
      Append(~Q2, z);
    end if;
  end for;

  Gamma`LevelCPAs_new[N] := <Q1, CPAs1, Q2, CPAs2>;
  return Q1, CPAs1, Q2, CPAs2;
end function;

//-------------
//
// Interface with fundamental domain algorithm.
//
//-------------

InducedRelation := function(rel, RPAs, RPAsinv : IsTrivialCoefficientModule:=false);
  rpa1 := RPAs[1];
  R    := BaseRing(rpa1);
  nr   := Nrows(rpa1);
  mats := [SparseMatrix(R, nr, nr) : i in [1..#RPAs]];

  I := IdentitySparseMatrix(R, nr);

  // if the coefficient module is trivial then
  // we can avoid some of the computation.
  //
  // TODO - abhijitm we probably also shouldn't be calling
  // InducedRelation in the first place if the coefficient module 
  // is trivial... but this function is going to disappear soon
  // anyways so I think it's not worth optimizing. 
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
        mats[absi] -:= RPAsinv[absi]*g;
        g := RPAsinv[absi]*g;
      else
        mats[absi] +:= g;
        g := RPAs[absi]*g;
      end if;
    end for;
  end if;
  return VerticalJoin(mats), rel;
end function;

CompleteRelationFromUnit := function(Gamma, alpha, RPAs, RPAsinv : IsTrivialCoefficientModule:=false);
  // this expresses alpha in terms of the generators of Gamma
  // TODO abhijitm - this may not be a problem, but I don't think these generators
  // need to agree with the generators produced by Generators(Group(Gamma)).
  // I think these come from the side pairing.
  reldata := ShimuraReduceUnit(Gamma!alpha);
  assert IsScalar(Quaternion(reldata[1]));
  rel := reldata[3];

  mat, rel := InducedRelation(rel, RPAs, RPAsinv : IsTrivialCoefficientModule:=IsTrivialCoefficientModule);
  return mat, rel;
end function;

//-------------
//
// Cohomology module.
//
//-------------

function InducedH1Internal(Gamma, N, cosets, RPAs, RPAsinv);
  if assigned Gamma`LevelH1s then
    for H1 in Gamma`LevelH1s do
      if H1[1] eq N then
        return H1[2], H1[3];
      end if;
    end for;
  end if;

  U, m := Group(Gamma);
  d := #Generators(U);
  gammagens := [Quaternion(m(U.i)) : i in [1..d]];

  R := HorizontalJoin(
    [InducedRelation(Eltseq(LHS(rel)), RPAs, RPAsinv) : rel in Relations(U)]);
  Z := Kernel(R);

  I := IdentitySparseMatrix(BaseRing(RPAs[1]), Nrows(RPAs[1]));
  coB := HorizontalJoin([r - I : r in RPAs]);
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
    assert Abs(Determinant(mHtilde)) eq 1;
    Htilde := mHtilde^(-1)*Matrix(Htilde);
    Htilde := [Htilde[i] : i in [1..Nrows(Htilde)]];
  end if;

  if assigned Gamma`LevelH1s then
    Append(~Gamma`LevelH1s, <N, Htilde, mH>);
  else
    Gamma`LevelH1s := <<N, Htilde, mH>>;
  end if;

  return Htilde, mH;
end function;

function InducedH1(Gamma, Gammap, N, cosets, cosetsp, RPAs, RPAsinv, RPAsp, RPAspinv);
  Htilde, mH := InducedH1Internal(Gamma, N, cosets, RPAs, RPAsinv);
  Htildep, mHp := InducedH1Internal(Gammap, N, cosetsp, RPAsp, RPAspinv);

  return Htildep, mH;
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

intrinsic HeckeMatrix2(Gamma::GrpPSL2, N, ell : UseAtkinLehner := false) -> AlgMatElt
  {Computes the matrix of the Hecke operator T_ell acting on H^1 of the 
   induced module from level N.}

  O := Gamma`BaseRing;
  B := Algebra(O);
  F := BaseRing(B);
  Z_F := MaximalOrder(F);
  FeqQQ := F cmpeq Rationals();

  elleqoo := ell cmpeq "Infinity";

  if elleqoo and assigned Gamma`HeckeMatrixoo then 
    for t in Gamma`HeckeMatrixoo do
      if t[1] eq N then
        vprint ModFrmHil, 2: "Recalling saved matrix! ...... ";
        return t[2];
      end if;
    end for;
  end if;

  if not elleqoo and assigned Gamma`HardHeckeMatrices then
    for t in Gamma`HardHeckeMatrices do
      if t[1] eq N and t[2] eq ell and t[3] eq UseAtkinLehner then
        vprint ModFrmHil, 2: "Recalling saved matrix! ...... ";
        return t[4];
      end if;
    end for;
  end if;

  require not UseAtkinLehner or Valuation(Discriminant(O)*N, ell) gt 0 :
    "Atkin-Lehner involution only applies when ell divides D*N";
  if not elleqoo and Valuation(Discriminant(B),ell) gt 0 then
    require UseAtkinLehner : 
      "Hecke operator not defined when ell divides D; use Atkin-Lehner operator instead";
  end if;

  P1N, P1Nrep := GetOrMakeP1(Gamma, N);

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

  Z_FN := quo<Z_F | N>;
  _, iota := ResidueMatrixRing(O, N);
  cosets := Gamma0Cosets(Gamma, N, Z_FN, iota, P1N, P1Nrep);

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

      alpha := ElementOfNormMinusOne(Ol);
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
  end if;

  if ridsbasis eq 0 then 
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

    ridsoldnum := 1;

    ridsold := O`RightIdealClasses[ridsoldnum];
    ridsnew := ridsold;

    vprintf ModFrmHil: "Ideal class representative not coprime to ell, recomputing using %o... \n", ridsoldnum;
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
          _, iotaold := ResidueMatrixRing(Oold, Nprime);
          P1Nprime, P1Nprimerep := GetOrMakeP1(Gamma, Nprime);
          Z_FNprime := quo<Z_F | Nprime>;
          cosetsold := Gamma0Cosets(Oold`FuchsianGroup, Nprime, Z_FNprime, iotaold, P1Nprime, P1Nprimerep);
          iotadelta := iotaold(delta^(-1));
          v := [iotadelta[2,1], -iotadelta[1,1]];
          _, v := P1Nprimerep(v, false, false);
          c := cosetsold[Index(P1Nprime, v)];
          delta := delta*c^(-1);
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
    Z_Fell := quo<Z_F | ell>;

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
        ellcosets := Gamma0Cosets(leftOrders[i]`FuchsianGroup, ell, Z_Fell, iotaell, P1ell, P1ellrep);
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
    P1ellq, P1ellqrep := GetOrMakeP1(Gamma, ellq);
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

  for i := 1 to #leftOrders do
    Ol := leftOrders[i];
    _, iota := ResidueMatrixRing(Ol, N);
    cosets := Gamma0Cosets(Ol`FuchsianGroup, N, Z_FN, iota, P1N, P1Nrep);
  end for;

  for i := 1 to #ClFelts do
    indp := Index(ClFelts, ClFelts[i]);
    ind := Index(ClFelts, ClFelts[i]+t);
    if inNormSupport then
      leftOrder := O`RightIdealClasses[ridsbasis][3][ind];
      M2ell, phiell, mFell := pMatrixRing(leftOrder, ell);
      _, iotaell := ResidueMatrixRing(leftOrder, ell);
    end if;
    Mblock := HeckeMatrix1(O, N, ell, ind, indp, ridsbasis, iotaell : ellAL := UseAtkinLehner);
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
    if not assigned Gamma`HeckeMatrixoo then
      Gamma`HeckeMatrixoo := [* *];
    end if;
    Append(~Gamma`HeckeMatrixoo, <N, M>);
  elif UseAtkinLehner or (ell + Discriminant(O)/Discriminant(B)*N eq ell) then
    if not assigned Gamma`HardHeckeMatrices then
      Gamma`HardHeckeMatrices := [* *];
    end if;
    Append(~Gamma`HardHeckeMatrices, <N, ell, UseAtkinLehner, M>);
  end if;

  return M, CharacteristicPolynomial(M);
end intrinsic;

HeckeMatrix1 := function(O_mother, N, ell, ind, indp, ridsbasis, iotaell : ellAL := false);
  // Initialization.
  Gamma_mother := O_mother`FuchsianGroup;
  assert O_mother`RightIdealClasses[ridsbasis][4];
  rids := O_mother`RightIdealClasses[ridsbasis];

// GetMemoryUsage(); MemProfile();

  P1N, P1Nrep := GetOrMakeP1(Gamma_mother, N);

  B := Algebra(O_mother);
  F := BaseRing(B);
  Z_F := MaximalOrder(F);
  Z_FN := quo<Z_F | N>;

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
  _, iota := ResidueMatrixRing(O, N);
  _, iotap := ResidueMatrixRing(Op, N);
  Z_FN := quo<Z_F | N>;

  cosets := Gamma0Cosets(Gamma, N, Z_FN, iota, P1N, P1Nrep);
  cosetsp := Gamma0Cosets(Gammap, N, Z_FN, iotap, P1N, P1Nrep);

  RPAs, RPAsinv := RightPermutationActions(Gamma, N, Z_FN, iota, P1N, cosets, P1Nrep);
  RPAsp, RPAspinv := RightPermutationActions(Gammap, N, Z_FN, iotap, P1N, cosetsp, P1Nrep);

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
    end if;

    if not FeqQQ and not -1 in RealSigns(Norm(alphap)) then
      assert ind eq indp;
      alphap := ElementOfNormMinusOne(O);
      assert alphap in O and IsUnit(Z_F!Norm(alphap)) and
             -1 in RealSigns(Norm(alphap));
    end if;

    // Ensure alpha is trivial at N.
    iotaalphap := iotap(alphap);
    v := [iotaalphap[2,1], -iotaalphap[1,1]];
    if not IsLevelOne then
      _, v := P1Nrep(v, false, false);
      c := cosetsp[Index(P1N, v)];
      alphap := c*alphap;
    end if;

    lambda := alphap;
    lambdas := [lambda];
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

      lambdas := [];
      _, iotapNell := ResidueMatrixRing(O, N/ell^ee);
      for c := 1 to #cosetsp do
        if Valuation(iotap(cosetsp[c]*lambda)[2,1],ell) ge ee and
           Valuation(iotap(cosetsp[c]*lambda)[2,2],ell) ge ee and
           iotapNell(cosetsp[c]*lambda)[2,1] in N/ell^ee then
          Append(~lambdas, cosetsp[c]*lambda);
        end if;
      end for;
      assert #lambdas eq 1;
    elif ellU then
      Z_Fell := quo<Z_F | ell>;
      P1ellfull, P1ellfullrep := GetOrMakeP1(Gamma_mother, ell);
      ellcosetsfull := Gamma0Cosets(Gamma, ell, Z_Fell, iotaell, P1ellfull, P1ellfullrep);
      ooind := 1;
      while ooind le #P1ellfull do
        if Valuation(P1ellfull[ooind][1],ell) gt 0 then // Should be infinity, in fact!
          break;
        end if;
      end while;
      P1ell := [P1ellfull[c] : c in [1..#P1ellfull] | c ne ooind];
      ellcosets := [ellcosetsfull[c] : c in [1..#P1ellfull] | c ne ooind];

      lambda := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell);
      lambdas := [lambda*ellcosets[c] : c in [1..numP1]];

      for i := 1 to #lambdas do
        lambdap := lambdas[i];
        iotalambdap := iotap(lambdap);
        v := [iotalambdap[2,1], -iotalambdap[1,1]];
        _, v := P1Nrep(v, false, false);
        c := cosetsp[Index(P1N, v)];
        lambdas[i] := c*lambdas[i];
      end for;
    end if;

    Y_U := [];

// GetMemoryUsage(); MemProfile();

    vprintf ModFrmHil: "Computing operator the hard way ...................... ";
    vtime ModFrmHil:

    for i in [1..n] do
      G := [];
      for k in [1..#cosets] do
        Gk := [];
        iotalik := iota(lifts[i]*cosets[k]^(-1));
        v := [iotalik[2,1], -iotalik[1,1]];
        _, v := P1Nrep(v, false, false);
        ci := Index(P1N, v);
        liftsik := O!(cosets[ci]*lifts[i]*cosets[k]^(-1));
        Y_Opi := [];

        for j in [1..numP1] do
          if elleqoo or ellAL then
            c := 1;
          else
            iotadelta := iotaell(lambdas[j]*liftsik);
            bl, v := P1ellfullrep(iotadelta[1], false, false);
            c := Index(P1ell, v);
          end if;
          y := Op!(lambdas[j]*liftsik*lambdas[c]^(-1));
          y,rel := CompleteRelationFromUnit(Gammap, y, RPAsp, RPAspinv : IsTrivialCoefficientModule := false);
          Append(~Gk, y);
        end for;

        Append(~G, Gk);
      end for;
      Append(~Y_U, G);
    end for;

    Htilde, mH := InducedH1(Gamma, Gammap, N, cosets, cosetsp, RPAs, RPAsinv, RPAsp, RPAspinv);

    if #Htilde eq 0 then
      return [];
    else
      // There is some normalization issue that I'm missing.  It should work just taking the 
      // first column submatrix, but fails in some isolated cases.  Shapiro's lemma
      // works acceptably for any choice of constant element, so once we find one that 
      // works, we should be OK...
      for t := 1 to Ncols(Y_U[1][1][1]) do 
        M := HorizontalJoin([ HorizontalJoin([ &+[ ColumnSubmatrix(Y_U[i][k][j],t,1) : j in [1..numP1]] : k in [1..#cosets]]) : i in [1..n] ]);
        MH := Matrix(Htilde)*M;
        if &and[MH[i] in Domain(mH) : i in [1..#Htilde]] then
          MM := Matrix([mH(MH[i]) : i in [1..#Htilde]]);
          return MM;
        end if;
      end for;
      error "No column submatrix worked!?  This is a serious error; please report.";
    end if;
  end if;

// GetMemoryUsage(); MemProfile();

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
        lambdas := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell : Slow := true, ALval := 1);
      elif inNormSupport then
        lambdas := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell : Slow := true);
      end if;

      // Ensure lambda is trivial at N.
      if not IsLevelOne then
        for i := 1 to #lambdas do
          lambdap := lambdas[i];
          iotalambdap := iotap(lambdap);
          v := [iotalambdap[2,1], -iotalambdap[1,1]];
          _, v := P1Nrep(v, false, false);
          c := cosetsp[Index(P1N, v)];
          lambdas[i] := c*lambdas[i];
        end for;
      end if;
    else // Go for the fast code.
      lambda := LeftIdealGens(Gamma, ell, JJp, 1, O, Op, iotaell);
      P1ell, P1ellrep := GetOrMakeP1(Gamma_mother, ell);
      Z_Fell := quo<Z_F | ell>;
      ellcosets := Gamma0Cosets(Gamma, ell, Z_Fell, iotaell, P1ell, P1ellrep);

      // Ensure lambda is trivial at N.
      if not IsLevelOne then
        levelmults := [];
        for i := 1 to #ellcosets do
          lambdap := lambda*ellcosets[i];
          iotalambdap := iotap(lambdap);
          v := [iotalambdap[2,1], -iotalambdap[1,1]];
          _, v := P1Nrep(v, false, false);
          c := cosetsp[Index(P1N, v)];
          Append(~levelmults, c);
        end for;
      else
        levelmults := [Op!1 : i in [1..#ellcosets]];
      end if;
    end if;
  else
    levelmults := [Op!1];
  end if;

// GetMemoryUsage(); MemProfile();

  vprintf ModFrmHil: "Computing conjugation actions ........................ ";
  vtime ModFrmHil:
  if not IsLevelOne then
    Q1, CPAs1, Q2, CPAs2 := ConjugationPermutationActions(Gammap, N, Z_FN, iotap, P1N, cosetsp, P1Nrep);

    Zp := [];
    for j in [1..numP1] do
      if inNormSupport then 
        iotaj := iotap(lambdas[j]);
      else
        iotaj := iotap(levelmults[j]*lambda*ellcosets[j]);
      end if;
      xinv := (Z_FN!iotaj[1,1])^(-1);
      perm1 := CPAs1[Index(Q1, Z_FN!iotaj[1,2]*xinv)];
      perm2 := CPAs2[Index(Q2, Z_FN!iotaj[2,2]*xinv)];
      Append(~Zp, PermutationSparseMatrix(Integers(), perm2 * perm1));
    end for;
  end if;

// GetMemoryUsage(); MemProfile();

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
        for j in [1..#lambdas] do
          for c in [1..#lambdas] do
            if lambdas[j]*lifts[i]*(lambdas[c])^(-1) in Op then
              Append(~Xi, c);
              Append(~Y_Opi, Op!(lambdas[j]*lifts[i]*lambdas[c]^(-1)));
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
          Append(~Y_Opi, Op!(levelmults[j]*lambda*ellcosets[j]*lifts[i]*
                             (levelmults[c]*lambda*ellcosets[c])^(-1)));
        end for;
      end if;
    end if;
    Append(~X, Xi);
    Append(~Y_Op, Y_Opi);
  end for;

// GetMemoryUsage(); MemProfile();

  Y_U := [];
  vprintf ModFrmHil: "Reducing %4o units of Gamma ......................... ", n*numP1;
  vtime ModFrmHil:
  for i in [1..n] do
    G := [];

    for j in [1..numP1] do
      y := CompleteRelationFromUnit(Gammap, Y_Op[i][j], RPAsp, RPAspinv : IsTrivialCoefficientModule := IsLevelOne);
      if not IsLevelOne then
        y := y*Zp[X[i][j]];
      end if;
      Append(~G, y);
    end for;
    Append(~Y_U, G);
  end for;

// GetMemoryUsage(); MemProfile();

  vprintf ModFrmHil: "Computing H1 (coinduced) ............................. ";
  vtime ModFrmHil:
  Htilde, mH := InducedH1(Gamma, Gammap, N, cosets, cosetsp, RPAs, RPAsinv, RPAsp, RPAspinv);
  
  if #Htilde eq 0 then
    return [];
  else
    M := HorizontalJoin([ &+[ Y_U[i][j] : j in [1..numP1]] : i in [1..n] ]);
    MH := Matrix(Htilde)*M;
    MM := Matrix([mH(MH[i]) : i in [1..#Htilde]]);
    return MM;
  end if;
end function;
