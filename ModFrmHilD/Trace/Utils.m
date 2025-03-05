//////////////// Enumeration of Totally Positive Elements ////////////////

intrinsic ElementsInABox(M::ModFrmHilDGRng, aa::RngOrdFracIdl,
                         XLBound::Any, YLBound::Any, XUBound::Any, YUBound::Any) -> SeqEnum
  {Enumerates all elements c in aa with XLBound <= c_1 <= XUBound and  YLBound <= c_2 <= YUBound}

  for bnd in [XUBound, YUBound, XLBound, YLBound] do
    require ISA(Type(bnd),FldReElt) : "Bounds must be coercible to real numbers";
  end for;
  basis := TraceBasis(aa);
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);

  //if Evaluate(basis[2],places[1]) lt 0 then
  //  basis := [basis[1], -basis[2]];
  //end if;


  // Precomputationss
  a_1 := Evaluate(basis[1], places[1]);
  a_2 := Evaluate(basis[1], places[2]);
  b_1 := Evaluate(basis[2], places[1]);
  b_2 := Evaluate(basis[2], places[2]);
  assert b_1 lt 0 and b_2 gt 0; // if this assumption changes, the inequalities get swapped

  // List of all Elements
  T := [];
  trLBound := Ceiling(XLBound+YLBound);
  trUBound := Floor(XUBound+YUBound);
  for i in [trLBound..trUBound] do
    // at place 1, i*a2 + j*b2 <= XUBound => j >= (XUBound -i*a1)/b1
    // at place 2, i*a2 + j*b2 >= YLBound => j >= (YLBound -i*a2)/b2
    lBound := Ceiling(Max((XUBound-i*a_1)/b_1, (YLBound-i*a_2)/b_2));
    uBound := Floor(Min((XLBound-i*a_1)/b_1, (YUBound-i*a_2)/b_2));
    for j in [lBound..uBound] do
      Append(~T, i*basis[1] + j*basis[2]);
    end for;
  end for;

  return T;
end intrinsic;

function lattice_elements_in_hypercube(basis, LBound, UBound, dual_basis)
  // dual_basis are elements x[1], ..., x[n] such that 
  // for every i we have sum_j basis[i][j]*x[i][j] > 0 and sum_j basis[i][j]*x[k][j] = 0 for all k > i
  // if #basis eq n, enumerates all integers a_1, ..., a_n such that LBound[j] <= sum a_i basis[i][j] <= UBound[j] for all j
  if #basis eq 0 then return [[]]; end if;
  eps := 10^(-100);
  assert (#LBound eq #basis[1]) and (#UBound eq #basis[1]); // number of inequalities
  n := #basis[1];
  if #basis eq 1 then
    b := basis[1];
    lBound := Maximum([(b[j] gt 0 select LBound[j] else UBound[j])/b[j] : j in [1..n]]);
    uBound := Minimum([(b[j] gt 0 select UBound[j] else LBound[j])/b[j] : j in [1..n]]);
    return [[alpha] : alpha in [Ceiling(lBound)..Floor(uBound)]];
  end if;
  x := dual_basis;
  assert &and[Abs(&+[basis[i][j]*x[i][j] : j in [1..n]]) gt eps : i in [1..#basis]];
  assert &and[&and[Abs(&+[basis[k][j]*x[i][j] : j in [1..n]]) lt eps : k in [i+1..#basis]] : i in [1..#basis]];
  lBound := &+[(x[1][j] gt 0) select x[1][j]*LBound[j] else x[1][j]*UBound[j] : j in [1..n]];
  uBound := &+[(x[1][j] gt 0) select x[1][j]*UBound[j] else x[1][j]*LBound[j] : j in [1..n]];
  factor := &+[basis[1][j]*x[1][j] : j in [1..n]];
  norm_lBound := Ceiling((factor gt 0 select lBound else uBound) / factor);
  norm_uBound := Floor((factor gt 0 select uBound else lBound) / factor);
  ret := [];
  for alpha in [norm_lBound..norm_uBound] do
    small_LBound := [LBound[j] - alpha*basis[1][j] : j in [1..n]];
    small_UBound := [UBound[j] - alpha*basis[1][j] : j in [1..n]];
    smaller_dim := lattice_elements_in_hypercube(basis[2..#basis], small_LBound, small_UBound, dual_basis[2..#basis]);
    ret cat:= [[alpha] cat coeffs : coeffs in smaller_dim];
  end for; 
 
  assert &and[&+[t[i]*basis[i][j] : i in [1..#basis]] le UBound[j] + eps : t in ret, j in [1..n]];
  assert &and[&+[t[i]*basis[i][j] : i in [1..#basis]] ge LBound[j] - eps : t in ret, j in [1..n]];
  return ret;
end function;

intrinsic ElementsInAHyperCube(M::ModFrmHilDGRng, aa::RngOrdFracIdl,
                               LBound::SeqEnum[FldReElt], UBound::SeqEnum[FldReElt]) -> SeqEnum
  {Enumerates all elements c in aa with LBound[i] <= c[i] <= UBound[i] for all i}

  basis := TraceBasis(aa);
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);
  n := Degree(F);

  // Precomputations
  basis_embedded := [[Evaluate(b, place) : place in places] : b in basis];
  dual_basis_embedded := [[Evaluate(ZF.i, place) : place in places] : i in [1..n]];

  all_coeffs := lattice_elements_in_hypercube(basis_embedded, LBound, UBound, dual_basis_embedded);
  ret := [&+[coeffs[i]*basis[i] : i in [1..n]] : coeffs in all_coeffs];

  if (n eq 2) then
    assert Set(ret) eq Set(ElementsInABox(M, aa, LBound[1], LBound[2], UBound[1], UBound[2]));
  end if;

  return ret;
end intrinsic;
