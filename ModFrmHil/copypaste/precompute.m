freeze; 

/***********************************************************************************
       PRECOMPUTATION PHASE OF DEMBELE'S ALGORITHM FOR COMPUTING
       HILBERT MODUULAR FORMS VIA DEFINITE QUATERNION ALGEBRAS

       Steve Donnelly, October 2008

       Last modified: May 2010

***********************************************************************************/

// We modify the import statements to import from copy-pasted local copies 
//import "../../Algebra/AlgAss/ideals-jv.m"
import "AlgAss/ideals-jv.m":                ColonInternal, 
                                            has_element_of_norm, 
                                            IsIsomorphicInternal, 
                                            Jprime, 
                                            TotallyPositiveUnits, 
                                            convert_rids;

//import "../../Algebra/AlgAss/enum.m" :
import "AlgAss/enum.m":                     junk_for_IsIsomorphic,
                                            RightIdealClassesAndOrders; 

// import "../../Algebra/AlgQuat/ramified.m" :
import "AlgQuat/ramified.m" :               RealValuations;

declare attributes AlgAssVOrd: norm_one_units_mod_scalars, 
                               pos_scalar_units_mod_norms,
                               thetas; // see usage below

declare verbose ModFrmHil, 3;

//////////////    GLOBAL SETTINGS    ///////////////
debug := false;
////////////////////////////////////////////////////

intrinsic 'meet'(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{The intersection of the ideals I and J of the same associative order}
  require Order(I) cmpeq Order(J) : "I and J must be ideals of the same order";
  left := IsLeftIdeal(I) and IsLeftIdeal(J);
  right := IsRightIdeal(I) and IsRightIdeal(J);
  require left or right: "Can't intersect left ideal with right ideal";
  B:= ZBasis(I);
  L:= Lattice( Matrix( Coordinates(ZBasis(J), B) ) );
  LL:= L meet StandardLattice(#B);
  BN:= BasisMatrix(LL);
  BB:= [&+[ BN[i,j]*B[j] : j in [1..#B] | BN[i,j] ne 0] : i in [1..#B]];
  if left and right then
    IJ := ideal< Order(I) | BB >;
  elif left then
    IJ := lideal< Order(I) | BB >;
  elif right then
    IJ := rideal< Order(I) | BB >;
  end if;
  return IJ;
end intrinsic;

// a sequence containing the right ideals in the maximal order O
// that have norm pp, where pp is a prime in the base ring of O
// (there are 1+Norm(pp) such ideals)

function Subideals_of_order(O, pp)
  p := Minimum(pp);
  A := Algebra(O);
  error if not IsMaximal(O), "Error in Subideals: not implemented for non-maximal orders";
  error if not IsPrime(pp), "Error in Subideals: only implemented for prime ideals pp";

  if pp in RamifiedPlaces(A) then
    Isub := ideal<O|pp> + CommutatorIdeal(O);  
    Isub`Norm := pp;
    if IsMaximal(O) then 
      Isub`RightOrder := O; Isub`LeftOrder := O; end if;
    return [Isub]; end if;

  ZbasisO := ZBasis(O);  
  M2F, phi := pMatrixRing(O, pp);
  e11 := Inverse(phi)(M2F.1);
  e21 := Inverse(phi)(M2F.2*M2F.1);
  e11coords, e21coords := Explode(Coordinates( [A!e11,A!e21], ZbasisO ));
  // Reduce mod p otherwise 'rideal' will choke  
  e11red := O! &+[ (e11coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];
  e21red := O! &+[ (e21coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];
 
  k, mk := ResidueClassField(Order(pp), pp);
  ideals := [];
  for museq in [[0,1]] cat [[1,x@@mk] : x in k] do
    mu := O!(museq[1]*e11red + museq[2]*e21red);
    I := rideal<O | [mu] cat Generators(pp)>;
    if debug then assert RightOrder(I) eq O; assert Norm(I) eq pp; end if; 
    I`Norm := pp;
    Append( ~ideals, I);
  end for;
  assert #ideals eq Norm(pp)+1;
  return ideals;
end function;

// intersects Subideals_of_order with I, only works for I coprime to pp

function Subideals_of_ideal(I, pp)
  O := Order(I);
  error if not IsRightIdeal(I), "I must be a right ideal";
  if pp in RamifiedPlaces(Algebra(O)) then
    T := Subideals_of_order(O, pp)[1];  assert IsTwoSidedIdeal(T);
    IT := '*'(I, T : Sides:="Right");
    return [ IT ];
  end if;
  error if Norm(GCD(Norm(I), pp)) ne 1, "Norm(I) must be coprime to pp";
  Osubids := Subideals_of_order(O, pp);
  Isubids := [I meet P : P in Osubids];
  Napp := Norm(I)*pp;
  if debug then
    for J in Isubids do 
      assert RightOrder(J) eq O;
      assert Norm(J) eq Napp; end for; 
  end if;
  for i := 1 to #Isubids do Isubids[i]`Norm := Napp; end for;
  return Isubids;
end function;

// A sequence containing the right ideals in Order(I) 
// that have index pp in I (ie J < I and I/J ~ pp) 
// where pp is a prime in the base ring of Order(I).
// There are 1+Norm(pp) such ideals.

// The localisation of I equals pp^e (for some integer e) times 
// the ideal consisting of all matrices [r,s // t,u] whose columns
// are multiples of some fixed vector (a:b) mod pp^m, ie the columns
// are in the ratios (r:t) == (s:u) == (a:b) mod pp^m.
// We have Norm(I) = pp^(2*e + m) locally.
/*
function Subideals_of_ideal_new(I, pp)
printf("_new:  ");
  O := Order(I);
  error if not IsRightIdeal(I), "I must be a right ideal";
time  M2F, phi, toFpp := pMatrixRing(O, pp : Precision:=20);
  Rpp := Integers(BaseRing(M2F));
  ZbasisO := ZBasis(O);
  ZbasisI := ZBasis(I);
  gens := [phi(zb) : zb in ZBasis(I)];
  // Figure out common factor pp^e and normalise
  e := Min([ Valuation(a) : a in Flat([Eltseq(mat) : mat in gens]) ]);
  pi := UniformizingElement(Rpp);
  pie := pi^e;
  gens := [gen/pie : gen in gens]; 

  // Figure out m and (a:b) 
  // Suffices to look at the first columns of the gens, and if we know Norm(I), 
  // it suffices to look at any one column that's not congruent to (0:0)
  m := Min([Valuation(x,pp) : x in Generators(Norm(I))]) - 2*e;
  for gen in gens do 
    r,_,t,_ := Explode(Eltseq(gen));
    if Valuation(r) eq 0 or Valuation(t) eq 0 then 
      a := r;  b := t;
      break gen;
    end if;
  end for;
  if debug then
    first_cols := Matrix([ [Rpp| gen[1,1], gen[2,1]] : gen in gens ]);
    col_space := RowSubmatrix(EchelonForm(first_cols), 1,2);
    m1 := Valuation(Determinant(col_space));  assert m1 lt Infinity();
    a1 := col_space[1,1];  b1 := col_space[1,2]; 
    assert m eq m1 and Valuation(a-a1) ge m and Valuation(b-b1) ge m;
  end if;

  // Create subideals corresponding to refinements of (a:b) mod pp^(m+1)
  
  pim := pi^m;
  kpp, red := ResidueClassField(Rpp);
  ks := [k@@red : k in kpp];
  // proj_pts contains tups of the form <a,b,m_new>
  if m eq 0 then
    proj_pts := [<0,1, 1>] cat [<1,k, 1> : k in ks];
  elif Valuation(a) eq 0 then 
    proj_pts := [<pi*a,pi*b, m>] cat [<a,b+k*pim, m+1> : k in ks] where pim is pi^m;
  elif Valuation(b) eq 0 then
    proj_pts := [<pi*a,pi*b, m>] cat [<a+k*pim,b, m+1> : k in ks] where pim is pi^m;
  else
    error "(a:b) is supposed to be a projective point mod pp^m, \na =",a, "\nb =",b;
  end if;
  assert #proj_pts eq 1+Norm(pp);

  e11 := Inverse(phi)(M2F.1);
  e21 := Inverse(phi)(M2F.2*M2F.1);
  e11coords, e21coords := Explode(Coordinates( [e11,e21], ZbasisO ));
// Check that e11 and e21 are actually integral (if not, need to use more Precision in pMatrixRing) 
ChangeUniverse( ~e11coords, Integers());  ChangeUniverse( ~e21coords, Integers());
  // Reduce mod p otherwise 'rideal' will choke  
  p := Minimum(pp);  
  e11red := O! &+[ (e11coords[i] mod p^(m+1)) * ZbasisO[i] : i in [1..#ZbasisO]];
  e21red := O! &+[ (e21coords[i] mod p^(m+1)) * ZbasisO[i] : i in [1..#ZbasisO]];

  ppem := pp^(e+m);  ppem1 := ppem*pp;  
  ppNI := pp*Norm(I);
  pie := pie @@toFpp;
  subids := [];
  for pt in proj_pts do 
//"pt =",pt;
    aa := pt[1] @@toFpp;  bb := pt[2] @@toFpp;  mnew := pt[3];
    mu := O!(aa*e11red + bb*e21red);
    if mnew eq m then
      Isub := I meet rideal<O | [pie*mu] cat Generators(ppem)>;
    else 
      assert mnew eq m+1; 
      Isub := I meet rideal<O | [pie*mu] cat Generators(ppem1)>;
    end if;
    if debug then assert RightOrder(Isub) eq O; assert Norm(Isub) eq ppNI; assert Isub subset I; 
    else Isub`Norm := ppNI; end if;
    Append( ~subids, Isub);
  end for;
  return subids;
end function;
*/

// Much better way!  It's overkill to use pMatrixRing just to work in I/pp*I.  
// Instead we find elements a*z1+b*z2 in the O-module I/pp*I, which span 2-dim 
// pieces of it.  The subideals are (a*z1+b*z2)*O + pp*I, for (a:b) in P^1(pp).

procedure assign_left_orders(subideals) 
  for I in subideals do if not assigned I`LeftOrder then _ := LeftOrder(I); end if; end for;
end procedure;

function Subideals_of_ideal_newer(I, pp : use_theta:=false)
  vprintf ModFrmHil,2: "_newer: ";
  O := Order(I);  
  OI := LeftOrder(I); 
  A := Algebra(O);
  OF := BaseRing(O);
  error if not IsRightIdeal(I), "I must be a right ideal";
  error if Order(pp) ne OF, "pp must be an ideal of the base order";
  assert IsMaximal(O);

  if pp in RamifiedPlaces(A) then return Subideals_of_ideal(I, pp); end if;

  Fpp, toFpp := ResidueClassField(pp);
  // get a uniformizer with negative valuations at all other places
  ppinv := pp^-1;
  pi := 1/pi1 where _,pi1 := TwoElement(ppinv);  
assert Valuation(pi,pp) eq 1 and 
       &and [tup[2] lt 0 or tup[1] eq pp : tup in Factorization(ideal<OF|pi>)];
   
  // Get bases for O, I and OI for which the coeff ideals are prime to pp, 
  // and for which the basis elements are in O or I
  basisO := Basis(O);  assert Universe(basisO) eq A;
  coeffidlsO := CoefficientIdeals(PseudoMatrix(O));
  for i := 1 to 4 do
    // first arrange that basisO is contained in O
    m := Numerator(Minimum(coeffidlsO[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsO[i] /:= m;
      basisO[i] *:= m;
    end if;
    v := Valuation(coeffidlsO[i], pp); 
    if v ne 0 then
      coeffidlsO[i] /:= pi^v;
      basisO[i] *:= pi^v;
    end if;
  end for;
  assert basisO[1] eq 1; // should be...
  if debug then assert Order(ZBasis(O) cat basisO) eq O; end if;
  
  basisI := Basis(I);  assert Universe(basisI) eq A;
  coeffidlsI := CoefficientIdeals(PseudoMatrix(I));
  for i := 1 to 4 do
    // first arrange that basisI is contained in I
    m := Numerator(Minimum(coeffidlsI[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsI[i] /:= m;
      basisI[i] *:= m;
    end if;
    v := Valuation(coeffidlsI[i], pp); 
    if v ne 0 then
      assert v lt 0;
      coeffidlsI[i] /:= pi^v;
      basisI[i] *:= pi^v;
    end if;
  end for;
  if debug then assert rideal<O| ZBasis(I) cat basisI> eq I; end if;

  basisOI := Basis(OI);  assert Universe(basisOI) eq A;
  coeffidlsOI := CoefficientIdeals(PseudoMatrix(OI));
  for i := 1 to 4 do
    // first arrange that basisOI is contained in OI
    m := Numerator(Minimum(coeffidlsOI[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsOI[i] /:= m;
      basisOI[i] *:= m;
    end if;
    v := Valuation(coeffidlsOI[i], pp); 
    if v ne 0 then
      coeffidlsOI[i] /:= pi^v;
      basisOI[i] *:= pi^v;
    end if;
  end for;
  assert basisOI[1] eq 1; // should be...
  if debug then assert Order(ZBasis(OI) cat basisOI) eq OI; end if;
/*
myOI := Order(A, PseudoMatrix( coeffidlsOI, Matrix([Eltseq(A!basisOI[i]) : i in [1..4]]) ) );
//assert myOI cmpeq OI;
assert &and [zb in myOI : zb in ZBasis(OI)] and &and [zb in OI : zb in ZBasis(myOI)];
*/
  // Write down the module action of O/pp*O on I/pp*I, as matrices over Fpp 
  // for basisO[2] and basisO[3] (since these generate the ring O/pp*O).
  // Note that O multiplies I from the right.   We express the action 
  // in terms of 4x4 row matrices (so these also act on the right).
  action_mats := [];
  basisI_mat := Matrix([ Eltseq(c) : c in basisI ]);
  basisI_mat_inv := basisI_mat ^-1;
  for b in basisO[2..3] do 
    coords_wrt_A := Matrix([ Eltseq(c*b) : c in basisI ]);
    coords_wrt_basisI := coords_wrt_A * basisI_mat_inv;
    mat := Matrix(Fpp,4,4, [cc@toFpp : cc in Flat(Eltseq(coords_wrt_basisI))] );
                            // there are no pp's in the denoms
    Append(~action_mats, mat);
  end for;

  // The ideals we want correspond to the 2-dim O-submodules of I/pp*I. 
  // We find a 2-dim subspace S (not an O-submodule), such that each element
  // of S generates a 2-dim O-submodule (yielding 1+#Fpp distinct ones in total).
  // Under a splitting I/pp*I == Mat(2,Fpp), S would have the shape [* 0 // * 0], 
  // and the submodules would be [a 0 // b 0]*Mat(2,Fpp) for (a:b) in P^1(Fpp).
  // We obtain S as the image of M-gamma*I, where gamma is an eigenvalue in Fpp of M.
  // The elements of O satisfy quadratic polynomials, hence the (nonscalar) matrices  
  // in the Fpp-span of the two action_mats will have quadratic min polys, and it's
  // not hard to show this must split into linear factors for some M in the span.  
  for s in Fpp do 
    M := action_mats[1] + s*action_mats[2];
    minpol := MinimalPolynomial(M);  assert Degree(minpol) eq 2;
    f := Factorization(minpol)[1][1];
    if Degree(f) gt 1 then continue; end if;
    fM := Evaluate(f, M);
    S := RowSpace(fM); // = image of fM
    break;
  end for;
  error if not assigned fM, 
       "Failed to find a matrix (in the 2-dim span) with an eigenvalue in Fpp";
  z1 := &+[ (S.1)[i]@@toFpp * basisI[i] : i in [1..4]]; 
  z2 := &+[ (S.2)[i]@@toFpp * basisI[i] : i in [1..4]]; 

  // The subideals are (a*z1+b*z2)*O + pp*I, as (a:b) runs through P^1(Fpp)
  ppI := HermiteForm(PseudoMatrix( [pp*CI : CI in coeffidlsI], Matrix([Coordinates(O,c) : c in basisI]) ));
  ppNI := pp*Norm(I); // = the norm of all the subidls
  subideals := [];
  P1Fpp := [ [Fpp|1,0] ] cat [ [x,1] : x in Fpp ];
  for ab in P1Fpp do 
    a,b := Explode(ab);  //"a =", a, "b =", b;
    gen_mod_pp := a*S.1 + b*S.2;  assert not IsZero(gen_mod_pp);
    gen := a@@toFpp * z1 + b@@toFpp * z2;
    // figure out 2 elements of basisO to span the image of (a*z1+b*z2)*O in I/pp*I
    inds := [1];  // since gen*1 is not in pp*I
    for i := 2 to 4 do 
      // if basisO[2,3] don't work, then basisO[4] must
      if i eq 4 or Rank(VerticalJoin( gen_mod_pp, gen_mod_pp*action_mats[i-1] )) eq 2 then
        Append(~inds,i); break; end if;
    end for;
    genO := PseudoMatrix( coeffidlsO[inds], Matrix([Coordinates(O,gen*basisO[i]) : i in inds]) );
    Isub := rideal<O| HermiteForm(VerticalJoin(ppI, genO)) : Check:=debug>; 
    if debug then assert RightOrder(Isub) eq O; assert Norm(Isub) eq ppNI; assert Isub subset I; 
    else Isub`RightOrder := O; Isub`Norm := ppNI; end if;
    Append(~subideals, Isub);
  end for;
  if debug then assert &and [subideals[i] ne subideals[j] : j in [1..i-1], i in [1..#subideals]]; end if;

  if use_theta then
    vprintf ModFrmHil, 2: "Left orders of subideals "; vtime ModFrmHil, 2:
    assign_left_orders(subideals);  
  end if;

  return subideals;
  
  /********    Compute the left orders of the subideals    ********/
  
  // Identify OI/pp with Mat(2,Fpp) via the action of OI/pp on the 2-dimensional module S
  left_action_mats := [IdentityMatrix(Fpp,2)]; // because basisOI[1] = 1
  assert basisOI[1] eq 1;
  for b in basisOI[2..4] do 
    cols := [];
    for z in [z1,z2] do 
      coords_wrt_basisI := Vector(Eltseq(b*z)) * basisI_mat_inv;
      coords_wrt_S := Coordinates(S, S![cc@toFpp : cc in Eltseq(coords_wrt_basisI)] );
                          // there are no pp's in the denoms
      Append(~cols, coords_wrt_S);
    end for;
    Append(~left_action_mats, Transpose(Matrix(cols)) );
  end for;

  // Choose elements of OI that reduce mod pp to the standard basis elements of Mat(2,Fpp)
  cob := Matrix(Fpp,4,4, [Eltseq(mat) : mat in left_action_mats] );
  bool, cob_inv := IsInvertible(cob);  assert bool;
  m11,m12,m21,m22 := Explode([A| &+[ r[i]@@toFpp * basisOI[i] : i in [1..4] ] : r in Rows(cob_inv) ]);

basisOI_mat := Matrix([ Eltseq(c) : c in basisOI ]);
for i := 1 to 4 do mm := [m11,m12,m21,m22][i];
 assert Vector( [c@toFpp : c in Eltseq(mm_A*basisOI_mat^-1) where mm_A := Vector(Eltseq(A!mm))] ) * cob 
     eq Vector( [Fpp| i eq j select 1 else 0 : j in [1..4]] ); end for; 

  // Write down the left order for each (a:b).  
  // Note that the subideal is locally principal, and modulo pp it is generated by 
  // the matrix [a r*p // b s*p] for any r,s for which a*s-b*r is nonzero mod pp.
  // To get the left order we conjugate OI by this matrix and add pp*OI.
  ppOI := HermiteForm(PseudoMatrix( [pp*CI : CI in coeffidlsOI], Matrix([Eltseq(c) : c in basisOI]) ));
  _,pi := TwoElement(pp); // the standard uniformiser
  one := ideal<OF|1>;
  left_orders := [];
time
  for i := 1 to #P1Fpp do 
    Isub := subideals[i];
    ppIsub := rideal<O| PseudoMatrix( [pp*CI : CI in CoefficientIdeals(pm)], Matrix(pm) ) 
                       : Check:=false> where pm is PseudoMatrix(Isub);
    ZBIsub := ZBasis(Isub); // TO DO: don't do this, of course
    a,b := Explode(P1Fpp[i]);  
    if b eq 0 then  
      // take [r,s] = [0,1]
      elts := [A| m11, m22];  xx0 := m12;  
 xx1 := m21;
    else assert b eq 1;  
      // take [r,s] = [1,0]
      aa := a@@toFpp;
      elts := [A| m11+m22, m11-aa*m12];  xx0 := aa*(m11-m22)-aa^2*m12+m21;  
 xx1 := (a eq 0) select m12 else m21;
    end if;
    // We know there's an element xx in pp*LeftOrder(Isub) with xx == xx0 mod pp; we now lift it mod pp^2
    // TO DO ... rewrite efficiently + get it right...
    flag := false;
    ppxx1 := pi*xx1;
    for s in Fpp do 
      xx := xx0 + s@@toFpp * ppxx1;
      if &and [xx*zb in ppIsub : zb in ZBIsub] then flag := true; break s; end if;
    end for;  assert flag; 
 /* ppm12 := pi*m12;  ppm21 := pi*m21;  
    flag := false;
    Fpp_classes := [ s@@toFpp : s in Fpp ];
    for s1 in Fpp_classes do for s2 in Fpp_classes do  
      xx := xx0 + s1*ppm12 + s2*ppm21; 
      // check if xx*Isub is contained in pp*Isub
      if &and [xx*zb in ppIsub : zb in ZBIsub] then flag := true; break s1; end if;
    end for; end for;  assert flag; 
 */
    conj := PseudoMatrix( [one,one,ppinv], Matrix([Eltseq(X) : X in elts cat [xx]]) ); // coords in terms of Basis(A)
    left_order := Order(A, HermiteForm(VerticalJoin(conj, ppOI)) );
    Append(~left_orders, left_order);
  end for;

printf "debug (check LeftOrder):  "; time
  for i in [1..#subideals] do 
if true or debug then 
      LOi := LeftOrder(subideals[i]);
      assert LOi eq left_orders[i]; 
      /*
      assert &and [b1*b2 in LOi : b1,b2 in ZBasis(LOi)]; // check they are really rings
      assert &and [b1*b2 in left_orders[i] : b1,b2 in ZBasis(left_orders[i])]; 
      assert IsMaximal(LOi) and IsMaximal(left_orders[i]);
      assert &and [zb in LOi : zb in ZBasis(left_orders[i])] and 
             &and [zb in left_orders[i] : zb in ZBasis(LOi)]; 
      */
    else subideals[i]`LeftOrder := left_orders[i]; end if;
  end for;
  return subideals;
end function;

/* This is for checking one method against another
intrinsic Subideals(arg::.,pp::.)  -> .
{}
  if ISA(Type(arg), AlgAssVOrd) then 
    print "Don't give me some stupid order, I want ideals!";
    error "";
    //return Subideals(rideal<arg | 1>, pp);
  end if;
  assert ISA(Type(arg), AlgAssVOrdIdl); 
time  ans := Subideals_of_ideal_new(arg, pp);
  if Norm(GCD(Norm(arg),pp)) ne 1 then 
    "Not coprime!"; return ans; end if;
time  ans0 := Subideals_of_ideal(arg, pp);
assert &and[ J in ans0 : J in ans ]
   and &and[ J in ans : J in ans0 ];
  return ans, ans0;
end intrinsic;
*/

// Given a sequence of units in OF that form a subgroup U of OF*/(OF*)^2 
// containing N, the group of norms of OH*, this returns units in OF 
// whose images in OF*/(OF*)^2 form a transversal of U/N 

function units_mod_norms(units, OH)
  OF := BaseRing(OH);
  UF, unitmap := UnitGroup(OF);
  UFmod2, mod2 := quo< UF | 2*UF >;
  norms := {Norm(u) : u in Units(OH)};
  N := sub< UFmod2 | [u @@unitmap @mod2 : u in norms] >;
  U := sub< UFmod2 | [u @@unitmap @mod2 : u in units] >;
  assert N subset U;
  return [t @@mod2 @unitmap : t in Transversal(U,N)];
end function;

function gcd_of_quad_form(M)
  return GCD([M[i,i] : i in [1..Nrows(M)]] cat [2*m : m in Eltseq(M)]);
end function;

////////////////////////   PRECOMPUTATION   ///////////////////////////

// Let I1, .., Ih denote the ridls.  For a prime power P = PP^eP,
// tps[<j,i>] := sequence of reps t in A, up to units of LeftOrder(Ii)
// such that P*Ii < t*Ij < Ii and the size of (t*Ij)\Ii is Norm(P)^2
// (Note that when eP > 1, we don't remove the "non-Hecke elements" here)

procedure precompute_tps(OH, P, ridls, record_idx, rows)

  H := Algebra(OH);
  F := BaseField(H);  
  OF := Integers(F);
  
  Pfact := Factorization(P);
  assert #Pfact eq 1; // must be prime power
  PP, eP := Explode(Pfact[1]);
  NP := Norm(P);
  NPP := Norm(PP);
  ramified := P in RamifiedPlaces(H);
  assert eP eq 1 or not ramified;
  if ramified then
    num := 1;
  elif eP eq 1 then
    num := NP + 1;
  else
    NPP := Norm(PP);
    num := (NPP^(eP+1) - 1) div (NPP - 1);
  end if;

  h := #ridls;
  assert rows subset [1..h];

  // TO DO: distinct left orders may be isometric, when Disc(H) ne 1
  // (it's unavoidable if we insist on strict_support in get_rids).
  // It just means redundant work computing thetas, norm_one_units etc
  ords := [];
  order_indices := [];
  for I in ridls do 
    for i := 1 to #ords do
      if IsIdentical(ords[i], I`LeftOrder) then 
        Append(~order_indices, i); 
        continue I; 
      end if;
    end for;
    Append(~ords, I`LeftOrder);
    Append(~order_indices, #ords); 
  end for;

  vprintf ModFrmHil: "Precomputation" * (debug select " (in debug mode): " else ": ") * "\n";
  IndentPush();
  time0 := Cputime();
  vprint ModFrmHil, 3: "Left order classes of the right ideal classes are", order_indices;

  pos_units := TotallyPositiveUnits(OF);
  for l := 1 to #ords do 
    LO := ords[l];
    if not assigned LO`norm_one_units_mod_scalars then
      n1group, n1map := NormOneGroup(LO : ModScalars);
      LO`norm_one_units_mod_scalars := [u@n1map : u in n1group];
    end if;
    if not assigned LO`pos_scalar_units_mod_norms then
      LO`pos_scalar_units_mod_norms := units_mod_norms(pos_units, LO);
    end if;
  end for;
  pos_units_mod_norms := [LeftOrder(I)`pos_scalar_units_mod_norms : I in ridls];
  real_places := RealPlaces(F);
  U, Umap := IndependentUnits(OF);
  Uvals := [RealValuations(RealPlaces(F), Umap(U.i)) : i in [1..Ngens(U)]]; 
  UnitRealValuations := <U, Umap, Uvals>;

  // Decide whether to use small prime method for the prime P, 
  // and whether it's worth using thetas
  // TO DO: rethink this -- if the colons etc are known, the large prime method is very quick,
  //        at least until the field degree gets too large.  A nice example is Q(sqrt(82)).
  C := #NarrowClassGroup(F); // known
  use_theta := h gt 10 and #ords gt 1  // could be worthwhile 
               and rows eq [1..h];     // TO DO for arbitrary rows(?)
  small_prime := eP eq 1; // subideals code assumes P is prime
  small_prime and:= ramified or
    use_theta select 10*num le #rows/C // would be 1*num if thetas distinguished all orders, and ignoring all overhead
               else h/2*num le #rows/C;
  use_theta and:= small_prime; // only the small_prime method involves thetas

  if not assigned OH`RightIdealClasses[record_idx]`rids_narrow_class_junk then
    ClF, ClFmap := NarrowClassGroup(F);
    ClFelts := [ cl : cl in ClF ];
    ClFreps := [ cl @ClFmap : cl in ClFelts ]; assert ClFreps[1] eq 1*OF;
    ridls_norms_classes := [Norm(I) @@ClFmap : I in ridls];
    inds := [Index(ClFelts, NI) : NI in ridls_norms_classes];

    // For each pair of ridls I,J find a generator of the pid R*Norm(I)/Norm(J) where R is in ClFreps 
    ridls_norms_gens       :=  [F| 0 : i in [1..h]];
    ridls_colon_norms_gens := [[F| 0 : i in [1..h]] : j in [1..h]];
    ClF_reps_diffs_gens    := [[F| 0 : i in [1..#ClFreps]] : j in [1..#ClFreps]];
    // Find generators of Cij/rep(Cij) where Cij is rep[i]/rep[j]
    for j,i in Seqset(inds) do 
      if i eq j then
        ClF_reps_diffs_gens[j][i] := F!1;
      else
        Q := ClFreps[i]/ClFreps[j];
        R := ClFreps[r] where r is Index(ClFelts, ClFelts[i]-ClFelts[j]);
        _, g := IsNarrowlyPrincipal(Q/R : real_places:=real_places, UnitRealValuations:=UnitRealValuations);
        ClF_reps_diffs_gens[j][i] := F!g;
      end if;
    end for;
    vprintf ModFrmHil: "Computing generators for norms of right ideal classes ... "; 
    vtime ModFrmHil:
    for i := 1 to h do 
      ii := Index(ClFelts, -ridls_norms_classes[i]);
      _, g := IsNarrowlyPrincipal(ClFreps[ii]*Norm(ridls[i]) : real_places:=real_places, 
                                                               UnitRealValuations:=UnitRealValuations);  
      ridls_norms_gens[i] := F!g;
    end for;
    for j,i in [1..h] do
      ii := Index(ClFelts, -ridls_norms_classes[i]);
      jj := Index(ClFelts, -ridls_norms_classes[j]);
      ridls_colon_norms_gens[j][i] := (i eq j) select 1 else
                                      ridls_norms_gens[i]/ridls_norms_gens[j] / ClF_reps_diffs_gens[jj][ii];
    end for;
    if debug then // check by doing it the straightforward O(h^2) way 
      for j,i in [1..h] do 
        R := ClFreps[r] where r is Index(ClFelts, ridls_norms_classes[j]-ridls_norms_classes[i]);
        bool, g := IsNarrowlyPrincipal(R*Norm(ridls[i])/Norm(ridls[j]) : real_places:=real_places,
                                                                         UnitRealValuations:=UnitRealValuations);  
        assert bool and g*OF eq g1*OF where g1 is ridls_colon_norms_gens[j][i];
      end for; 
    end if;

    OH`RightIdealClasses[record_idx]`rids_narrow_class_junk := 
      [* ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, inds, ridls_norms_gens, ridls_colon_norms_gens *];
  end if; // assigned junk
  // Look up junk
  ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, _, _, ridls_colon_norms_gens 
    := Explode(OH`RightIdealClasses[record_idx]`rids_narrow_class_junk);

  if use_theta then
    // Try to quickly determine the class of the left order of each subideal using theta series.  
    // This reduces the number of ideal-isomorphism tests, but means we have to compute the left orders + thetas. 
    ords_forms := [ [j[2],j[3]] where j is junk_for_IsIsomorphic(LO) : LO in ords ];
    /* TO DO: use values of short vectors somehow ... it's yielded nothing so far!
    ords_grams := [ T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
                                        where j is junk_for_IsIsomorphic(LO) : LO in ords ];
    */
    // Note: LO`thetas[1] now computed in RightIdealClassesAndOrders
    if not &and [assigned LO`thetas : LO in ords] then
      // check if the second forms are pos def (TO DO: should we arrange this by taking 'a' totally positive?)
      js := &and[ IsPositiveDefinite(forms[2]) : forms in ords_forms ] select [1,2] else [1];
      ords_lats := [ [LatticeWithGram(ords_forms[i,j] : CheckPositive:=false) : j in js] : i in [1..#ords] ];
      dim := 4*Degree(F); 
      Vol1 := Pi(RealField())^(dim/2) / Gamma(dim/2 + 1); // = volume of unit sphere of this dimension
      Det_size := Min([ Determinant(ords_forms[i][1]) : i in [1..#ords] ]);
      theta_prec := Ceiling( (100 * Sqrt(Det_size) / Vol1) ^ (2/dim) );
      g := GCD([gcd_of_quad_form(ords_forms[i,j]) : i in [1..#ords], j in js]); // lazy
      theta_prec := (theta_prec div g) * g; // TO DO: ThetaSeries should be smart enough to figure this out!
      // get theta coefficients up to and including theta_prec
      vprintf ModFrmHil: "Computing theta series to precision %o ... ", theta_prec; 
      vtime ModFrmHil:
      for i := 1 to #ords do
        ords[i]`thetas := [ThetaSeries(ords_lats[i,j], theta_prec) : j in js]; end for;
      vprint ModFrmHil, 3: "Theta series of the left orders are", &cat [LO`thetas : LO in ords];
    else // need js below (this is hacky)
      js := [1..#ords[1]`thetas];
      assert &and [#LO`thetas eq #js : LO in ords];
    end if;
    ords_thetas := [LO`thetas : LO in ords];
    // reset theta_prec to the minimum that distinguishes these pairs of (partial) theta series
    // TO DO: haven't done it properly for pairs 
    theta_prec := 1;
    for j := 1 to #ords_thetas[1] do 
      coeffs := [ [Coefficient(th,n) : n in [1..AbsolutePrecision(th)-1]] where th is thetas[j] 
                                                                         : thetas in ords_thetas ];
      coeffs := Sort(Setseq(Seqset(coeffs))); // sort the distinct thetas lexicographically
      for k := 2 to #coeffs do 
        i := Min([i : i in [1..#coeffs[k]] | coeffs[k-1][i] ne coeffs[k][i] ]); 
        theta_prec := Max(theta_prec, i);
      end for;
    end for;
    vprintf ModFrmHil, 2: "Using theta series to precision %o (the %o orders have %o distinct series)\n", 
                           theta_prec, #ords, #Seqset(ords_thetas);
    /* Also use the values of f2 on short vectors of f1 to distinguish pairs 
    ords_short_vals := [* *];
    vprintf ModFrmHil, 1: "Listing values on short vectors ... ", theta_prec; 
    vtime ModFrmHil, 1:
    for i := 1 to #ords_forms do 
      // look at the second positive integer that is represented by the first form
      // (no point considering the first because shortest vectors are exactly the units of norm 1)
      assert theta_prec lt 2*Degree(F) or Minimum(ords_lats[i,1]) eq 2*Degree(F); // just to make sure
      N := 2*Degree(F) + 1;
      while N le theta_prec do 
        if Coefficient(ords_thetas[i,1], N) gt 0 then break; end if;
        N +:= 1;
      end while;
      if N gt theta_prec or Coefficient(ords_thetas[i,1], N) gt 100 then 
        Append( ~ords_short_vals, {});
        continue i;
      end if;
      svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(ords_lats[i,1], N), sgn in [1,-1] ];
      //Append( ~ords_short_vals, Sort([ (sv*ords_forms[i,2]*Transpose(sv))[1,1] : sv in svs ]) );
      svs_vals := [ (sv*ords_grams[i]*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
      svs_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
      Append( ~ords_short_vals, svs_vals);
    end for; // i
ii := Min([i : i in [1..#ords] | #ords_short_vals[i] gt 0 ] cat [1]);
"The short values are (sample only): ", ords_short_vals[i]; 
    */
  end if; // use_theta

  // seems always faster to use_Jprime for the colon calculation 
  // instead of ColonInternal
  // However ... the basis obtained when we use_Jprime seems worse,
  // so the lattice enumeration step then takes longer, eg
  // around 20% longer for the real subfield of Q(zeta_25) of degree 10.
  // The enumeration cost dominates running time for degree > 8.
  use_Jprime := Degree(F) le 8; 
  if use_Jprime then  
    if debug then   // make sure ridls are integral ideals, as the Jprime trick assumes
      for J in ridls do assert &and [zb in OJ : zb in ZBasis(J)] where OJ is RightOrder(J); end for;
    end if;
    ps := LCM([NP] cat [Integers()| Norm(Norm(J)) : J in ridls ]); 
    vprintf ModFrmHil, 3: "Getting JJs ... ";  
    vtime ModFrmHil, 3:
    JJs := [ <JJ,b,P> where JJ,b,P is Jprime(J : coprime_to:=ps) : J in ridls ]; 
  end if;

    // (previously) loop over several Ps started here

    bool, tps := IsDefined(OH`RightIdealClasses[record_idx]`tps, P);
    if not bool then
      tps := AssociativeArray(CartesianProduct([1..h],[1..h]));
    end if;
      
    Pclass := P @@ ClFmap;
    Pclassrep := ClFreps[r] where r is Index(ClFelts, Pclass);
    bool, gP := IsNarrowlyPrincipal(P/Pclassrep : real_places:=real_places, 
                                    UnitRealValuations:=UnitRealValuations);  assert bool;
    gP := F!gP;
    function inds_for_j(j)
      b := ridls[j];
      NormbP := Norm(ridls[j])/P; // = Norm(bP) for each bP below
      NormbP_class := ridls_norms_classes[j] - Pclass;
      inds := [i : i in [1..h] | ridls_norms_classes[i] eq NormbP_class];
      return inds, b, NormbP, NormbP_class;
    end function;

    if eP eq 1 then
      vprintf ModFrmHil: "Getting tp's for prime of norm %o (using \"%o prime method\")\n", 
                          NP, small_prime select "small" else "large";
    else
      vprintf ModFrmHil: "Getting tp's for ideal of norm %o^%o (using \"%o prime method\")\n", 
                          NPP, eP, small_prime select "small" else "large";
    end if;
    IndentPush(); 

    if small_prime then  // quicker to run through subideals

      // Let I1, .., Ih denote the ridls.  
      // We need Ij < t^-1*Ii with norm-index P. 
      // Writing b for Ij, list the (NP+1) P-super-ideals bP of b.  
      // For each bP, find Ii and t with t*bP = Ii. 
      // Thus t is determined up to left mult by units of LeftOrder(Ii)

      for j in rows do
        inds, b, NormbP, NormbP_class := inds_for_j(j);
        vprintf ModFrmHil, 2: "Subideals"; 
        vtime ModFrmHil, 2:
        b_subideals := Subideals_of_ideal_newer(b, P : use_theta:=use_theta );
        vprintf ModFrmHil, 2: "Ideal isomorphism tests: "; time_iso := Cputime();
        numtests := 0;

        for bsub in b_subideals do 
          // Set bP := P^-1 * bsub
          bPCIs := [ Pinv*CI : CI in CoefficientIdeals(PseudoMatrix(bsub)) ] where Pinv is P^-1;
          bPmat := Matrix(PseudoMatrix(bsub));
          bP := rideal< OH | PseudoMatrix(bPCIs, bPmat) : Check:=debug >;
          if debug then assert Norm(bP) eq NormbP; 
          else bP`Norm := NormbP; end if; 
          // Figure out the class of bP as a right ideal of O
          // ie compute v in A, a in ridls such that  v*a = bP.
         /* TO DO: figure out whether this makes any sense, and fix syntax now that tps are arrays
          // Some hocus pocus to guess which inds are more likely:
          inds_nonzero := [i : i in inds | IsDefined(tps[<j,i>]) and #tps[<j,i>] gt 0]; // indices of ridls which already showed up
          if #inds_nonzero gt 0 then 
            // if some ridls tend to occur repeatedly, check those first; 
            // if they tend to occur at most once, check the others first
            avg_count := &+[#tps[<j,i>] : i in inds_nonzero] / #inds_nonzero;
            sgn := (avg_count gt 1.33 or #inds_nonzero eq 1) select 1 else -1; 
            Sort(~inds, func< i1,i2 | sgn*(#tps[<j,i2>]-#tps[<j,i1>]) >); 
          end if;
         */
          if use_theta then
            bsub_forms := [j[2],j[3]] where j is junk_for_IsIsomorphic(LeftOrder(bsub));
          //bsub_gram := T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
          //                                 where j is junk_for_IsIsomorphic(LeftOrder(bsub)); 
            bsub_lats := [ LatticeWithGram(f : CheckPositive:=false) : f in bsub_forms[js] ];
            vprintf ModFrmHil,3: "ThetaSeries ... "; 
            vtime ModFrmHil,3:
            bsub_thetas := [ ThetaSeries(L, theta_prec) : L in bsub_lats ];
  /* skip this for now, because it doesn't help with the Gross example (or indeed any example I've seen yet!)
    assert Minimum(bsub_lats[1]) eq 2*Degree(F);
            N := 2*Degree(F) + 1;
            while N le theta_prec do 
              if Coefficient(bsub_thetas[1], N) gt 0 then break; end if;
              N +:= 1;
            end while;
            if N gt theta_prec or Coefficient(bsub_thetas[1], N) gt 100 then 
              bsub_short_vals := {};
            else
              svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(bsub_lats[1], N), sgn in [1,-1] ];
              //bsub_short_vals := Sort([ (sv*bsub_forms[2]*Transpose(sv))[1,1] : sv in svs ]);
              svs_vals := [ (sv*bsub_gram*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
              bsub_short_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
            end if;
  */
          end if;
          found_class := false; 
          for i in inds do
            // quickly try to rule out some order classes (by looking at short vectors of the pair of forms)
            if use_theta then 
              io := order_indices[i];
              for j in js do
                if Valuation(bsub_thetas[j] - ords_thetas[io,j]) le theta_prec then 
                  continue i; 
                end if; 
              end for;
              /*
              if bsub_short_vals ne ords_short_vals[io] then
                "short vals don't match"; 
                continue i; 
              end if;
              */
            end if;
            numtests +:= 1;
            if use_Jprime then
              // scale to make ideal integral, since the Jprime trick assumes this
              bool, v := IsIsomorphicInternal(NP*bP, ridls[i] : real_places:=real_places,
                                                                UnitRealValuations:=UnitRealValuations,
                                                                JJ:=JJs[i] );
              if bool then v *:= NP; end if;
            else                                                         
              bool, v := IsIsomorphicInternal(bP, ridls[i] : real_places:=real_places,
                                                             UnitRealValuations:=UnitRealValuations );
            end if;
            if bool then
              if debug then assert ridls[i] eq v*bP; end if;
              ji := <j,i>;
              if IsDefined(tps, ji) then
                Append(~tps[ji], v); 
              else
                tps[ji] := [v]; 
              end if;
              error if found_class, "This ideal is in more than one class!!!\n", bP; // only caught in debug
              found_class := true; 
              if not debug then break i; end if;
            end if;
          end for; // i
          error if not found_class, "Failed to find isomorphism class for right ideal\n", bP;
        end for; // bsub
        vprintf ModFrmHil, 2: "needed %o tests; time for row = %o sec\n", numtests, Cputime(time_iso);

        for subI in b_subideals do  // these ideals are gonna get deleted, make sure stored data gets deleted too
         if assigned subI`LeftOrder then 
          delete subI`LeftOrder`junk_for_IsIsomorphic; end if; end for;
      
     end for; // j
   end if;
   if not small_prime then  // NP large relative to h ==> quicker to run through ideal classes

      // Let I1 .. Ih denote the ridls.  For each pair Ij, Ii, we list all t in H 
      // with t*Ij < Ii and Norm(t*Ij) = P*Norm(Ii), up to mult by scalars, 
      // and then choose reps for t modulo left mult by units of LeftOrder(Ii)

      ts_raw := []; // ts_raw[j] will contain raw ts for the jth row
     
      ridls_colonZBs := OH`RightIdealClasses[record_idx]`rids_colonZBs; 

      for j := 1 to h do 
        if j notin rows then
          Append(~ts_raw, [[] : i in [1..h]]);
          continue;
        end if;

        inds := inds_for_j(j);

        // Make sure we know Z-bases for (I:J)'s
        for i in inds do 
          // Get a totally positive generator g of the ideal (there exists one, for i in inds)
          if not IsDefined(ridls_colonZBs, <j,i>) then
            vprintf ModFrmHil,3: "Z-basis for I:J (%ousing the J' trick) ... ", 
                                                   use_Jprime select "" else "not "; 
            vtime ModFrmHil,3:
            if use_Jprime then 
              JJ, b := Explode(JJs[j]);  // [I : J] = I * J^-1 = I * JJ * b^-1
              IJJ_ZB := IntersectionZBasis(ridls[i], JJ);
              ridls_colonZBs[<j,i>] := [H| x*binv : x in IJJ_ZB ] where binv is b^-1;
            else
              icolonj := ColonInternal(PseudoMatrix(ridls[i],H), PseudoMatrix(ridls[j],H), H, true // left multipliers
                                       : Hermite:=false); 
              ridls_colonZBs[<j,i>] := ZBasis(icolonj, H);
            end if;
          end if;
        end for; // i in inds

        vprintf ModFrmHil, 2: "Doing row #%o:  ", j;
        time_row := Cputime();

        if debug then
          for i in inds do
            g := ridls_colon_norms_gens[j][i]*gP;
            assert g*OF eq Norm(ridls[i])/Norm(ridls[j])*P;
          end for;
        end if;

        ts_raw_j := [[] : i in [1..h]];
        for i in inds do
          g := ridls_colon_norms_gens[j][i] * gP;
          for u in pos_units_mod_norms[i] do
            bool, elts := has_element_of_norm(ridls_colonZBs[<j,i>], u*g : all);
            if bool then 
              Append(~ts_raw_j[i], elts); 
            end if;
          end for;
        end for;
        Append(~ts_raw, ts_raw_j); assert #ts_raw eq j;
       
        vprintf ModFrmHil, 2: "Time for row #%o: %o\n", j, Cputime(time_row);

      end for; // j

      OH`RightIdealClasses[record_idx]`rids_colonZBs := ridls_colonZBs; // update cache (note: this might use a lot of memory!)

      // We've computed ts_raw[j][i] for all (relevant) j and i
      // Now choose one from each orbit under left action of units

      // Choose well-defined reps mod +-1 
      function normalize(S)
        return {-s lt s select -s else s : s in S};
      end function;

      inds := [(j in rows) select inds_for_j(j) else [] : j in [1..h]];
      allinds := Seqset(&cat inds);
      noums := AssociativeArray(allinds);
      for i in allinds do 
        noumsi := ridls[i]`LeftOrder`norm_one_units_mod_scalars;
        assert Universe(noumsi) eq H;
        Exclude(~noumsi, H!1);
        Exclude(~noumsi, H!-1);
        noums[i] := noumsi;
      end for;

      vprintf ModFrmHil, 2: "Choosing representatives modulo left multiplication by units: ";
      vtime ModFrmHil, 2:

      for j in rows do
        for i in inds[j] do 
          ts := [H| ];
          for ie := 1 to #ts_raw[j][i] do 
            elts := ts_raw[j][i][ie]; 
            us := noums[i];
            // Discard repeats modulo left mult by the norm-one-units us;
            // here elts contains full orbits mod +-1,
            // and us are the units mod +-1
            length := 1+#us;
            if length eq 1 then
              ts cat:= elts;
            elif #elts eq length then
              Append(~ts, elts[1]);
            else
              elts := normalize(elts);
              while true do
                // assert #elts ge length;
                // assert #elts mod length eq 0;
                e1 := Rep(elts);
                Append(~ts, e1);
                if #elts eq length then
                  // the current elts form precisely one orbit
                  break;
                else
                  Exclude(~elts, e1);
                  orbit := normalize({H| u*e1 : u in us});
                  // assert orbit subset elts;
                  elts diff:= orbit;
                end if;
              end while;
            end if;
          end for; // ie

          if debug and small_prime then // this checks the two methods against eachother
            bool, tpsji := IsDefined(tps, <j,i>); assert bool;
            assert #ts eq #tpsji;
            for t in ts do 
              assert #[tt : tt in tpsji | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
            for t in tpsji do 
              assert #[tt : tt in ts | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
          end if;

          tps[<j,i>] := ts;
        end for; // i
      end for; // j

    end if; // small_prime
    IndentPop();

    // Sanity checks
    // (we really need the first check, it actually once failed for a huge prime p)
    keys := Keys(tps);
    for j in rows do
      assert &+ [#tps[<j,i>] : i in [1..h] | <j,i> in keys] eq num; 
    end for; 
    if debug then
      if rows eq [1..h] then
        tps0 := OH`RightIdealClasses[record_idx]`tps;
        tps_rows0 := OH`RightIdealClasses[record_idx]`tps_rows;
        TP := Matrix(h, [Integers()| IsDefined(tps,<j,i>) select #tps[<j,i>] else 0 : i,j in [1..h]]);
        for P0 in Keys(tps0) do
          if tps_rows0[P0] eq [1..h] then
            TP0 := Matrix(h, [Integers()| IsDefined(tps0[P0],<j,i>) select #tps0[P0][<j,i>] else 0 : i,j in [1..h]]);
            assert TP*TP0 eq TP0*TP;
          end if;
        end for; 
      end if;
    end if;

    OH`RightIdealClasses[record_idx]`tps[P] := tps;
    bool, old_rows := IsDefined(OH`RightIdealClasses[record_idx]`tps_rows, P);
    OH`RightIdealClasses[record_idx]`tps_rows[P] := bool select Sort(old_rows cat rows) else rows;

    // (previously) loop over several Ps ended here
    
  IndentPop();
  vprint ModFrmHil: "Precomputation time:", Cputime(time0);
end procedure;

//////////////////////   INITIALIZATIONS   /////////////////////////////

// Choose 'Support' for RightIdealClasses.
// Take primes not dividing Level(M), with extra properties as specified

function support_for_rids(M : norm_gt:=1, coprime_to:=1, num:=1)
  N := coprime_to * Level(M);
  OA := QuaternionOrder(M);
  ZF := BaseRing(OA);
  F := NumberField(ZF);
  ClF, cl := NarrowClassGroup(F);
  Support := [];
  S := sub<ClF| >;
  q := norm_gt;
  inc := 50;
  while true do
    primes := [Q : Q in PrimesUpTo(q+inc, F) | Norm(Q) gt q and Norm(Q+N) eq 1];
    //primes := [Q : Q in primes | IsPrime(Norm(Q))]; // only use degree 1 (why?)
    for Q in primes do 
      Qcl := Q @@ cl;
      if Qcl notin S or S eq ClF then
        S := sub<ClF| S, Qcl>;
        Append(~Support, Q);
        if #Support ge num and S eq ClF then 
          return Support; 
        end if;
      end if;
    end for;
    q +:= inc;
  end while;
end function;

// Access or compute right ideal classes
// !! ALWAYS ACCESS/CACHE THE RIGHT IDEAL REPS FOR M VIA THIS !!

function get_rids(M)
  if assigned M`rids then 
    return M`rids;
  elif assigned M`Ambient then
    return get_rids(M`Ambient);
  end if;

  OA := QuaternionOrder(M);
  OK := BaseRing(OA);
  one := 1*OK;
  N := Level(M);

  // Use stored rids if their support is prime to Level(M)
  if assigned OA`RightIdealClasses then
    for rec in OA`RightIdealClasses do 
      if forall {P : P in rec`support | P + N eq one} then
        M`rids := rec`rids;
        return M`rids;
      end if;
    end for;
  end if;

  // If stored rids have wrong support, convert them to rids with suitable support 
  if assigned OA`RightIdealClasses and #OA`RightIdealClasses gt 0 then
    supp1 := OA`RightIdealClasses[1]`support;
    rids1 := OA`RightIdealClasses[1]`rids;
    // convert_rids assumes support coprime to support of rids1
    // TO DO: what num to use here? using more than 1, to avoid deep searches (hopefully)
    support := support_for_rids(M : coprime_to := &*supp1, 
                                    num := Floor(Sqrt(Degree(OK))) );
    M`rids := convert_rids(rids1, support);
    return M`rids;
  end if;

  // Computing rids for OA for the first time
  support := support_for_rids(M : norm_gt:=1);
  M`rids := RightIdealClassesAndOrders(OA : Support:=support,
                                            compute_order_classes:=false);
  return M`rids;
end function;

// Access or compute the tps for p
// !! ALWAYS ACCESS STORED tps VIA THIS !!

forward get_tps_for_rids, convert_tps;

function get_tps(M, p : rows:=0)
  return get_tps_for_rids(QuaternionOrder(M), get_rids(M), p : rows:=rows);
end function;

function get_tps_for_rids(OA, rids, p : rows:=0)
  h := #rids;
  if rows cmpeq 0 then
    rows := [1..h];
  else
    assert Type(rows) eq SeqEnum and rows subset [1..h];
  end if;
  new_rows := rows;

  // Check if tps are cached for these rids
  // (Locating the rids_record this way is a silly vestigial thing)
  idx := 1; 
  while idx le #OA`RightIdealClasses do 
    rec := OA`RightIdealClasses[idx];
    if IsIdentical(rids, rec`rids) then
      if not assigned rec`tps then
        break;
      end if;
      bool, tps_p := IsDefined(rec`tps, p);
      if bool then 
        bool, old_rows := IsDefined(rec`tps_rows, p); assert bool;
        if rows subset old_rows then
          return tps_p;
        else
          new_rows := [i : i in rows | i notin old_rows];
        end if;
      end if;
      break;
    end if;
    idx +:= 1;
  end while;
  error if idx gt #OA`RightIdealClasses, "There should be a record for these rids!";

  if assigned rec`rids1 then
    // rids were converted from rids1, by left-multiplying by elts
    // (rids1 and rids_conversion are assigned together by convert_rids)
    rids1 := rec`rids1;
    elts := rec`rids_conversion;
    if debug then
      assert forall{i: i in [1..#rids] | rids[i] eq elts[i]*rids1[i]};
    end if;
    // Policy: always compute and cache tps on rids1 
    // because rids1 are likely to be used for most levels
    // (and usually the first record in OA`RightIdealClasses).
    // Don't cache the converted tps, they take far too much memory!
    tps1 := get_tps_for_rids(OA, rids1, p : rows:=rows);
    vprintf ModFrmHil, 2: "Converting tp's for prime of norm %o: ", Norm(p);
    vtime ModFrmHil, 2:
    tps := convert_tps(tps1, elts, rows);
    return tps;
  end if;

  // prepare record to be used in precompute_tps
  if not assigned rec`rids_colonZBs then
    rec`rids_colonZBs := AssociativeArray(CartesianProduct([1..h],[1..h]));
  end if;
  if not assigned rec`tps then 
    rec`tps := AssociativeArray(PowerIdeal(Order(p)));
    rec`tps_rows := AssociativeArray(PowerIdeal(Order(p)));
  end if;
  OA`RightIdealClasses[idx] := rec;

  precompute_tps(OA, p, rids, idx, new_rows); 
  // This caches them in OA`RightIdealClasses[idx]`tps[p], 
  //    and also updates OA`RightIdealClasses[idx]`tps_rows[p]

  return OA`RightIdealClasses[idx]`tps[p];
end function;

// Given tps1 for rids1, convert to tps for rids
// where rids[i] eq elts[i]*rids1[i]

function convert_tps(tps1, elts, rows)
  A := Universe(elts); 
  assert Type(A) eq AlgQuat;
  inv_elts := [A| 1/x : x in elts];
  h := #elts;
  tps := AssociativeArray(CartesianProduct([1..h],[1..h]));
  for j in rows, i in [1..h] do 
    ji := <j,i>;
    bool, tps1ji := IsDefined(tps1, ji);
    if bool then
      xi := elts[i];
      xj := inv_elts[j];
      tps[ji] := [A| xi * t * xj : t in tps1ji];
    end if;
  end for;
  return tps;
end function;

intrinsic DeleteHeckePrecomputation(O::AlgAssVOrd)
{This deletes stored data that is used to compute Hecke operators of Hilbert modular forms
(the data is computed during the precomputation phase, and is used for all spaces of forms 
over the same number field).  This does not delete the stored Hecke operators themselves.}

  if assigned O`RightIdealClasses then
    for i := 1 to #O`RightIdealClasses do 
      if assigned O`RightIdealClasses[i]`tps then
        for P in Keys(O`RightIdealClasses[i]`tps) do 
          Remove(~O`RightIdealClasses[i]`tps, P);
          Remove(~O`RightIdealClasses[i]`tps_rows, P);
        end for;
      end if;
    end for;
  end if;
end intrinsic;

intrinsic DeleteHeckePrecomputation(O::AlgAssVOrd, P::RngOrdIdl)
{"} // "
  if assigned O`RightIdealClasses then
    for i := 1 to #O`RightIdealClasses do 
      if assigned O`RightIdealClasses[i]`tps then
        Remove(~O`RightIdealClasses[i]`tps, P);
        Remove(~O`RightIdealClasses[i]`tps_rows, P);
      end if;
    end for;
  end if;
end intrinsic;
