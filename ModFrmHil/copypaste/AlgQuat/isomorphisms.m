freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      ISOMORPHISM OF QUATERNIONS                    //
//                  -- ALGEBRAS, ORDERS, AND IDEALS --                //
//                        Created January 2001                        //
//                           by David Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose QuaternionIsomorphism, 2;

////////////////////////////////////////////////////////////////////////
//                        Isomorphism testing                         //
////////////////////////////////////////////////////////////////////////

intrinsic IsIsomorphic(A::AlgQuatOrd,B::AlgQuatOrd: FindElement:= false, ConnectingIdeal:= 0) -> BoolElt, Map, AlgQuatElt
   {True if and only if A and B are isomorphic as algebras.}

   K := QuaternionAlgebra(A);
   require K cmpeq QuaternionAlgebra(B) : 
      "Arguments must be orders in the same algebra.";

   R:= BaseRing(A);
   if Type(R) eq RngInt then
     if IsIndefinite(K) then return true, _, _; end if;
     val:= ReducedGramMatrix(A) eq ReducedGramMatrix(B);
   else
     R:= BaseRing(R);
     require IsField(R) and IsFinite(R) and Characteristic(R) ne 2 : "algebras must be over Z or F_q[X] with q odd";
     if IsIndefinite(K) then return true, _, _; end if;
     val:= Discriminant(A) eq Discriminant(B);
     val:= val and ReducedGramMatrix(A : Canonical) eq ReducedGramMatrix(B : Canonical);
   end if;

   if val and FindElement then
      h, t := Isomorphism(A,B);
      return true, h, t;
   end if;
   return val, _, _;
end intrinsic;

// wrapper around number field case, where this is implemented
function is_isomorphic_indefinite(I, J : left:=0)
  O := Order(I);  assert BaseRing(O) eq Integers();
  B := Algebra(O);
  a, b, Bstd, B_to_Bstd := StandardForm(B);
  QQ := NumberField(Polynomial([-1,1]) : DoLinearExtension);
  BB := QuaternionAlgebra<QQ | a,b>;
  B_to_BB := map<B -> BB | x :-> BB!Eltseq(B_to_Bstd(x)),
                           y :-> (Bstd!Eltseq(y))@@B_to_Bstd >;
  OO := Order([B_to_BB(x) : x in Basis(O)]);
  if left then
    II := lideal<OO | [B_to_BB(x) : x in Basis(I)]>;
    JJ := lideal<OO | [B_to_BB(x) : x in Basis(J)]>;
  else
    II := rideal<OO | [B_to_BB(x) : x in Basis(I)]>;
    JJ := rideal<OO | [B_to_BB(x) : x in Basis(J)]>;
  end if;
  bool, tt := IsIsomorphic(II,JJ);
  if bool then
    t := tt @@ B_to_BB;
    tbas := left select [ x*t : x in Basis(Order(I)) ]
                  else  [ t*x : x in Basis(Order(I)) ];
    h := hom< Order(I) -> Order(J) | x :-> &+[ x[i]*tbas[i] : i in [1..4] ] >;
    return true, h, t;
  else
    return false, _, _;
  end if;
end function;

function isprincQ(A, I, min)
  M:= BasisMatrix(I, A);
  L:= Lattice(M, GramMatrix(NormSpace(A)));
  if Minimum(L) eq 2*min then
    return true, A ! Eltseq(ShortestVectors(L : Max:= 1)[1]);
  end if;
  return false, _;
end function;

intrinsic IsLeftIsomorphic(I::AlgQuatOrdIdl[RngInt],J::AlgQuatOrdIdl[RngInt]) -> BoolElt, Map, AlgQuatElt
   {True if and only if I is isomorphic to J as an ideal over a 
   common left order.}

   require LeftOrder(I) cmpeq LeftOrder(J) : 
      "Arguments must have the same left order.";
   
   A:= Algebra(I);
   if not IsDefinite(A) then 
     return is_isomorphic_indefinite(I, J : left:=true);
   end if;
   nI:= Norm(I);

//   IJ := Conjugate(I)*J;
   IJ := rideal< RightOrder(J) | [ Conjugate(x) * y: x in Basis(I), y in Basis(J) ] >;
   ok, x:= isprincQ(A, IJ, nI * Norm(J));
   if ok then
     x:= x/nI;
     //assert J eq lideal< Order(J) | [ b*x: b in Basis(I) ] >;
     xinv:= x^-1;
     return true, hom< A -> A | a :-> a*x, b:-> b*xinv >, x;
   end if;
   return false, _, _;
end intrinsic;

intrinsic IsLeftIsomorphic(I::AlgQuatOrdIdl[RngUPol], J::AlgQuatOrdIdl[RngUPol]) -> BoolElt, Map, AlgQuatElt
{"} // "
  require LeftOrder(I) cmpeq LeftOrder(J) :
      "Arguments must have the same left order.";
  A:= Algebra(I);
  F:= BaseRing(BaseField(A));
  require IsField(F) and IsFinite(F) and IsOdd(Characteristic(F)) : "Only defined for F_q[X] with q odd";
  if not IsDefinite(A) then return true, _, _; end if;

  IJ:= Conjugate(I)*J;
  B:= ReducedBasis(IJ);
  nI:= Norm(I);

  if Normalize(Norm(B[1])) eq nI * Norm(J) then
    x:= B[1] / nI;
    //assert J eq lideal< Order(J) | [ b*x : b in Basis(I) ] >;
    xx:= x^-1;
    return true, map< A -> A | a:-> a*x, b:-> b*xx >, x;
  end if;
  return false, _, _;
end intrinsic;

intrinsic IsRightIsomorphic(I::AlgQuatOrdIdl[RngInt],J::AlgQuatOrdIdl[RngInt]) -> BoolElt, Map, AlgQuatElt
   {True if and only if I is isomorphic to J as an ideal over a 
   common right order.}

   require RightOrder(I) cmpeq RightOrder(J) : 
      "Arguments must have the same right order.";

   A:= Algebra(I);
   if not IsDefinite(A) then 
     return is_isomorphic_indefinite(I, J : left:=false);
   end if;

   nI:= Norm(I);
   //JI:= J*Conjugate(I);
   JI:= lideal< LeftOrder(J) | [ x*Conjugate(y) : x in Basis(J), y in Basis(I) ] >;
   ok, x:= isprincQ(A, JI, nI * Norm(J));
   if ok then
     x:= x/nI;
     //assert J eq rideal< Order(J) | [ x*b: b in Basis(I) ] >;
     xinv:= x^-1;
     return true, hom< A -> A | a :-> x*a, b:-> xinv*b >, x;
   end if;
   return false, _, _;
end intrinsic;

intrinsic IsRightIsomorphic(I::AlgQuatOrdIdl[RngUPol], J::AlgQuatOrdIdl[RngUPol]) -> BoolElt, Map, AlgQuatElt
{"} // "
  require RightOrder(I) cmpeq RightOrder(J) :
      "Arguments must have the same right order.";
  A:= Algebra(I);
  F:= BaseRing(BaseField(A));
  require IsField(F) and IsFinite(F) and IsOdd(Characteristic(F)) : "Only defined for F_q[X] with q odd";
  if not IsDefinite(A) then return true, _, _; end if;

  JI:= J*Conjugate(I);
  B:= ReducedBasis(JI);
  nI:= Norm(I);

  if Normalize(Norm(B[1])) eq Norm(J) * nI then
    x:= B[1] / nI;
    //assert J eq rideal< Order(J) | [ x*b : b in Basis(I) ] >;
    xx:= x^-1;
    return true, map< A -> A | a:-> x*a, b:-> xx*b >, x;
  end if;
  return false, _, _;
end intrinsic;

intrinsic IsIsomorphic(I::AlgQuatOrdIdl, J::AlgQuatOrdIdl) -> BoolElt, AlgQuatElt
{Returns true iff I,J are isomorphic (left or right) ideals (ie, whether I and J are in
 the same left or right ideal class), and if so, also returns an element x such that J = x*I (or I*x).}
  require Order(I) cmpeq Order(J): "The arguments must be ideals with the same order";

  if IsLeftIdeal(I) and IsLeftIdeal(J) then
    ok, _, x:= IsLeftIsomorphic(I, J);
  else
    require IsRightIdeal(I) and IsRightIdeal(J) :
           "Ideals must both be left ideals or both be right ideals";
    ok, _, x:= IsRightIsomorphic(I, J);
  end if;
  if ok then return true, x; end if;
  return false, _;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                          Isomorphisms                              //
////////////////////////////////////////////////////////////////////////

intrinsic Isomorphism(A::AlgQuatOrd[RngInt],B::AlgQuatOrd[RngInt]) -> Map, AlgQuatElt
   {Given two isomorphic definite quaternion orders S and T, returns
    an isomorphism as algebras}

   K := QuaternionAlgebra(A);

   require K eq QuaternionAlgebra(B) : 
      "Arguments must be orders in the same algebra.";
   L := LatticeWithGram(GramMatrix(A));
   M := LatticeWithGram(GramMatrix(B));
   val, T := IsIsometric(L,M);
   require val : "Arguments must be isomorphic.";
   Q := [ A!Eltseq(T[i]) : i in [1..4] ];
   // Ensure that 1 :-> 1.
   // This assumes the first basis elements of A and B are 1, 
   // which hasn't been the case since 2005
   //u := A!Q[1];
   u := A!Eltseq( Vector(Integers(),Eltseq(B!1)) * T );  
   if u ne 1 then 
      assert IsUnit(u);
      vprintf QuaternionIsomorphism : 
         "Lattice isometry off by unit u = %o of argument 1.\n", u;
      vprint QuaternionIsomorphism : 
         "MinimalPolynomial(u) =", MinimalPolynomial(u);
      Q := [ uu*x : x in Q ] where uu is u^-1;
      T := Matrix(4,4,&cat[ Eltseq(x) : x in Q ]);
   end if;
   S := T^-1;
   P := [ B!Eltseq(S[i]) : i in [1..4] ];
   U := BasisMatrix(A)^-1*S*BasisMatrix(B);
   h := hom< A -> B | x :-> &+[ x[i]*P[i] : i in [1..4] ], 
                      y :-> &+[ y[i]*Q[i] : i in [1..4] ] >;
   // Ensure that h is a homomorphism, not an anti-homomorphism.
   //if h(A.1)*h(A.2) ne h(A.1*A.2) then
   if Determinant(U) eq -1 then 
      vprint QuaternionIsomorphism :
         "Isometry not an isomorphism, taking conjugates.";
      Q := [ Conjugate(x) : x in Q ];
      T := Matrix(4,4,&cat[ Eltseq(x) : x in Q ]);
      S := T^-1;
      P := [ B!Eltseq(S[i]) : i in [1..4] ];
      h := hom< A -> B | x :-> &+[ x[i]*P[i] : i in [1..4] ], 
                         y :-> &+[ y[i]*Q[i] : i in [1..4] ] >;
      U := BasisMatrix(A)^-1*S*BasisMatrix(B);
   end if;
   assert Determinant(U) eq 1;
   fac := Factorization(CharacteristicPolynomial(U));
   if GetVerbose("QuaternionIsomorphism") ge 1 then
      printf "Factored charpoly: \n%o\n", fac;
   end if;
   // Characteristic polynomial is (X-1)^2*G(X). 
   if #fac eq 1 then 
      // Characteristic polynomial of U is (X-1)^4, return identity.
      x := K ! 1;
   elif Degree(fac[2][1]) eq 1 then
      V := Kernel(U-1);
      x := K!Basis(V)[2];
      x -:= K!Trace(x)/2;
      x *:= K!Denominator(Norm(x));   
   else 
      chi := fac[2][1];
      V1 := Kernel(U-1);
      V2 := Kernel(Evaluate(chi,U));
      if GetVerbose("QuaternionIsomorphism") ge 1 then
         printf "Kernel(U-1) =\n%o\n", V1;
         print "chi =", chi;
         print "Kernel(Evaluate(chi,U)) =", Kernel(Evaluate(chi,U));
      end if;
      // Let x be a non-central element of Kernel(U-1),
      // y any element of Kernel(chi(U)), and z = y*U.
      // Solve for c such that (x+c)^-1*y*(x + c) = z.
      // ==> c*(y-z) = (x*z - y*x).
      x := K!Basis(V1)[2];
      y := K!Basis(V2)[1];
      z := K!(Basis(V2)[1]*U);
      x +:= (x*z-y*x)/(y-z);
      x *:= K!Denominator(Norm(x));   
   end if;
   if GetVerbose("QuaternionIsomorphism") ge 1 then
      xx := x^-1;      
      assert &and[ xx*y*x in B : y in Basis(A) ];     
      assert &and[ x*y*xx in A : y in Basis(B) ]; 
   end if;
   return h, x;
end intrinsic;


intrinsic Isomorphism(S::AlgQuatOrd[RngUPol], T::AlgQuatOrd[RngUPol]) -> Map, AlgQuatElt
{"} // "
  A:= Algebra(S);
  require A cmpeq Algebra(T) : "The orders must be in the same algebra.";

  require IsDefinite(A) : "The algebra must be definite.";

  G1:= ReducedGramMatrix(S : Canonical);
  G2:= ReducedGramMatrix(T : Canonical);
  require G1 eq G2 : "The orders are not conjugate";

  B1:= ReducedBasis(S : Canonical);
  B2:= ReducedBasis(T : Canonical);
  B:= Basis(A);
  K:= Kernel(Matrix( [ &cat[ Eltseq(B1[i]*b - b*B2[i]) : i in [2..4] ] : b in B ] ));
  if Dimension(K) eq 0 then
    K:= Kernel(Matrix( [ &cat[ Eltseq(B1[i]*b + b*B2[i]) : i in [2..4] ] : b in B ] ));
    assert Dimension(K) eq 1;
  end if;
  x:= A ! Eltseq(K.1);
  assert S^x eq T;
  
  xx:= x^-1;
  return map< A -> A | a :-> xx*a*x, b:-> x*b*xx >, x;
end intrinsic;


intrinsic LeftIsomorphism(I::AlgQuatOrdIdl,J::AlgQuatOrdIdl) -> Map, AlgQuatElt
   {Given two isomorphic left ideals over a definite order S over Z or F_q[X],
    returns the S-module isomorphism between them, followed by the
    quaternion algebra element which defines the isomorphism by right-multiplication}

   K := QuaternionAlgebra(Order(I));
   require K cmpeq QuaternionAlgebra(Order(J)) : 
      "Arguments must be ideals in the same algebra.";
   require IsDefinite(K) :
      "Arguments must be ideals in a definite quaternion algebra.";
   require LeftOrder(I) eq LeftOrder(J) : 
      "Arguments must have the same left order.";
   val, h, t := IsLeftIsomorphic(I,J);
   require val : "Arguments must be isomorphic as left ideals.";
   return h, t;
end intrinsic;

intrinsic RightIsomorphism(I::AlgQuatOrdIdl,J::AlgQuatOrdIdl) -> Map, AlgQuatElt
   {Given two isomorphic right ideals over a definite order S over Z or F_q[X],
    returns the S-module isomorphism between them, followed by the
    quaternion algebra element which defines the isomorphism by left-multiplication}

   K := QuaternionAlgebra(Order(I));
   require K cmpeq QuaternionAlgebra(Order(J)) : 
      "Arguments must be ideals in the same algebra.";
   require IsDefinite(K) :
      "Arguments must be ideals in a definite quaternion algebra.";
   require RightOrder(I) eq RightOrder(J) : 
      "Arguments must have the same right order.";
   val, h, t := IsRightIsomorphic(I,J);
   require val : "Arguments must be isomorphic as right ideals.";
   return h, t;
end intrinsic;

