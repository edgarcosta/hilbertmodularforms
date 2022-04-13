freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Interface functions for Quaternion Algebras
// September-October 2005, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// General use functions for associative algebras: compute the representation
// of an algebra on a free module.
//
//-------------

intrinsic RepresentationMatrix(a::AlgAssVOrdElt : Side := "Left") -> Mtrx
  {Returns the matrix representation of Side-multiplication by the element 
   a acting on its parent order.}

  if Side eq "Right" then
    return RightRepresentationMatrix(a);
  else
    return LeftRepresentationMatrix(a);
  end if;

end intrinsic;

intrinsic IsScalar(a::AlgAssElt) -> BoolElt, RngElt
  {Returns true (and R ! a) iff a belongs to the base ring R}

  A := Parent(a);
  F := BaseRing(A);
  require IsUnitary(A) : "A must have unity";
  Aone := A ! 1;
  Aoneseq := Eltseq(Aone);  

  i := 1;
  n := Dimension(A);
  while Aoneseq[i] eq 0 do
    i +:= 1;
  end while;
  c := a[i]/Aoneseq[i];
  if (a-c*Aone) ne 0 then
    return false, _;
  else
    return true, c;
  end if;
end intrinsic;

intrinsic RepresentationMatrix(a::AlgAssVElt, M::AlgAssV : Side := "Right")
  -> AlgMatElt
  {Returns the matrix representation of Side-multiplication by the element
   a in the associative algebra A on the A-module M.}

  if ISA(Type(M), AlgGrp) then
      M, m := Algebra(M);
      if ISA(Type(a), AlgGrpElt) then
	a := m(a);
      end if;
  end if;

  // use internal code (which is now correct) when M = A  
  if IsIdentical(M, Parent(a)) then 
    return RepresentationMatrix(a : Side:=Side);
  end if;

  EndM := EndomorphismRing(Module(M));
  // If M is a quaternion algebra, then the indexing is wrong
  M := AssociativeAlgebra(M); 

  // This is a brutal thing to do, and has no built-in error checking.
  // A more natural/elegant implementation of modules (or, really, ideals)
  // would make this more transparent, also it would avoid the need to
  // input Side
  if Side eq "Right" then
    return EndM ! &cat[Eltseq(M.i*a) : i in [1..Degree(EndM)]];
  else
    return EndM ! &cat[Eltseq(a*M.i) : i in [1..Degree(EndM)]];
  end if;
end intrinsic;

intrinsic MatrixAlgebra(A::AlgAssV, M::AlgAssV : Side := "Right") -> AlgMat, Map
  {Given a finite-dimensional R-algebra A and a (Side-)A-module M,
   (both free as R-modules,) return the matrix algebra End_A(M) and the 
   R-algebra homomorphism phi: A -> End_A(M).}
   
  d := Dimension(A);
  EndM := EndomorphismRing(Module(M));
  
  imgs := [RepresentationMatrix(A.i, M : Side := Side) : i in [1..d]];
  subEndM := sub<EndM | imgs>;
  
  // This gives a well-defined map, but it really should be a hom in
  // the category of algebras, in particular a linear map, so e.g. the
  // kernel, inverse can be computed.
  phi := hom<A -> subEndM | a :-> &+[Eltseq(a)[i]*imgs[i] : i in [1..d]]>;
  
  return subEndM, phi;
end intrinsic;

//-------------
//
// Algorithms to determine if an associative algebra is a quaternion algebra.
//
//-------------

// This function takes a 4-dimensional algebra A, 
// an element eps in A such that eps^2=0, 
// an element theta such that (eps*theta)^2 <> 0,
// and returns matrix units giving rise to an isomorphism A -> M_2(F).
function MatrixUnitsFromNilpotent(A, eps, theta);
  c := [Trace(theta), Norm(theta)];

  epstheta := eps*theta;  
  epsthetaseq := Eltseq(epstheta);
  i := 1;
  while i le 4 and IsWeaklyZero(epsthetaseq[i]) do
    i +:= 1;
  end while;
  error if i gt 4, "Error in MatrixUnitsFromNilpotent: eps*theta should not be zero";
  epsthetasqseq := Eltseq((epstheta)^2);
  t := epsthetasqseq[i]/epsthetaseq[i];
  epsp := (1/t)*eps;

  F := BaseField(A);
  // Hardcoded formulas: In the isomorphism to M_2(F), we have 
  //   epsp = [[0, 1], [0, 0]]
  // and
  //   theta = [[0, -c[2]], [1, c[1]].
  // The existence of the negative signs is specifically for the 
  // mixed-characteristic (0,2) case.

  E := [-c[1]*epsp + epsp*theta, epsp,
        -c[1] + (c[2]-c[1]^2)*epsp + theta + c[1]*epsp*theta,
        1 + c[1]*epsp - epsp*theta];
  return E;
end function;

// This function takes a 4-dimensional algebra A, 
// an element eps in A such that eps^2=0, 
// an element theta such that (eps*theta)^2 <> 0,
// and returns a standard representation A = (1,1 / F).
function StandardGeneratorsFromNilpotent(A, eps, theta);
  // c := [Trace(theta), Norm(theta)];
  cpol := MinimalPolynomial(theta); assert Degree(cpol) eq 2;
  c := [Coefficient(cpol,1), Coefficient(cpol, 0)]; // JV fix, Sep 2015

  epstheta := eps*theta;  
  epsthetaseq := Eltseq(epstheta);
  i := 1;
  while i le 4 and IsWeaklyZero(epsthetaseq[i]) do
    i +:= 1;
  end while;
  error if i gt 4, "Error in StandardGeneratorsFromNilpotent: eps*theta should not be zero";
  epsthetasqseq := Eltseq((epstheta)^2);
  t := epsthetasqseq[i]/epsthetaseq[i];
  epsp := (1/t)*eps;

  F := BaseField(A);
  // Hardcoded formulas: In the isomorphism to M_2(F), we have 
  //   epsp = [[0, 1], [0, 0]]
  // and
  //   theta = [[0, -c[2]], [1, c[1]].
  // The existence of the negative signs is specifically for the 
  // mixed-characteristic (0,2) case.

  if Characteristic(F) eq 2 or (Type(F) eq FldPad and Prime(F) eq 2) then
    alpha := theta+((-c[1]+1)*theta + (c[2]+1))*epsp;
    beta := theta-(c[1]+1)*theta*epsp + epsp*(c[2]-c[1]+theta);
  else
    alpha := epsp*theta-theta*epsp-c[1]*epsp;
    beta := theta+(-c[1]*theta+c[2]+1)*epsp;
  end if;

  return alpha, beta;
end function;

function MatrixRingInternal(A,eps,theta);
  eps0 := eps;

  // Optional specification of theta used for internal purposes; 
  // In particular, specification of theta implies eps^2 = 0
  if IsWeaklyZero(theta) then
    a := Trace(eps0);
    if not IsWeaklyZero(a) then
      for i := 1 to 3 do
        beta := A.i;
        if not IsWeaklyZero(beta*eps0-eps0*beta) then
          break i;
        end if;
      end for;
      eps0 := (eps0-a)*(Trace(eps0*beta)+a*beta);
    end if;

    for i := 1 to 3 do
      if not IsWeaklyZero(Trace(A.i*eps0)) then
        theta := A.i;
        break i;
      end if;
    end for;
  end if;

  E := MatrixUnitsFromNilpotent(A, eps0, theta);

  F := BaseField(A);
  M2F := MatrixRing(F,2);

  T := Matrix(F,4,4,[Eltseq(e) : e in E]);
  bool, Tinv := IsInvertible(T);
  if not bool then 
    error IsExact(BaseRing(Parent(T))) 
          select "Error in MatrixRing: matrix T is not invertible"
           else  "Error in MatrixRing: matrix T is not invertible -- try increasing Precision?";
                 // TO DO: automatically increase precision if called from pMatrixRing
  end if; 
  // This is an algebra map!  (A linear map!)
  phi := map<A -> M2F | theta :-> M2F ! Eltseq(Matrix(1,4,Eltseq(theta))*Tinv),
                        theta :-> A ! Eltseq(Matrix(1,4,Eltseq(theta))*T)>;

  return M2F, phi;
end function;  

intrinsic MatrixRing(A::AlgQuat, eps::AlgQuatElt) -> AlgMat, Map
  {Given a quaternion algebra A and a zerodivisor eps in A,
   returns the matrix algebra M_2(F) and an isomorphism
   A -> M_2(F).}

  require not IsZero(eps) and not IsInvertible(eps): "The second argument must be a zero divisor.";

  M2F, phi := MatrixRingInternal(A, eps, 0);
  return M2F, phi;
end intrinsic;

// See [Voight, Algorithm 4.2.9], [Voight2, Algorithm 1.2.3]

intrinsic IsQuaternionAlgebra(A::AlgGen) -> BoolElt, AlgQuat, Map
  {Returns true if and only if A is a quaternion algebra;
   if true, it returns the associated quaternion algebra and 
   an algebra homomorphism to it.}
 
  if not ISA(Type(A), AlgAss) then
    if not IsAssociative(A) then
      return false, _, _;
    else
      AA := AssociativeAlgebra(A);
      AtoAA := map< A -> AA | a :-> AA!a, a :-> A!a >;
      bool, QA, AAtoQA := IsQuaternionAlgebra(AA);
      if bool then
        return true, QA, AtoAA * AAtoQA;
      else
        return false, _, _;
      end if;
    end if;
  end if;

  if not IsUnitary(A) then
    return false, _, _;
  end if;
  Aone := A ! 1;

  // A quaternion algebra must be dimension 4 over a field
  if (Dimension(A) ne 4) or not IsField(BaseRing(A)) then
    return false, _, _;
  end if;
  
  Abasis := Basis(A);
  // Make the first basis element unity.
  if Aone ne Abasis[1] then
    Abasis := ExtendBasis([Vector(Aone)], Parent(Vector(Aone)));
  end if;
  F := BaseField(A);
  e := [A ! Abasis[i] : i in [1..4]];

  if Characteristic(F) eq 2 then
    t := [0] cat [(Vector(e[i]^2))[i] : i in [2..4]];

    if not &and[IsScalar(e[i]^2+t[i]*e[i]) : i in [2..4]] then
      return false, _, _;
    end if;
    if t eq [0,0,0,0] then
      return false, _, _;
    end if;

    if t[2] eq 0 then
      if t[3] ne 0 then
        alpha := e[3]/t[3];
      else
        alpha := e[4]/t[4];
      end if;
      e3star := e[2];
    else
      alpha := e[2]/t[2];
      e3star := e[3] + t[3]*alpha;
    end if;
    
    _, a := IsScalar(alpha^2+alpha);

    bl, c := IsScalar(e3star*alpha+(alpha+1)*e3star);
    if not bl then
      return false, _, _;
    end if;
    beta := e3star+c;

    bl, b := IsScalar(beta^2);
    if not bl or alpha*beta eq beta*alpha then
      return false, _, _;
    end if;

    if b eq 0 then
      if (e3star*e[4])^2 eq 0 then
        return false, _, _;
      else
        n4 := F ! (e[4]^2 + t[4]*e[4]);
        alpha, beta := StandardGeneratorsFromNilpotent(A, beta, e[4]);
        a := 1;
        b := 1;
      end if;
    else
      if a eq 0 then
        alpha +:= beta;
        a := b;
      end if;
    end if;
  else // F has characteristic not 2
    estar := [0] cat [e[i] - Trace(e[i])/4 : i in [2..4]];
    estarsq := [0] cat [estar[i]^2 : i in [2..4]];
    
    blout := true;
    estarsqout := [F ! 0];
    for i := 2 to 4 do
      bl, n := IsScalar(estarsq[i]);
      if not bl then
        blout := false;
        break i;
      else
        Append(~estarsqout, n);
      end if;
    end for;
    if not blout then
      return false, _, _;
    else
      estarsq := estarsqout;
    end if;

    if (estarsq[2] eq 0) then
      t23 := Trace(estar[2]*estar[3]);
      t24 := Trace(estar[2]*estar[4]);
      if t23 eq 0 and t24 eq 0 then
        return false, _, _;
      elif t23 ne 0 then
        alpha, beta := StandardGeneratorsFromNilpotent(A, estar[2], estar[3]);
      else
        alpha, beta := StandardGeneratorsFromNilpotent(A, estar[2], estar[4]);
      end if;
      a := 1;
      b := 1;
    else
      alpha := estar[2];
      a := estarsq[2];

      estar[3] -:= 1/(4*a)*Trace(estar[3]*alpha)*alpha;
      bl, b := IsScalar(estar[3]^2);
      if not bl then
        return false, _, _;
      end if;

      if b eq 0 then
        if Trace(estar[3]*estar[4]) eq 0 then
          return false, _, _;
        else
          alpha, beta := StandardGeneratorsFromNilpotent(A, estar[3], estar[4]);
          a := 1;
          b := 1;
        end if;
      else
        beta := estar[3];
        if alpha*beta eq beta*alpha then
          return false, _, _;
        end if;
      end if;
    end if;
  end if;

  if ISA(Type(F), FldAlg) then
    // Clear denominators; have to take squareroot because of the difference
    // between norm in the associative algebra and reduced norm in the quaternion
    // algebra.
    boo, d := IsSquare(Denominator(Norm(Norm(alpha))));
    assert boo;
    a *:= d^2;
    alpha *:= d;
    boo, d := IsSquare(Denominator(Norm(Norm(beta))));
    assert boo;
    b *:= d^2;
    beta *:= d;
  end if;

  T := Matrix(F,4,4,[Eltseq(Aone), Eltseq(alpha), Eltseq(beta), Eltseq(alpha*beta)]);
  Tinv := T^(-1);
  
  Aquat := QuaternionAlgebra<F | a, b>;
  
  // This is an algebra map!  (A linear map!)
  phi := map<A -> Aquat | theta :-> Aquat ! Eltseq(Matrix(1,4,Eltseq(theta))*Tinv),
                          theta :-> A ! Eltseq(Matrix(1,4,Eltseq(theta))*T)>;
  
  return true, Aquat, phi;
end intrinsic;

// Matrix algebra version added Feb 2010, SRD

intrinsic IsQuaternionAlgebra(A::AlgMat) -> BoolElt, AlgQuat, Map
{"} // "
  AA, AtoAA := Algebra(A);
  bool, QA, AAtoQA := IsQuaternionAlgebra(AA);
  if bool then
    return true, QA, AtoAA * AAtoQA;
  else
    return false, _, _;
  end if;
end intrinsic;

intrinsic StandardForm(A::AlgQuat) -> RngElt, RngElt, AlgQuat, Map
  {Returns values a,b such that A is isomorphic to the 
   quaternion algebra AA = (a,b /F), together with AA, 
   and the homomorphism from A to AA.}
  
  F := BaseField(A);

  // If A is in standard form, return A
  bool, a := IsCoercible(F, A.1^2);
  if bool then
    bool, b := IsCoercible(F, A.2^2);
    if bool then
      return a, b, A, hom< A->A | x:->x, x:->x >;
    end if;
  end if;

  Ass := AssociativeAlgebra(A);  
  A_to_Ass := hom< A -> Ass | Basis(Ass) >;
  
  _, AA, Ass_to_AA := IsQuaternionAlgebra(Ass);
  a := -Norm(AA.1);
  b := -Norm(AA.2);

  return F!a, F!b, AA, A_to_Ass * Ass_to_AA;
end intrinsic;

//-------------
//
// Bibliography
//
//-------------

/*

[Lam]
T.Y. Lam, A first course in noncommutative rings, 2nd ed., Graduate texts in mathematics, 
vol. 131, Springer-Verlag, New York, 2001.

[Voight] 
John Voight, Quadratic forms and quaternion algebras: Algorithms and arithmetic, Ph.D. thesis,
University of California, Berkeley, 2005.

[Voight2]
John Voight, Algorithms for quaternion algebras, preprint, 2006.

*/
