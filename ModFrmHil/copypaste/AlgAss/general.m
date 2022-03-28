freeze;

// This function assumes that E is a field!!!
function identify_field(E)
  F:= BaseRing(E);
  d:= Dimension(E);
  if d eq 1 then return hom< F -> E | >; end if;
  B:= Basis(E);
  P:= PolynomialRing(F);

  // add more if you want
  if Type(F) in {FldRat, FldFunRat, FldFun} or ISA(Type(F), FldAlg) then
    rand:= func< F, r | Random(F, r) >;
  elif Type(F) eq FldFin then
    rand:= func< F, r | Random(F) >;
  else
    error "Base field is not supported";
  end if;

  repeat
    x:= &+[ rand(F, 10) * b : b in B];
    m:= P ! MinimalPolynomial(x);
    if m mod P.1 eq 0 then
      m div:= P.1;
    end if;
  until Degree(m) eq d;
  K:= ext< F | m >;
  return hom< K -> E | x >;
end function;

// This function assumes that A is simple
function algebra_over_center(A)
  mats:= Type(A) eq AlgMat;
  B:= Basis(A);
  C:= Center(A);
  F:= BaseRing(A);
  h:= identify_field(C); K:= Domain(h);
  CB:= [ x @ h : x in Basis(K) ];
  m:= #CB;
 
  BB:= [ ];
  BK:= [];
  V:= VectorSpace(F, mats select Degree(A)^2 else Dimension(A) );
  W:= sub< V | >;
  i:= 0;
  while #BB ne #B do
    repeat
      i+:= 1;
      x:= Vector(F, Eltseq(B[i]));
     until x notin W;
    Append(~BK, B[i]);
    BB cat:= [ b*B[i]: b in CB ];
    W:= sub< V | [Eltseq(x) : x in BB] >;
  end while;

  // get structure constants over K
  T:= Matrix(F, [ Coordinates(A, b) : b in BB ] )^-1;
  SC:= [ [ [ K ! x : x in Partition(Eltseq(Vector(F, Coordinates(A, c*b)) * T), m) ] : b in BK ] : c in BK ];

  AA:= AssociativeAlgebra< K, #SC | SC >;
  hh:= map< A -> AA | x:-> [ (K ! P[i]) : i in [1..#P] ] where P:= Partition(Eltseq(Vector(F, Eltseq(Coordinates(A, x))) * T), m),
                      y:-> &+ [ BB[i] * e[i] : i in [1..#BB] ] where e:= &cat [ Eltseq(x) : x in Eltseq(y) ] >;

  return AA, hh;
end function;

intrinsic AlgebraOverCenter( A :: Alg ) -> AlgAss, Map
{Given a simple algebra A with center K, returns a K-isomorphic K-algebra B and a K-isomorphism from A to B}
  F:= BaseRing(A);
  T:=  Type(A);
  require T eq AlgMat or ISA(T, AlgAss) : "The algebra must be of type AlgAss, AlgMat or AlgClff";
  require IsField(F) : "Base ring must be a field";
  require #CentralIdempotents(A) eq 1 : "The algebra is not simple";
  if Dimension(Center(A)) eq 1 then 
    if T eq AlgAss then
      return A, hom< A -> A | x:-> x, y:-> y >;
    elif T eq AlgMat then
      return Algebra(A);
    else
      B:= AssociativeAlgebra(A);
      return B, Coercion(A, B);
    end if;
  end if;
  return algebra_over_center(A); 
end intrinsic;

function restrict_scalars(A, F, K)
    C := CoefficientField(K);

    dA := Dimension(A);
    dK := Degree(K);
    dd := dA*dK;
    V := VectorSpace(C, dd);

/*
    sc := [];
    for i in [0 .. dd-1] do
	Vi := [Zero(K) : k in [1 .. dA]];
	Vi[i div dK + 1] := K.1^(i mod dK);
	Vi := A!Vi;
	for j in [0 .. dd - 1] do
	    Vj := [Zero(K) : k in [1 .. dA]];
	    Vj[j div dK + 1] := K.1^(j mod dK);
	    Vj := A!Vj;
	    Vij := Vi*Vj;
	    Vij := &cat[Eltseq(v) : v in Eltseq(Vij)];
	    while Universe(Vij) ne F do
		Vij := &cat[Eltseq(v) : v in Eltseq(Vij)];
	    end while;
	    Append(~sc, Vij);
	end for;
    end for;
sc;
#sc;
*/

    sc := [[] : i in [1 .. dd]];
    basis_prods := BasisProducts(A);
    rep_mat_1 := RepresentationMatrix(K!1, F);
    rep_mat_dK := RepresentationMatrix(K.1^dK, F);
    for i in [0 .. dA-1] do
	bpi := basis_prods[i +1];
	for j in [0 .. dA-1] do
	    bpij := bpi[j +1];
	    for k in [0 .. dK-1] do
		rm := rep_mat_1;
		for l in [0 .. dK-1] do
		    klm := k + l;
		    if klm ge dK then
			rm := rep_mat_dK;
		    end if;
		    klm := klm mod dK + 1;
//i*dK+k, j*dK + l;
//i, j, k, l, klm;
		    // Structure constants may only lie in the number field
		    // so they may not be scalars to this multiplication
		    sc[i*dK + k+1][j*dK + l+1] := &cat[Eltseq(rm[klm]*RepresentationMatrix(K!_sc, F)) : _sc in Eltseq(bpij)];
		end for;
	    end for;
	end for;
    end for;

    if ISA(Type(A), AlgAss) then
	B := AssociativeAlgebra<V | sc>;
    else
	B := Algebra<V | sc>;
    end if;

    m := map<A -> B | x :-> B!&cat[Eltseq(K!v) : v in Eltseq(x)], 
		    y :-> A![BaseRing(A)!K!v[k*dK+1..(k+1)*dK] : k in [0 .. dA-1]] where 
		    						v is Eltseq(y)>;
    return B, m;

end function;

function restrict_scalars_FldNum(A, F)
    KA := BaseRing(A);
    K := RelativeField(NumberField(F), NumberField(KA));
    return restrict_scalars(A, F, K);
end function;

function restrict_scalars_FldFun(A, F)
    KA := BaseRing(A);
    K := UnderlyingField(KA, F);
    return restrict_scalars(A, F, K);
end function;

intrinsic RestrictionOfScalars(A::AlgAss[FldAlg]) -> AlgAss, Map
{Given an algebra A over a number field compute an isomorphic algebra over the coefficient field of the number field}
    return restrict_scalars_FldNum(A, BaseField(BaseRing(A)));
end intrinsic;

intrinsic RestrictionOfScalars(A::AlgAss[FldFun]) -> AlgAss, Map
{Given an algebra A over a function field compute an isomorphic algebra over the coefficient field of the function field}
    return restrict_scalars_FldFun(A, BaseField(BaseRing(A)));
end intrinsic;

intrinsic RestrictionOfScalars(A::AlgAss[FldAlg], F::Fld) -> AlgAss, Map
{Given an algebra A over a number field compute an isomorphic algebra over the coefficient field F of the number field}
    require ISA(Type(F), FldAlg) or Type(F) eq FldRat : "Argument 2 is not a coefficient field of the base field of Argument 1";

    require AbsoluteDegree(BaseField(A)) mod AbsoluteDegree(F) eq 0 : "Argument 2 is not a coefficient field of the base field of Argument 1";

    return restrict_scalars_FldNum(A, F);
end intrinsic;

intrinsic RestrictionOfScalars(A::AlgAss[FldFun], F::FldFunG) -> AlgAss, Map
{Given an algebra A over a function field compute an isomorphic algebra over the coefficient field F of the function field}

    require AbsoluteDegree(BaseField(A)) mod (AbsoluteDegree(F) eq Infinity() select 1 else AbsoluteDegree(F)) eq 0 : "Argument 2 is not a coefficient field of the base field of Argument 1";

    return restrict_scalars_FldFun(A, F);
end intrinsic;

/*
P<x> := PolynomialRing(QuadraticField(23));
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3,b>;
A := AssociativeAlgebra(A);
RestrictionOfScalars(A);
RestrictionOfScalars(A, Rationals());
*/
