freeze;

/*****************************************************************************

  Hecke operators on spaces of modular forms over number fields.

  (Linear algebra routines for Hecke modules over number fields.)

  Steve Donnelly, last modified November 2013

*****************************************************************************/

import "hackobj.m" : Ambient, 
                     TopAmbient,
                     HMF0, 
                     IsBianchi, 
                     BMF_with_ambient,
                     set_quaternion_order;

import "definite.m" : BasisMatrixDefinite,
                      EisensteinBasis,
                      HeckeOperatorDefiniteBig,
                      AtkinLehnerDefiniteBig,
                      DegeneracyDown1DefiniteBig,
                      DegeneracyDownpDefiniteBig;

debug := false;

please_report :=
"\nPlease send this example to magma-bugs@maths.usyd.edu.au" *
"\n\nHint: to print the entire input of this session, type %P\n";

/**************************************************************************************/

// Use ONLY for situations where the search for a single generator of the hecke algebra
// gets badly stuck

declare attributes ModFrmHil: UseHardHeckeGenerator; // positive integer

/**************************************************************************************/

// TEMP ONLY --- TO DO

declare attributes FldNum: SplittingField; // = <L, rts> as returned by SplittingField

// OldSpaceAlgorithm := "degeneracy"; 
// "degeneracy" : use degeneracy maps when available
// or "naive"   : use linear algebra method always
// TO DO: probably make this a user option.  By default, choose intelligently
// depending on the space.  Note: degeneracy is not always better, since it 
// requires full tp's for primes dividing the level, so for large prime level
// will take time.  But naive involves worse linear algebra, which will blow up
// horribly for large dimension (sub)spaces.

/**************************************************************************************/

function make_ideal(x)
  case Type(x) :
    when RngIntElt : return x*Integers();
    when FldRatElt : return (Integers()!x)*Integers();
    else           : return x;
  end case;
end function;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

function hecke_matrix_field(M)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
    return Ambient(M)`weight_base_field;
  end if;
end function;

// The natural field over which Hecke operators can be expressed.

function minimal_hecke_matrix_field(M)
  bool, minimal := HasAttribute(M, "hecke_matrix_field_is_minimal");
  if bool and minimal then
    H := M`hecke_matrix_field;
  elif assigned M`Ambient then
    H := minimal_hecke_matrix_field(M`Ambient);
  elif IsParallelWeight(M) then
    H := Rationals();
  else
    vprintf ModFrmHil: "Figuring out the \'Hecke matrix field\' ... "; 
    time0 := Cputime();

    // The field where they currently live was created as an ext of Kgal.
    // The hecke_matrix_field is the subfield of Kgal corresponding to
    // the subgroup of the Galois group that fixes Weight(M).
    K := BaseField(M);
    assert assigned K`SplittingField; // WeightRepresentation should set it 
    Kgal, rts := Explode(K`SplittingField);
    assert IsAbsoluteField(Kgal);
    Aut, _, Autmap := AutomorphismGroup(Kgal);
    // figure out the Galois group as a permutation group acting on rts
    Sym := SymmetricGroup(AbsoluteDegree(K));
    gens := [Aut.i@Autmap : i in [1..Ngens(Aut)]];
    images := [Sym| [Index(rts, r@a) : r in rts] : a in gens];
    G := sub< Sym | images >;
    Aut_to_G := hom< Aut -> G | images >;
    act := func< w,g | [w[i] : i in Eltseq(g^-1)] >;
    Gw := sub< G | [g : g in G | act(w,g) eq w] > where w is Weight(M);
    Gw_in_Aut := sub< Aut | [h@@Aut_to_G : h in Generators(Gw)] >;
    H := FixedField(Kgal, Gw_in_Aut);  

    vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  end if;
  return H;
end function;

function basis_is_honest(M)
  return assigned M`basis_is_honest and M`basis_is_honest
         or assigned M`basis_matrix and not assigned M`Ambient;
         // (an ambient is automatically honest)
end function;

// For Fuchsian group Gamma, return a basis matrix for the plus subspace 
// of HeckeMatrix(Gamma, "Infinity") 

function basis_of_plus_subspace(M) 
  Gamma := FuchsianGroup(QuaternionOrder(M));
  N := Level(M) / make_ideal(Discriminant(QuaternionOrder(M)));
  T := HeckeMatrix(Gamma, N, "Infinity");
  if T cmpeq [] then 
    T := Matrix(Integers(), 0, 0, []); 
  end if;
  T := ChangeRing(T, Integers());
  plus_basis := KernelMatrix(T-1);
  plus_basis := ChangeRing(plus_basis, Rationals()); 
  minus_basis := KernelMatrix(T+1);
  minus_basis := ChangeRing(minus_basis, Rationals()); 
  assert Nrows(plus_basis) + Nrows(minus_basis) eq Nrows(T);

  return plus_basis, minus_basis;
end function;


// Given matrices B and C specifying complementary row spaces
// return a matrix Binv satisfying B*Binv = identity, C*Binv = zero

function pseudo_inverse(B, C)
  BC := VerticalJoin(B,C); 
  assert Nrows(BC) eq Ncols(BC);

  verbose := false and IsVerbose("ModFrmHil", 2) and Nrows(BC) ge 500;
  if verbose then
     printf "Finding pseudo-inverse:";
     t0 := Cputime();
  end if;

  I := IdentityMatrix(BaseRing(B), Nrows(B));
  O := ZeroMatrix(BaseRing(C), Nrows(C), Nrows(B));
  IO := VerticalJoin(I,O);
  Binv := Transpose(Solution(Transpose(BC), Transpose(IO)));

  if verbose then
     printf " %o\n", Cputime(t0); 
  end if;

  return Binv;
end function;


// Main function to trigger explicit computation of a space M 

function basis_matrix(M)
  if not assigned M`basis_matrix then

    assert not IsBianchi(M);

    // Determine method for computing M, if not already known
    QO := QuaternionOrder(M);
    ambient := not assigned M`Ambient;

    rel_level := NewLevel(M) / make_ideal(Discriminant(QO));
    assert ambient eq IsOne(rel_level);

    if IsDefinite(M) and ambient then
        _ := BasisMatrixDefinite(M);

    elif IsDefinite(M) and 
         (Seqset(Weight(M)) eq {2} or IsSquarefree(rel_level)) 
    then
        _ := BasisMatrixDefinite(M);

    elif not IsDefinite(M) and ambient then
        plus_basis, minus_basis := basis_of_plus_subspace(M);
        M`basis_matrix := plus_basis;
        M`basis_matrix_inv := pseudo_inverse(plus_basis, minus_basis);
        // TO DO: M`basis_is_honest, right?

    else
        MA := M`Ambient;
        _ := basis_matrix(MA);
        // If MA is honest and we know its inner product, 
        // then we can find an honest basis for M  
        useIP := false;
        if basis_is_honest(MA) then
            try 
                IP := InnerProductMatrix(MA);
                useIP := true;
            catch ERROR
                if "implemented" notin ERROR`Object then 
                    error ERROR`Object;
                end if;
            end try;
        end if;
        vprintf ModFrmHil: 
            "Using naive method to determine new subspace (%ousing inner product)\n", 
             useIP select "" else "not ";
        V := VectorSpace(hecke_matrix_field(MA), Dimension(MA));
        C := sub< V | >;
        if useIP then
            for pp in Factorization(NewLevel(M)/NewLevel(MA)) do
                C +:= NewAndOldSubspacesUsingHeckeAction(MA, pp[1] : OldOnly);
            end for;
            vprintf ModFrmHil, 2: "Computing new space as orthogonal complement of old space: "; 
            vtime ModFrmHil, 2:
            V := Kernel(Transpose(BasisMatrix(C)*IP));
        else
            for pp in Factorization(NewLevel(M)/NewLevel(MA)) do
                new, old := NewAndOldSubspacesUsingHeckeAction(MA, pp[1]);
                V meet:= new;
                C +:= old;
            end for;
        end if;
        R := BaseRing(MA`basis_matrix);
        bm_new := ChangeRing(BasisMatrix(V), R);
        bm_old := ChangeRing(BasisMatrix(C), R);
        M`basis_matrix_wrt_ambient := bm_new;
        M`basis_matrix_wrt_ambient_inv := pseudo_inverse(bm_new, bm_old);
        M`basis_matrix := M`basis_matrix_wrt_ambient * MA`basis_matrix;
        M`basis_matrix_inv := MA`basis_matrix_inv * M`basis_matrix_wrt_ambient_inv;
        M`basis_is_honest := useIP;
/*
 // for testing degeneracy (select the naive method above)
 bm := M`basis_matrix;
 delete M`basis_matrix;
 delete M`basis_matrix_inv;
 delete M`basis_is_honest;
 _ := BasisMatrixDefinite(M);
 assert RowSpace(bm) eq RowSpace(M`basis_matrix);
*/
    end if;

    if assigned M`Dimension then 
      error if M`Dimension ne Rank(M`basis_matrix),
           "\nA serious error has been detected (dimension is wrong!)\n" * please_report;
    else
      M`Dimension := Rank(M`basis_matrix);
    end if;

  end if;

  bool, bmi := HasAttribute(M, "basis_matrix_inv");
  if bool then
    return M`basis_matrix, bmi;
  else
    return M`basis_matrix, _;
  end if;
end function;


function restriction(M, T)
  bm, bmi := basis_matrix(M);
  bmT := bm * ChangeRing(T, BaseRing(bm));
  if assigned bmi then
    TM := bmT * bmi;
  else
    // solve bm * TM = bmT
    TM, K := Solution(bm, bmT);
    assert Dimension(K) eq 0;
  end if;
  return TM;
end function;


////////////////////////////////////////////////////////////////////////////////////////
// Interface for operators (handles caching and calls the appropriate raw function)
////////////////////////////////////////////////////////////////////////////////////////

function checks(M, _p, op)
  p := make_ideal(_p);

  if not (ISA(Type(p), RngOrdIdl) and NumberField(Order(p)) eq BaseField(M)) 
     and not (Type(p) eq RngInt and BaseField(M) eq Rationals()) 
  then
    return false, "The second argument should be an ideal of the base field of the first argument", p;
  end if;

  if IsBianchi(M) then
    if op eq "Hecke" then
      return true, _, p;
    else
      return false, "Not implemented for spaces of Bianchi forms", p;
    end if;
  end if;
    
  if op notin {"Hecke", "AL"} and not IsDefinite(M) then
    return false, "Operator not implemented (for spaces computed with the indefinite algorithm)", p;
  end if;

  if op ne "AL" and not IsPrime(p) then
    return false, "The second argument must be prime", p;
  end if;

  if op ne "Hecke" then
    // must divide the Eichler level
    if not Level(M) subset p * make_ideal(Discriminant(QuaternionOrder(M))) then
      if not Level(M) subset p then
        return false, "The second argument must divide the level of the space", p;
      end if;
      return false, "Operator not implemented in this case (ideal is not coprime to the"
                   *" discriminant of the quaternion order used to compute this space)", p;
    end if;
    if op ne "AL" and Seqset(Weight(M)) ne {2} then
      return false, "Operator is currently implemented only for parallel weight 2", p;
    end if;
  end if;

  return true, _, p;
end function;

function operator(M, p, op)
  assert op in {"Hecke", "AL", "DegDown1", "DegDownp"};

  // Check if cached on M
  cached, Tp := IsDefined(eval "M`"*op, p);
  if cached then 
    return Tp;
  end if;

  if Dimension(M : UseFormula:=false) eq 0 then // gets cached dimension or computes the space

    Tp := ZeroMatrix(Integers(), 0, 0); 

  elif assigned M`basis_matrix_wrt_ambient then 

    // (TO DO: is this always better than getting it directly from the big operator?)
    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    Tp_amb := operator(M`Ambient, p, op);
    Tp_amb := ChangeRing(Tp_amb, BaseRing(bm));
    Tp := bm * Tp_amb * bmi;

    if debug and basis_is_honest(M) and Norm(p + Level(M)) eq 1 then 
      // check Tp really preserves M as a subspace of M`Ambient
      assert Rowspace(bm * Tp_amb) subset Rowspace(bm); 
    end if;

  elif IsBianchi(M) then

    // Always compute and store operator on ambient

    bool, MA := HasAttribute(M, "Ambient");

    if not bool then
      return HeckeMatrixBianchi(M, p);
    end if;

    assert not assigned MA`Ambient;

    Tp := HeckeMatrixBianchi(MA, p);

    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    return bm * Tp * bmi;

  elif IsDefinite(M) then 

    MA := TopAmbient(M);
    case op:
      when "Hecke"   : Tp_big := HeckeOperatorDefiniteBig(MA, p);
      when "AL"      : Tp_big := AtkinLehnerDefiniteBig(MA, p);
      when "DegDown1": Tp_big := DegeneracyDown1DefiniteBig(MA, p);
      when "DegDownp": Tp_big := DegeneracyDownpDefiniteBig(MA, p);
    end case;
    Tp := restriction(M, Tp_big);

  else // indefinite quat order

    disc := make_ideal(Discriminant(QuaternionOrder(M)));
    MA := TopAmbient(M);
    assert disc eq make_ideal(NewLevel(MA));
    N := Level(M)/disc;

    Gamma := FuchsianGroup(QuaternionOrder(M));
    case op:
      when "Hecke" : Tp_big := HeckeMatrix(Gamma, N, p);
      when "AL"    : Tp_big := HeckeMatrix(Gamma, N, p : UseAtkinLehner);
    end case;
    bm, bmi := basis_matrix(M);
    Tp := restriction(M, Tp_big);

  end if;

  if assigned M`hecke_matrix_field then
    bool, Tp := CanChangeRing(Tp, M`hecke_matrix_field);
    error if not bool, 
         "The hecke_matrix_field seems to be wrong!\n" * please_report;
  end if;

  if debug then
    // check commutativity
    bad := Level(M) / NewLevel(M);
    new := Minimum(bad) eq 1;
    for l in Keys(M`Hecke) do 
      if new or Minimum(l + bad) eq 1 then
        Tl := M`Hecke[l];
        assert Tl*Tp eq Tp*Tl; 
      end if;
    end for; 
  end if;

  // Cache
  // (for definite ambient, big matrix is cached instead)
// TO DO: hecke_algebra etc checks cache directly
//if not (IsDefinite(M) and not assigned M`Ambient) then
    case op:
      when "Hecke"    : M`Hecke[p]    := Tp;
      when "AL"       : M`AL[p]       := Tp;
      when "DegDown1" : M`DegDown1[p] := Tp;
      when "DegDownp" : M`DegDownp[p] := Tp;
    end case; 
//end if;

  return Tp;
end function;

intrinsic HeckeOperator(M::ModFrmHil, p::Any) -> Mtrx
{The Hecke operator T_p on the space M of Hilbert modular forms 
 (where p is a prime ideal of the base field of M)}

  bool, err, p := checks(M, p, "Hecke");
  require bool : err;
 
  return operator(M, p, "Hecke");
end intrinsic;

intrinsic AtkinLehnerOperator(M::ModFrmHil, q::Any) -> Mtrx
{The Atkin-Lehner operator W_q on the space M of Hilbert modular forms
 (where q is an ideal of the base field of M)}
       
  bool, err, q := checks(M, q, "AL");
  require bool : err;

  // The internal AL functions take primes (by convention)
  ps := [t[1] : t in Factorization(q)];
  Wq := operator(M, ps[1], "AL");
  for p in ps[2..#ps] do
    Wq *:= operator(M, p, "AL");
  end for;

  return Wq;
end intrinsic;

// TO DO
// intrinsic DegeneracyOperator(M::ModFrmHil, p::Any, p::Any) -> Mtrx

// TO DO: also Min poly, and use the modular method (implemented in this file)

intrinsic HeckeCharacteristicPolynomial(M::ModFrmHil, p::Any) -> RngUPolElt
{Optimized way to obtain CharacteristicPolynomial(HeckeOperator(M, p)).}

  if not assigned M`HeckeCharPoly then
    M`HeckeCharPoly := AssociativeArray();
  end if;

  bool, fp := IsDefined(M`HeckeCharPoly, p);
  if not bool then
    Tp := HeckeOperator(M, p);
    fp := CharacteristicPolynomial(Tp);
    M`HeckeCharPoly[p] := fp;
  end if;
  return fp;
end intrinsic;

/* 
Livne Theorem 7.4 gives us the Ramanujan bound for a Hecke eigenvalue
at a prime P lying over a rational prime p:
  |a_P| <= 2 * p ^ ([F_P:Q_p] * C/2)
where C = CentralCharacter(M)

TO DO: there's a discrepancy in the statements of Livne's theorems !!!
Must be C+1 not C here?
*/
intrinsic HeckeEigenvalueBound(M::ModFrmHil, P::Any) -> RngElt
{Bound on |a_P| where a_P is the Hecke eigenvalue at the prime P 
of a cuspidal newform in M}

  rat := Type(BaseField(M)) eq FldRat;
  p := Minimum(P);
  d := rat select 1 else LocalDegree(Place(P));
  C := CentralCharacter(M);
  r := d*(C+1)/2;
  if IsIntegral(r) then
    r := Integers()!r;
  end if;
  return 2*p^r;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
//  Linear algebra stuff for bases, decomposition etc                  //
/////////////////////////////////////////////////////////////////////////

function random_large_split_prime_using_max_order(K)
  OK := Integers(K);
  while true do 
    p := PreviousPrime(Random(B,2*B) : Proof:=false) where B is Round(2^22.5);
    if OK cmpeq Integers() then 
      return p;
    elif AbsoluteDiscriminant(OK) mod p eq 0 then 
      continue;
    elif exists(P){tup[1] : tup in Factorization(p*OK) | AbsoluteNorm(tup[1]) eq p} then
      assert IsPrime(P);
      return P; 
    end if;
  end while;
end function;

function random_large_split_prime(K)
  if Type(K) eq FldRat then
    p := PreviousPrime(Random(B,2*B) : Proof:=false) where B is Round(2^22.5);
    return p;
  end if;
  F := BaseField(K);
  OF := Integers(F);

  assert Ngens(K) eq 1;
  f := DefiningPolynomial(K);
  integral, f := CanChangeRing(f, OF);
  assert integral;
  assert IsMonic(f);
  O := Order(ChangeUniverse(Basis(OF), K) cat [K.1]);

  while true do 
    p := random_large_split_prime_using_max_order(F);
    k, res := ResidueClassField(p);
    fp := Polynomial([k| c@res : c in Coefficients(f)]);
    bool, rt := HasRoot(fp);
    if bool and Evaluate(Derivative(fp),rt) ne 0 then
      pbasis := Type(p) eq RngIntElt select [O|p] 
                                      else ChangeUniverse(Basis(p),O);
      P := ideal< O | pbasis cat [O| K.1 - (rt@@res)] >;
      assert IsPrime(P);
      return P;
    end if;
  end while;
end function;

// Reduction mod P of a matrix algebra T

function reduction(T, P : res:=0)
  K := BaseRing(T);
  if res cmpne 0 then
    k := Codomain(res);
  elif Type(K) eq FldRat then
    k := GF(P);
    res := map<Rationals() -> k | x :-> k!x>;
  else
    k, res := ResidueClassField(P);
  end if;

/* TO DO: implement CanChangeRing(Mrtx[FldRat], FldFin)
  if Type(K) eq FldRat then
    if ISA(Type(T), Mtrx) then
      return CanChangeRing(T, k);
    else
      U := [];
      for t in GeneratorsSequence(T) do
        bool, u := CanChangeUniverse(t, k);
        if bool then
          Append(~U, u);
        else
          return false, _;
        end if;
        return true, MatrixAlgebra< k, Degree(T) | U >;
      end for;
    end if;
  end if;
*/

  // General case
  // TO DO: implement CanChangeRing(Mtrx, Map)

  function red(t)
    u := MatrixAlgebra(k, Nrows(t)) ! 0;
    flag := true;
    for e in Support(t) do
      i, j := Explode(e);
      try
        u[i,j] := t[i,j] @ res;
      catch E;
        flag := false;
      end try;
    end for;
    if flag then
      return true, u;
    else
      return false, _;
    end if;
  end function;
  
  if ISA(Type(T), Mtrx) then
    return red(T);
  else
    U := [];
    for t in GeneratorsSequence(T) do
      bool, u := red(t);
      if bool then
        Append(~U, u);
      else
        return false, _;
      end if;
    end for;
    return true, MatrixAlgebra< k, Degree(T) | U >;
  end if;
end function;

function reduction_mod_random_large_split_prime(T, F)
  repeat
    P := random_large_split_prime(F);
    bool, U := reduction(T, P);
  until bool;
  return U, P;
end function;

// For a matrix algebra U, returns the dimension of the module U*v
// (which is a lower bound on the dimension of U)

function dimension_lower_bound(U : maxdim:=-1, tries:=1, vector:=0, suborbit:=0)
  g := Ngens(U);
  n := Ncols(U.1);
  F := BaseRing(U);
  V := VectorSpace(F, n);
  if maxdim lt 0 then
    maxdim := n; // the strongest lower bound we might obtain
  end if;
  if vector cmpne 0 then
    vectors := [vector];
    assert tries eq 1;
  else
    vectors := [[Random(100) : i in [1..n]] : t in [1..tries]];
    assert suborbit cmpeq 0;
  end if;
  dims := [];
  orbits := [];

  for t := 1 to tries do

    if suborbit cmpne 0 then
      assert g gt 1;
      W := suborbit;
    else
      // First get module generated by images under U.1
      w := V! vectors[t];
      W := sub< V | w >;
      repeat
        w := w*U.1;
        Include(~W, w, ~new);
      until not new;
    end if;
    dim := Dimension(W);

    // Now get the whole module
    if g gt 1 then

// Here the first loop is nicer than the second loop.
// For probabilistic results, use the first loop only.
// Using both seems slightly faster on average than 
// using only the second.
if true then 
      time0 := Cputime();
      count0 := 10;   // TO DO
      count := count0;
      while dim lt maxdim and count gt 0 do
        i := (suborbit cmpne 0 and Random(1) eq 1)
             select g else Random([1..g]);
        w := Random(Basis(W)) * U.i;
        Include(~W, w, ~new);
        if new then
          count := count0;
        else
          count -:= 1;
        end if;
        dim := Dimension(W);
      end while;
      vprintf ModFrmHil, 2: " [New bit: %o] ", Cputime(time0);
end if;
// dim0 := dim;
if true then
      time0 := Cputime();
      stable := [false : i in [1..g]];
      i := 1;
      while dim lt maxdim and not &and stable do 
        i := (i lt g) select i+1 else 1;
        W := Rowspace( VerticalJoin(B, B*U.i) ) where B is BasisMatrix(W);
        if dim eq Dimension(W) then
          stable[i] := true;
        else
          stable := [false : i in [1..g]];
        end if;
        dim := Dimension(W);
      end while;
      vprintf ModFrmHil, 2: " [Old bit: %o] ", Cputime(time0);
end if;
// assert dim0 eq dim;
// if dim0 ne dim then printf "\nFAIL\n[%o, %o]\n", dim0, dim; end if;

    end if;

    Append(~dims, dim);
    Append(~orbits, W);

    if dim eq maxdim then 
      break t; 
    end if;

  end for; // tries

  _, t := Max(dims);
  return dims[t], vectors[t], orbits[t];
end function;

// The matrix algebra generated by all Hecke operators of a *new* space M.
// The generators are Hecke operators of M, at sufficiently many primes 
// (not dividing the level) to generate it.
// Also returns a vector which generates the Hecke module,
// and for later conveniece, the reduction mod P of the matrix algebra.

// TO DO: do not construct any MatrixAlgebra

function hecke_algebra_dimension(M) 
  if IsNew(M) then
    d := Dimension(M);
  else
    // TO DO: directly with formula 
    F := BaseRing(M);
    k := Weight(M);
    QO := QuaternionOrder(M);
    NN := NewLevel(M);
    vprintf ModFrmHil, 2: "Hecke algebra dimension: ";
    vtime ModFrmHil, 2:
    dims := [ Dimension(NewSubspace(HilbertCuspForms(F, I*NN, k) : QuaternionOrder:=QO))
            : I in Divisors(Level(M)/NN)];
    d := &+ dims;
    if assigned M`include_eis and M`include_eis then
      d +:= NarrowClassNumber(BaseRing(M));
    end if;
    vprintf ModFrmHil, 2: "Hecke algebra dimension: %o = %o (%o)\n", dims, d, Dimension(M);
  end if;
  assert d gt 0;
  return d;
end function;

function hecke_algebra(M : generator:=false, minimal:=true)

  // don't use cached hecke_algebra if basis has since been changed to a rational_basis
  use_cached_hecke_algebra := false;
  if assigned M`hecke_algebra then
    if not assigned M`hecke_matrix_field
      or M`hecke_matrix_field eq BaseRing(M`hecke_algebra[1])
    then
      use_cached_hecke_algebra := true;
    end if;
  end if;

  if not use_cached_hecke_algebra then

    K := BaseRing(M);
    N := Level(M);
    d := Dimension(M);
    da := hecke_algebra_dimension(M);
    assert da gt 0;

    PI := PowerIdeal(Integers(K));
    n := 1;
    if assigned M`UseHardHeckeGenerator then
      n := M`UseHardHeckeGenerator; assert Type(n) eq RngIntElt and n ge 1;
    end if;
    primes_n := [PI|];
    primes_used := [PI|];
    dim := 0;

    vprintf ModFrmHil: "Constructing Hecke algebra of dimension %o:\n", da;
    vtime ModFrmHil:

    i := 0;
    repeat
      dim0 := dim;
      // get another prime pp
      while IsEmpty(primes_n) do
        n +:= 1;
        primes_n := [p: p in PrimesUpTo(n, K : coprime_to:=N) | Norm(p) eq n];
        // sort them in a suitable order (note this is not unique)
        ordering := [<Minimum(p), p> : p in primes_n];
        ParallelSort(~ordering, ~primes_n);
        Reverse(~primes_n);
        if IsBianchi(M) then
          C, mC := ClassGroup(K);
          C2 := 2*C;
          primes_n := [p: p in primes_n | p@@mC in C2];
        end if;
      end while;
      Append(~primes_used, primes_n[#primes_n]);
      Prune(~primes_n);
      heckes := [HeckeOperator(M, p) : p in primes_used];
      F := BaseRing(Universe(heckes));
      T := MatrixAlgebra< F, d | heckes >;
      i +:= 1;
      if i mod 3 eq 1 or Ngens(T) eq 1 then
        U, P := reduction_mod_random_large_split_prime(T, F);
        dim, vec, orbit := dimension_lower_bound(U : maxdim:=da, tries:=1);
      else
        _, U := reduction(T, P); // TO DO: res vararg?
        dim, vec, orbit := dimension_lower_bound(U : maxdim:=da, tries:=1, 
                                                 vector:=vec, suborbit:=orbit);
      end if;
      // We very rarely choose a bad random large prime P, 
      // but if M decomposes into many pieces, occasionally
      // choose a bad random vector.  (Either way, we then
      // compute unnecessary hecke operators.)
      // The work here (esp for raw spaces) is harder than
      // computing Hecke operators (at least for definite), 
      // so take tries = 1, and sometimes reuse P and vec.
assert dim ge dim0; // unless bad P
      if dim le dim0 then
        Prune(~primes_used);
      end if;
    until dim eq da;

if minimal then
    // Second pass, to get a minimal set of generators
    // (this is relatively quick)
    FP := BaseRing(U);
    t := Ngens(T);
    inds := [1..t];
    vprintf ModFrmHil: "Choosing minimal generators for Hecke algebra: \n";
    vtime ModFrmHil:
    for i := 1 to t-1 do 
      Ui := MatrixAlgebra< FP, d | [U.j : j in inds | j ne i] >;
      if da eq dimension_lower_bound(Ui : maxdim:=da, vector:=vec) then
        // T.i is redundant
        Exclude(~inds, i);
      end if;
    end for;
    T := MatrixAlgebra< F, d | [T.i : i in inds] >;
    U := MatrixAlgebra< FP, d | [U.i : i in inds] >;
    primes_used := [primes_used[i] : i in inds];
end if;

    assert Ngens(T) gt 0;
    assert Ngens(T) eq #primes_used;
    assert forall{i: i in [1..Ngens(T)] | T.i eq HeckeOperator(M, primes_used[i])};
    if debug then
      assert U eq reduction(T, P);
      assert da eq dimension_lower_bound(U : vector:=vec);
    end if;

    vprintf ModFrmHil: "Hecke algebra is generated by primes of norms %o\n", 
                        [Norm(P) : P in primes_used];

    M`hecke_algebra := [* T, primes_used, Vector(F,vec), U, P *];

  end if; // not use_cached_hecke_algebra

  if generator and #M`hecke_algebra eq 5 then

    // Find a single generator of the matrix algebra T,
    // as a combination of the generators T.i
    // Always uses the last generator with coefficient 1

    // Note: testing candidates mod P is quick compared with other things 
    // (like finding the min poly of the result), so it's definitely worth
    // looking for a simple combination that works

    d := Dimension(M);
    da := hecke_algebra_dimension(M);
    T, primes_used, vec, TP, P := Explode(M`hecke_algebra);
    vec := Vector(BaseRing(TP), vec);
    g := Ngens(T);

    if g eq 1 then
      M`hecke_algebra cat:= [* T.1, [1] *];

    elif assigned M`UseHardHeckeGenerator then
      // Use combination guaranteed to have distinct eigenvalues
      bounds := [HeckeEigenvalueBound(M, P) : P in primes_used];
      v := [1];
      for i := 2 to g do
        v[i] := Ceiling( v[i-1] * (bounds[i-1] + 1) );
      end for;
      t  := &+ [v[i] * T.i : i in [1..g]];
      tP := &+ [v[i] * TP.i : i in [1..g]];
      assert dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec) eq da;

      M`hecke_algebra cat:= [* t, v *];

      vprintf ModFrmHil: "The hard Hecke algebra generator has the form %o * %o\n",
                          v, [Norm(P) : P in primes_used];
    else
      // If hard, use "divide + conquer" strategy
      FP := BaseRing(TP);
      function single_gen(TP, vec : dim:=0)
        if dim eq 0 then 
          dim := dimension_lower_bound(TP : vector:=vec); 
          // is this necessarily the full dimension of the T associated to TP? 
          // (in any case, a rigourous check is done at the end)
          rigour := false;
          dim_known := false;
        else
          dim_known := true;
        end if; 
        g := Ngens(TP);
        L := StandardLattice(g-1);
        n := 0;
        count := 0;
        maxcount := 500;
        vprintf ModFrmHil, 2: "(%o)", g; 
        while true do
          n +:= 1;
          svs := [tup[1] : tup in ShortVectors(L,n,n) | 0 notin Eltseq(tup[1])];
          for sv in svs, s in {1,-1} do 
            count +:= 1;
            vprintf ModFrmHil, 2: "."; 
            v := s*sv;
            tP := &+ [v[i]*TP.i : i in [1..g-1]] + TP.g;
            dlb := dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec);
            if dlb eq dim then
              return Eltseq(v) cat [1], tP, dim_known;
            elif count ge maxcount and g ge 4 then
              // divide and conquer
              gg := g div 2;
              v1, tP1 := single_gen(MatrixAlgebra<FP,d| [TP.i : i in [1..gg]] >, vec);
              v2, tP2 := single_gen(MatrixAlgebra<FP,d| [TP.i : i in [gg+1..g]] >, vec);
              w, tP := single_gen(MatrixAlgebra<FP,d|tP1,tP2>, vec);
              v := [w[1]*x : x in v1] cat [w[2]*x : x in v2];
              assert tP eq &+ [v[i]*TP.i : i in [1..g]];
              return v, tP, false;
            end if;
          end for; // v
        end while;
      end function;
  
      vprintf ModFrmHil: "Looking for a single generator of the Hecke algebra: ";
      vprintf ModFrmHil, 2: "\n";
      vtime ModFrmHil:

      v, tP, rigorous := single_gen(TP, vec : dim:=da);
      if not rigorous then
        // Check the result to ensure rigour
        // (dimension_lower_bound may have been used non-rigorously above)
        assert dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec) eq da;
      end if;
      assert #v eq g;
      assert tP eq &+ [v[i]*TP.i : i in [1..g]];
      t         := &+ [v[i]*T.i : i in [1..g]];
      M`hecke_algebra cat:= [* t, v *];

      vprintf ModFrmHil: "The Hecke algebra generator has the form %o * %o\n",
                          v, [Norm(P) : P in primes_used];
    end if; // g = 1

  end if; // needed to find generator

  return M`hecke_algebra;
end function;

// Basis of M consisting of some vector v and its images under a rational basis of hecke_algebra(M),
// obtained by taking monomials in its generators (we take the first monomials, lexicographically,
// that are independent).  We do it all mod P, only the basis vectors themselves need to be done 
// globally.  Returns the basis of M, and the corresponding polynomials over BaseField(M).

function rational_basis(M)

  vprint ModFrmHil: "Computing enough Hecke operators to generate the Hecke algebra"; 
  time0 := Cputime();
  IndentPush();
  T, _, v, TP, P := Explode(hecke_algebra(M));
  IndentPop();
  vprintf ModFrmHil: "Time: %o\n", Cputime(time0);

  dim := Dimension(M);
  k, res := ResidueClassField(P); // we can't be over Q here? otherwise this will fail!
  vP := Vector(k, dim, [res(a) : a in Eltseq(v)]);
  Tgens := GeneratorsSequence(T);
  TPgens := GeneratorsSequence(TP);
assert TPgens eq [Matrix(k, dim, [res(a) : a in Eltseq(t)]) : t in Tgens];

  // Now implicitly compute a rational basis of T, collecting the 
  // corresponding images of v and checking their independence mod P 
  // (note: we know that v works)
  vprintf ModFrmHil, 2: "Now choosing the rational basis: ";
  Pol := PolynomialRing(BaseField(M), #Tgens);
  V := Parent(v); 
  VP := Parent(vP);
  bas := [v];
  basP := [vP];
  wP := vP;
  WP := sub< VP | vP >;
/*
  // Optional: first find the orbit under the first generator of T
  // (probably a bad idea; will tend to put the first generator 
  // in rational canonical form, but make the others Heckes bad)
  w := v;
  vtime ModFrmHil, 2:
  for i := 1 to dim-1 do
    w := w*Tgens[1];
    wP := wP*TPgens[1];
    Include(~WP, wP, ~new);
    if new then
      vprintf ModFrmHil, 2: ".";
      Append(~bas, w);
      Append(~basP, wP);
    else
      break i;
    end if;
  end for;
*/
  // Now use each of the generators in turn, until we reach full dim
  i := 0;
  vtime ModFrmHil, 2:
  while #bas lt dim do
    i := (i lt #Tgens) select i+1 else 1;
    vprintf ModFrmHil, 2: "%o", i;
    for j := 1 to #bas do 
      wP := basP[j] * TPgens[i];
      Include(~WP, wP, ~new);
      if new then
        vprintf ModFrmHil, 2: ".";
        w := bas[j] * Tgens[i];
        Append(~bas, w);
        Append(~basP, wP);
        if #bas eq dim then
          break;
        end if;
      end if;
    end for;
  end while;

  return Matrix(bas);
end function;

intrinsic SetRationalBasis(M::ModFrmHil)
{For a space M of Hilbert modular forms over a number field K, this
 resets the basis of the space to be such that the Hecke operators are
 matrices with entries in the smallest field possible.  (In parallel 
 weight, this is Rationals().  In general, it is a subfield of the 
 splitting field of K.)  The basis is then fixed, and all subsequent 
 computations with M will be done relative to this basis.}

  if IsBianchi(M) 
     or assigned M`QuaternionOrder and not IsDefinite(M) 
     or Seqset(Weight(M)) eq {2}
     or Dimension(M) eq 0 
  then
    M`hecke_matrix_field := Rationals();
  end if;

  // Check if M already has a rational basis
  if assigned M`hecke_matrix_field then
    // coerce cached Hecke if necessary
    H := M`hecke_matrix_field;
    for P in Keys(M`Hecke) do 
      TP := M`Hecke[P];
      if BaseRing(TP) cmpne H then
        M`Hecke[P] := ChangeRing(TP, H);
      end if;
    end for;
    for P in Keys(M`HeckeCharPoly) do 
      fP := M`HeckeCharPoly[P];
      if BaseRing(fP) cmpne H then
        M`HeckeCharPoly[P] := ChangeRing(fP, H);
      end if;
    end for;
    return;
  end if;

  require IsNew(M) : "Currently SetRationalBasis is only available for new spaces,"
                    *" ie spaces M with NewLevel(M) = Level(M)";
  // Note: in particular this means the basis of M`Ambient can never change.

  // Reset basis matrix 
  K := BaseField(M);

  vprint ModFrmHil: "Choosing \'rational\' basis for space of dimension", Dimension(M); 
  IndentPush(); time0 := Cputime();
  cob := rational_basis(M);
  IndentPop(); vprint ModFrmHil: "Time:", Cputime(time0);
  vprintf ModFrmHil: "Inverting change of basis matrix: "; 
  vtime ModFrmHil:
  cob_inv := cob^-1;
  M`basis_matrix := cob * M`basis_matrix;
  M`basis_matrix_inv := M`basis_matrix_inv * cob_inv;
  if assigned M`basis_matrix_wrt_ambient then
    M`basis_matrix_wrt_ambient := cob * M`basis_matrix_wrt_ambient;
    M`basis_matrix_wrt_ambient_inv := M`basis_matrix_wrt_ambient_inv * cob_inv;
  end if;

  // Conjugate stored Hecke operators into the new basis
  for P in Keys(M`Hecke) do
    TP := M`Hecke[P];
    M`Hecke[P] := cob * TP * cob_inv;
  end for;

  if not M`hecke_matrix_field_is_minimal then
    H := minimal_hecke_matrix_field(M);
    M`hecke_matrix_field := H;
    M`hecke_matrix_field_is_minimal := true;
    // Coerce stored Hecke matrices to the smaller field
    for P in Keys(M`Hecke) do
      TP := M`Hecke[P];
      M`Hecke[P] := ChangeRing(TP, H);
    end for;
    for P in Keys(M`HeckeCharPoly) do
      fP := M`HeckeCharPoly[P];
      M`HeckeCharPoly[P] := ChangeRing(fP, H);
    end for;
  end if;

end intrinsic;

/*
function MinimalPolynomialViaAction(T, v)
printf "(using MinimalPolynomialViaAction) ";
  K := BaseRing(T);
  n := Nrows(T);
  M := ZeroMatrix(K, n+1, n);
  InsertBlock(~M, v, 1, 1);
  w := v;
  for i := 1 to n do 
printf ".";
    w := w*T;
    InsertBlock(~M, w, i+1, 1);
  end for;
printf "KernelMatrix "; time
  K := KernelMatrix(M);
  assert Nrows(K) eq 1;
  pol := Polynomial(Eltseq(K[1]));
if n lt 50 then
 assert Evaluate(pol, T) eq 0;
end if;
  return pol;
end function;
*/

// assumes poly is monic with coeffs in Z bounded by 'bound'

// TO DO: probably do this for min poly also

function CharacteristicPolynomialViaCRT(T, bound)
  K := BaseRing(T);
  OK := Integers(K);
  error if K eq Rationals(), "Over Q, use internal CharacteristicPolynomial.";

  n := Nrows(T);

  primes := [Integers()| ];
  pols := [* *];

  // use extra primes as a safety check
  extra := 5;
  safety := Ceiling((2^23.5) ^ extra);

  p := Floor(2^23.5);

  while &*primes lt bound*safety do 
    p := PreviousPrime(p : Proof:=false);
    if not exists(P){tup[1] : tup in Factorization(p*OK) | Norm(tup[1]) eq p} then
      continue;
    end if;
    vprintf ModFrmHil, 2: ".";
    k, res := ResidueClassField(P);
    TP := Matrix(k, n, [a@res : a in Eltseq(T)]);
    chiP := CharacteristicPolynomial(TP);
    assert IsMonic(chiP);
    if Degree(chiP) eq n then
      Append(~primes, p);    
      Append(~pols, chiP);
    end if;
  end while;

  prod := &* primes;
  coeffs := [1 : i in [0..n]];
  for i := 0 to n-1 do
    c := CRT([Integers()!Coefficient(pols[j],i) : j in [1..#primes]], primes);
    // take least residues
    if 2*c gt prod then 
      c -:= prod;
    end if;
    coeffs[i+1] := c;
  end for;

  // the following check is likely to fail if answer is bogus and extra > 0
  assert forall{c : c in coeffs | Abs(c) le bound};

  pol := Polynomial(coeffs);

if n le 20 then
 TT := MatrixAlgebra(K, n)! T;
 assert Evaluate(pol, TT) eq 0;
end if;

 return pol;
end function;


function NewformsOfDegree1Implemented(M)
  bool, k := IsParallelWeight(M);
  return bool and k eq 2;
end function;

// TO DO: Sort (by default?)

intrinsic NewformDecomposition(M::ModFrmHil : Dimensions:=0) -> List
{Given a new space M of Hilbert modular forms, this decomposes M into subspaces 
 that are irreducible as Hecke modules, and returns this list of new spaces}

  // Check if full decomposition is stored
  bool, ND := HasAttribute(M, "NewformDecomposition");
  if bool and Dimension(M) eq &+ [Integers()| Dimension(N) : N in ND] then
    if Dimensions cmpeq 0 then
      return ND;
    elif Type(Dimensions) eq RngIntElt then
      return [* N : N in ND | Dimension(N) eq Dimensions *];
    else
      return [* N : N in ND | Dimension(N) in Dimensions *];
    end if;
  end if;

  dim := Dimension(M : UseFormula := false);

  if Dimensions cmpeq 0 then
    Dimensions := [1..dim];
  elif Type(Dimensions) eq RngIntElt then
    Dimensions := [Dimensions];
  else
    require ISA(Type(Dimensions), Setq) and Type(Universe(Dimensions)) eq RngInt: 
            "'Dimensions' should be a sequence of integers";
  end if;

  require IsNew(M) or dim eq 0 :
         "Currently implemented only for new spaces (constructed using NewSubspace)";

  if assigned M`HeckeIrreducible and M`HeckeIrreducible then
    // M was constructed by NewformDecomposition
    if not assigned M`HeckeMethod then
      M`HeckeMethod := 1;
    end if;
    ND := [* M *];

  elif dim eq 0 then 
    ND := [* *]; 

  /* TO DO
  elif dim eq 1 then 
    endow M with the attributes of an eigenspace
    ND := [* M *]; 
  */

  elif Dimensions eq [1] and NewformsOfDegree1Implemented(M)
and dim ne 1 // beware recursion
  then
    return [* Parent(f) : f in NewformsOfDegree1(M) *];

  else

// !!!!! possibly don't SetRationalBasis first !!!!!
// SetRationalBasis(M);

    K := hecke_matrix_field(M); // Hecke matrices should be over this, currently

    T, primes, v, _, P, t, comb := Explode(hecke_algebra(M : generator));
    assert BaseRing(t) eq K;

    vprintf ModFrmHil: "Characteristic polynomial of Hecke algebra generator: "; 
    vtime ModFrmHil:
    if K eq Rationals() or not IsParallelWeight(M) then
      chi := CharacteristicPolynomial(t);
    else
      // parallel weight ==> poly is over Z
      apbound := &+ [Abs(comb[i])*HeckeEigenvalueBound(M,primes[i]) 
                    : i in [1..#primes] | comb[i] ne 0];
      bound := dim*apbound^dim;
      chi := CharacteristicPolynomialViaCRT(t, bound);
    end if;

    // decomposition should be over the true hecke field (= Q for parallel weight)
    chi := ChangeRing(chi, minimal_hecke_matrix_field(M));

    vprintf ModFrmHil: "Factoring the polynomial: "; 
    vtime ModFrmHil:
    fact := Factorization(chi);
    assert forall{tup: tup in fact | tup[2] eq 1};

    if #fact eq 1 then
      M`HeckeIrreducible := true;
    end if;

    vprintf ModFrmHil: "Decomposition dimensions: %o = %o\n", dim, [Degree(tup[1]) : tup in fact];

    fact1 := Dimensions cmpeq 0 select fact 
                                else [tup: tup in fact | Degree(tup[1]) in Dimensions];
    if IsEmpty(fact1) then
      return [* *]; 
    end if;
    // TO DO: elif #fact eq 1 then

    // CHECK: each field should either be totally real or a CM field
    vprintf ModFrmHil, 2: "Checking the eigenvalue fields look okay: ";
    vtime ModFrmHil, 2:
    for tup in fact1 do
      if BaseRing(K) cmpeq Rationals() then
        real_pols := [* tup[1] *];
      else
        real_pols := [* Polynomial([Real(Conjugate(c,i)) : c in Eltseq(tup[1])]) 
                      : i in [1..Degree(K)] *];
      end if;
      real_roots := [#Roots(pol) : pol in real_pols];
      okay := &and [num eq Degree(tup[1]) : num in real_roots] or &and [num eq 0 : num in real_roots];
      error if not okay,
        "Serious bug detected!!!\nThe eigenvalue fields are not of the expected kind.\n" * please_report;
    end for;

    // Construct the irreducible subspaces, in some form.
    // Here we have lots of choices:
    // (1) proceed as Allan did over Q: write down trivial basis of each component 
    //     using the trick below, then echelon using rational reconstruction. 
    // (2) write down a nicer basis by taking images, so that action of known 
    //     heckes is integral.  Use LLL.  Don't find inverse change of basis:
    //     obtain hecke matrices in new basis via CRT, since they are integral.
    // (3) Don't write down a basis.  Compute an eigenform by doing Nullspace 
    //     over an extension (use rational reconstruction).  Hecke operators on
    //     each subspace are obtained as representation matrices of eigenvalues.

HeckeMethod := assigned M`HeckeMethod 
               select M`HeckeMethod else 1;

if HeckeMethod eq 4 then 
 "\nWARNING!!!  Method 4 was specified in NewformDecomposition!" *
 "\n\nThis method transcends normal dimensions: it exists in a" *
 "\nhyperspatial paradigm whose existentiality is not known to be" *
 "\nconsistent with the Magma philosophy. This may be dangerous.";
end if;

    if HeckeMethod eq 0 then

      // Obvious way to decompose:
      components := [* KernelMatrix(Evaluate(tup[1], t)) : tup in fact *];

      "WARNING: Method 0 was selected!!! (Usefulness = 0)";

    elif HeckeMethod eq 1 then

      // Write down basis of each component.
      // For each prime factor f with chi = f*g, the corresponding newform space is 
      // Ker f(t) = Im g(t) which has (rational) basis [v*g(t)*t^i : 0 <= i < deg(g)]

      // First write down (rational) basis [v*t^i : 0 <= i < dim]
      v_images := ZeroMatrix(K, dim, dim);
      InsertBlock(~v_images, v, 1, 1);
      vti := v;
      vprintf ModFrmHil: "Spinning: ";
      vtime ModFrmHil: 
      for i := 1 to dim-1 do 
        vti := vti * t;
        InsertBlock(~v_images, vti, i+1, 1);
      end for;

      components := [* *];
      vprintf ModFrmHil: "Decomposing: ";
      vtime ModFrmHil: 
      for tup in fact do 
        f := tup[1];
        g := chi div f;
        d := Degree(f);
        vprintf ModFrmHil: "%o ", d;
        gcoeffs := ChangeRing(Vector(Eltseq(g)), K);
        // build left-multiplier matrix (rows determine basis elements)
        coeff_mat := ZeroMatrix(K, d, dim);
        for i := 1 to d do 
          InsertBlock(~coeff_mat, gcoeffs, i, i);
        end for;
        bas_mat := coeff_mat * v_images;
        // better echelonize now, will be needed immediately below (in method 1)
        vprintf ModFrmHil, 3: "Echelonizing basis: ";
        vtime ModFrmHil, 3: 
        bas_mat := EchelonForm(bas_mat); 
        Append(~components, bas_mat);
      end for;

    end if;

    if HeckeMethod le 1 then

      // TO DO: the hecke_matrix_field business here might not be correct
      // Previously we had SetRationalBasis on M and its ambient at the start. 
      // Here we do have a rational basis of each component (at least in method 1).

      MA := Ambient(M);
      ND := [* *];
      vprintf ModFrmHil: "Setting up newform spaces: ";
      vtime ModFrmHil: 

      for k := 1 to #components do
        kmat := components[k];
        if Nrows(kmat) notin Dimensions then
          continue;
        end if;

        if IsBianchi(M) then
          N := BMF_with_ambient(MA);
          N`NewLevel := N`Level;
        else
          N := HMF0(BaseField(M), Level(M), Level(M), DirichletCharacter(M), Weight(M), CentralCharacter(M)); 
          N`Ambient := MA;
        end if;
        // give N same ambient as M (TO DO: but reconsider when to make M wrt ambient, rather than wrt raw?)
        N`is_new := true;
        N`HeckeIrreducible := true;
        if assigned M`hecke_matrix_field then
          N`hecke_matrix_field := M`hecke_matrix_field;
        end if;
        field := hecke_matrix_field(N`Ambient);
        if #components eq 1 then 
          pseudo_inv := kmat ^ -1;
        else 
          complement := VerticalJoin(<components[i] : i in [1..#components] | i ne k>);
          pseudo_inv := pseudo_inverse(kmat, complement);
        end if;
        N`Dimension := Nrows(kmat);
        if assigned M`basis_matrix_wrt_ambient then
          N`basis_matrix_wrt_ambient := ChangeRing(kmat, BaseRing(A)) * A
                                                   where A is M`basis_matrix_wrt_ambient;
          N`basis_matrix_wrt_ambient_inv := Ai * ChangeRing(pseudo_inv, BaseRing(Ai))
                                                   where Ai is M`basis_matrix_wrt_ambient_inv;
          N`basis_matrix := ChangeRing(N`basis_matrix_wrt_ambient, BaseRing(A)) * A 
                                                   where A is MA`basis_matrix;
          N`basis_matrix_inv := Ai * ChangeRing(N`basis_matrix_wrt_ambient_inv, BaseRing(Ai)) 
                                                   where Ai is MA`basis_matrix_inv;
        else
          N`basis_matrix := ChangeRing(kmat, BaseRing(A)) * A
                                                   where A is M`basis_matrix;
          N`basis_matrix_inv := Ai * ChangeRing(pseudo_inv, BaseRing(Ai))
                                                   where Ai is M`basis_matrix_inv;
        end if;
        if assigned M`basis_is_honest then
          N`basis_is_honest := M`basis_is_honest;
        end if;
        Append(~ND, N);
      end for; // k

    else
      assert HeckeMethod ge 3; // Method 2 does not exist!
 
      if HeckeMethod eq 3 then
        "WARNING: Method 3 was selected for Hecke eigenform computations!!!";
        "         It's a very inefficient method (just warm-up for method 4)";
      end if;

      ND := [* *];

      assert K eq BaseRing(t);
      vprintf ModFrmHil, 2: "Checking hecke_algebra_generator (should take no time): "; 
      vtime ModFrmHil, 2:
      assert t eq &+ [comb[i]*HeckeOperator(M,primes[i]) : i in [1..#primes]];
      M`hecke_algebra_generator := <primes, comb, t>; // this must never be changed

      vprintf ModFrmHil: "Setting up newform spaces: "; 
      vtime ModFrmHil:
      for tup in fact1 do 
        // Construct eigenvalue field E
        f := tup[1];
        if Degree(f) eq 1 then
          E := BaseRing(f);
          e := Roots(f)[1][1];
        else
  	  E := ext< BaseRing(f) | f >; e:=E.1;// TO DO: Check:=false ?
        end if;

        // This space will not need any basis matrix stuff.
        // Hecke eigenvalues will be calculated from data stored in the eigenform.

        N := HMF0(BaseField(M), Level(M), Level(M), DirichletCharacter(M), Weight(M), CentralCharacter(M)); 
        N`Ambient := M;    // eigenvectors are expressed wrt the basis of M
        N`NewSpace := M;   // (this is used in best_column -- why not use ambient?)
        N`HeckeIrreducible := true;
        N`is_new := true;
        N`Dimension := Degree(f);

        // eigenvalue corresponding to N`Ambient`hecke_algebra_generator
        // TO DO: if debug, check it really is an eigenvalue of that
        N`hecke_algebra_generator_eigenvalue := e; 

        Append(~ND, N);
      end for;

    end if; // HeckeMethod

    for i := 1 to #ND do
      ND[i]`HeckeMethod := HeckeMethod;
    end for;

  end if;

  if &+ [Integers()| Dimension(N) : N in ND] eq Dimension(M) then
    M`NewformDecomposition := ND;
  end if;

  return ND;
end intrinsic;


// Find an eigenvector of M mod P with eigenvalue e mod P
// Returns false if eigenspace mod P is not dimension 1

function red_eigenvector(M, e, P, res)
//time
//assert not prime_is_in_denom(M, P);
 time
  MP := reduction(M, P : res:=res);
  eP := res(e);
 time
  VP := Eigenspace(MP, eP);
  if Dimension(VP) eq 1 then
    return true, VP.1;
  else
    return false, _;
  end if;
end function;

forward get_red_vector; // temp (TO DO)

intrinsic Eigenform(M::ModFrmHil) -> ModFrmHilElt
{An eigenform in the space M of Hilbert modular forms
 (which must be an irreducible module under the Hecke action)}

  require assigned M`HeckeIrreducible and M`HeckeIrreducible :
         "This is implemented only for spaces constructed using NewformDecomposition"; 

  require Dimension(M) gt 0 : "The given space M should not be zero-dimensional";

   if not assigned M`Eigenform then 

METHOD := M`HeckeMethod;

     vprintf ModFrmHil: "Setting up eigenform for space of dimension %o", Dimension(M);
     vprintf ModFrmHil, 2: " (using METHOD %o)", METHOD;
     vprintf ModFrmHil: "\n"; 

     nf := New(ModFrmHilElt);
     nf`Parent := M;

if METHOD lt 3 then

     // Old way: determine the Hecke algebra of this newform space

     T, _, _, _, _, t := Explode(hecke_algebra(M : generator));  

     vprintf ModFrmHil: "CharacteristicPolynomial: ";
     vtime ModFrmHil:
     chi := CharacteristicPolynomial(t);  
     chi := ChangeRing(chi, minimal_hecke_matrix_field(M)); // decomposition over this field
     require IsIrreducible(chi) : 
            "The space M is not an irreducible module under the Hecke action";

     if Degree(chi) eq 1 then 
       E := BaseRing(chi);
       e := t[1][1];
     else
       E := NumberField(chi); e:=E.1;
     end if;
     nf`BaseField := E;                  

     K := BaseRing(t);
     EK := CompositeFields(K, E)[1];

     tEK := ChangeRing(t, EK);
     eEK := EK!e;

     nf`BaseField := E;
     nf`EK := EK;
     nf`tEK := tEK;
     nf`eEK := eEK;

     vprintf ModFrmHil: "Eigenspace: ";
     vtime ModFrmHil:
     espace := Eigenspace(tEK, eEK);
     assert Dimension(espace) eq 1;
     nf`coords_wrt_parent := Basis(espace)[1];
     if basis_is_honest(M) then
       nf`coords_raw := nf`coords_wrt_parent * ChangeRing(M`basis_matrix, EK);
     end if;

elif METHOD ge 3 then

     // M is a component of the NewformDecomposition of M`Ambient
     // Write down an eigenvector relative to M`Ambient
     // TO DO: using rational reconstruction

     // Note: E is already defined above

     t := M`Ambient`hecke_algebra_generator[3];
     e := M`hecke_algebra_generator_eigenvalue;
     E := Parent(e); 
     K := BaseRing(t);
    
     // Construct a composite EK
     f := DefiningPolynomial(E);
     if Degree(f) eq 1 then
       EK := K;
     else
       vprintf ModFrmHil, 2: "Factorization: ";
       vtime ModFrmHil, 2:
       fact := Factorization(ChangeRing(f,K));
       fK := fact[1][1];
       if Degree(fK) eq 1 then
         EK := K;
         if EK ne E then
           Embed(E, EK, Roots(fK)[1][1]);
         end if;
       else
         EK := ext< K | fK >;
         Embed(E, EK, EK.1);
        /*
         // old work around
         // use the absolute field so that coercion works for EK to E 
         EKrel := ext< K | fK >;
         EK := AbsoluteField(EKrel);
         Embed(E, EK, EK!EKrel.1);
        */
       end if;
       // Doesn't help to use absolute, optimized EK
     end if;

     tEK := ChangeRing(t, EK);
     eEK := EK!e;

     nf`BaseField := E;
     nf`EK := EK;
     nf`tEK := tEK;
     nf`eEK := eEK;

end if;

if METHOD eq 3 then

     vprintf ModFrmHil: "Eigenspace of degree %o: ", Degree(f); 
     vtime ModFrmHil:
     V := Eigenspace(tEK, eEK);
     assert Dimension(V) eq 1;
     v := Vector(V.1);
     nf`coords_wrt_ambient := v;

     MA := M`Ambient;
     if basis_is_honest(MA) then
       nf`coords_raw := ChangeRing(v, EK) * ChangeRing(MA`basis_matrix, EK);
     end if;

elif METHOD eq 4 then

     // collect some eigenvectors mod P
     nf`red_coords_wrt_ambient := [* *];
     // TO DO: delay until needed (this is here for testing only) 
     get_red_vector(EK, tEK, eEK, ~nf`red_coords_wrt_ambient : NUM:=10);

end if; // METHOD
    
     nf`hecke_eigenvalues := AssociativeArray(PowerIdeal(Integers(BaseField(M))));
     M`Eigenform := nf;

   end if; // not assigned M`Eigenform

   return M`Eigenform;
end intrinsic;

intrinsic Eigenforms(M::ModFrmHil) -> List
{A list of eigenforms in the space M of Hilbert modular forms,
 corresponding to the NewformDecomposition of M}

  require IsNew(M) or Dimension(M) eq 0: 
    "Currently implemented only for new spaces (constructed using NewSubspace)";

  if Dimension(M) eq 0 then return [* *]; end if;

  return [* Eigenform(MM) : MM in NewformDecomposition(M) *];
end intrinsic;

intrinsic IsEigenform(f::ModFrmHilElt) -> BoolElt
{True iff the Hilbert modular form f was constructed as an eigenform}

  M := Parent(f);
  return assigned M`Eigenform and IsIdentical(f, M`Eigenform);
end intrinsic;

intrinsic HeckeEigenvalueField(M::ModFrmHil) -> Fld
{Same as BaseField(Eigenform(M))}  

  require assigned M`HeckeIrreducible and M`HeckeIrreducible :
         "This is implemented only for spaces constructed using NewformDecomposition";

  return BaseField(Eigenform(M));
end intrinsic;

procedure get_red_vector(EK, tEK, eEK, ~red_vecs : NUM:=1)
  // TO DO ??? will actually want it in the 'raw' basis ???
  Qs := {tup[1] : tup in red_vecs};
  for n := 1 to NUM do
    repeat
      repeat
        vprintf ModFrmHil, 2: "\nChoosing a large split prime: ";
        vtime ModFrmHil, 2:
        Q := random_large_split_prime(EK);
      until Q notin Qs;
      _, res := ResidueClassField(Q);
      okay, vQ := red_eigenvector(tEK, eEK, Q, res);
    until okay;
    Append(~red_vecs, <Q, res, vQ>);
  end for;
end procedure;

// Choose which column of A`BigHecke[P] to use
// when computing eigenvalues of the eigenform f

// TO DO: some newforms are contained in blocks,
// Should choose a minimal number of columns and 
// assign them (instead of giving up if 'no best')

function best_column(f, P)
  Mf := Parent(f);
  A := TopAmbient(Mf);
  known := {Integers()|};
  if assigned A`HeckeBig then
    bool, _known := IsDefined(A`HeckeBigColumns, P);
    if bool then
      known := Seqset(_known);
    end if;
  end if;
  v := f`coords_raw;
  n := Ncols(v);
  zeros := [{Integers()| i : i in [1..n] | v[i] eq 0}];
  if exists(i){i: i in known | i notin zeros[1]} then
    return i;
  end if;
  if assigned f`best_column then
    return f`best_column;
  end if;

  // Prefer a column that can be used for other newforms
  // (if not for all others, then prefer the first few) 
  // TO DO: newforms outside M that are computed via A
  newforms := [* f *];
  if assigned Mf`NewSpace and 
     assigned Mf`NewSpace`NewformDecomposition 
  then
    for N in Mf`NewSpace`NewformDecomposition do
      if assigned N`Eigenform then
        Append(~newforms, N`Eigenform);
      end if;
    end for;
  end if;
  if assigned Ambient(Mf)`NewformsOfDegree1 then
    newforms cat:= Ambient(Mf)`NewformsOfDegree1;
  end if;

  for ff in newforms do
    bool, v := HasAttribute(ff, "coords_raw");
    if bool then
      Append(~zeros, {Integers()| i : i in [1..n] | v[i] eq 0});
    end if;
  end for;
  best := 0;
  scores := [0 : i in [1..n]];
  for i := 1 to n do
    if i notin known then 
      new := known join {i};
      for z := 1 to #zeros do 
        if new subset zeros[z] then
          scores[i] := z-1;
          break z;
        end if;
        if z eq #zeros then
          best := i;
          break i;
        end if;
      end for;
    end if;
  end for;
  if best ne 0 then
    for j := 1 to #newforms do
      newforms[j]`best_column := best;
    end for;
  else
    _, best := Max(scores); 
    assert best gt 0;
  end if;
  return best;
end function;

intrinsic HeckeEigenvalue(f::ModFrmHilElt, P::Any) -> RngElt
{Given an eigenform f in a new space of Hilbert modular forms, this
 returns the eigenvalue for the Hecke operator at the prime P}
  
  M := Parent(f);
  F := BaseField(M);
  E := BaseField(f);

  require M`HeckeIrreducible: 
         "The first argument f must be a newform (constructed using Eigenform)";

  if F cmpeq Rationals() then
    if Type(P) eq RngIntElt then
      P := ideal< Integers() | P >;
    else
      require Type(P) eq RngInt : "The arguments are not compatible";
    end if;
  else
    require ISA(Type(P), RngOrdIdl) and NumberField(Order(P)) eq F :
            "The arguments are not compatible";
  end if;

  require IsPrime(P): "The second argument P should be prime";

  bool, e := IsDefined(f`hecke_eigenvalues, P);
  if bool then
    return e;
  end if;

  if IsDefinite(M) and assigned f`coords_raw then

    // compute v * (ith column of Tp) = e * v[i]
    v := f`coords_raw;
    n := Ncols(v);
    i := best_column(f, P);
    TP := HeckeOperatorDefiniteBig(TopAmbient(M), P : Columns:=[i]);
    assert Ncols(TP) eq n;
    TPi := ExtractBlock(TP, 1, i, n, 1);
    vTPi := v * ChangeRing(TPi, BaseRing(v));
    e := vTPi[1]/v[i];

  elif assigned f`coords_wrt_parent then

    // TO DO: correct coercions for all cases
    v := f`coords_wrt_parent;
    TP := HeckeOperator(M, P);
    vTP := v * ChangeRing(TP, BaseRing(v));
    assert exists(i){i : i in [1..Ncols(v)] | v[i] ne 0};
    e := vTP[i]/v[i];
    error if vTP ne e*v, 
         "Form does not seem to be an eigenform!" * please_report;

  elif assigned f`coords_wrt_ambient then
    
    // TO DO: correct coercions for all cases
    v := f`coords_wrt_ambient;
    TP := HeckeOperator(M`Ambient, P);
    vTP := v * ChangeRing(TP, BaseRing(v));
    assert exists(i){i : i in [1..Ncols(v)] | v[i] ne 0};
    e := vTP[i]/v[i];
    error if vTP ne e*v, 
         "Form does not seem to be an eigenform!" * please_report;

  elif assigned f`red_coords_wrt_ambient then
    
    TP := HeckeOperator(M`Ambient, P);
    EK := f`EK;

    // TO DO: check Q-integrality where needed in this

    // figure out bound needed so that LLL finds the shortest vector
D := Integers()! Discriminant(AbsoluteMinimalPolynomial(EK.1));
bound := D * Max(10^100, 10^(10*Degree(E)*Dimension(M)) );

    // figure out which primes to use
    NQprod := 1;
    num := 0;
    repeat
      num +:= 1;
      if num gt #f`red_coords_wrt_ambient then
        get_red_vector(EK, f`tEK, f`eEK, ~f`red_coords_wrt_ambient : NUM:=5);
      end if;
      NQprod *:= AbsoluteNorm(f`red_coords_wrt_ambient[num][1]);
    until NQprod gt bound;
printf "Using %o primes for eigenvalue congruences\n", num;

    // Multiply e by D here, divide by D at the very end
    Qs := [];
    eQs := [];
    for n := 1 to num do 
      Q, resQ, vQ := Explode(f`red_coords_wrt_ambient[n]);
      TPQ := reduction(TP, Q : res:=resQ);
      // TO DO: cache TPQ on M`Ambient 
      vTPQ := vQ * TPQ;
      assert exists(i){i : i in [1..Ncols(vQ)] | vQ[i] ne 0};
      eQ := vTPQ[i]/vQ[i];
      error if vTPQ ne eQ*vQ, 
           "Form does not seem to be an eigenform!" * please_report;
      DeQ := (D@resQ) * eQ;
      Append(~Qs, Q);
      Append(~eQs, DeQ @@ resQ);
    end for;
    e0 := CRT(eQs, Qs);

    // Find the shortest integral element that satisfies the congruences
    // TO DO: 
    //  -- work over E not EK
    //  -- avoid CRT ?
    //  -- use correct estimates on possible denominator 
    //     (first use what is likely, then as fallback use what is rigorous)
    //  -- maybe shortcut when e = 0 ?
prec := 10^3;
    Qprod := &* Qs;
assert NumberField(Order(Qprod)) eq EK;
assert Degree(EK) gt 1;
    OEK := Order(Qprod);
    FOEK := FieldOfFractions(OEK);
    L, toL := MinkowskiLattice(Qprod : Precision:=prec);
    L, tr := LLL(L);
assert NumberField(Parent(e0)) eq EK;
    e0 := FOEK! e0;
    s := Denominator(e0) * Minimum(Qprod);
    eR := (s*e0) @ toL;
    //coords := Coordinates(eR); // doesn't work, neither does Solution
    coords := Vector(eR) * BasisMatrix(L)^-1;
    eL := [c/s : c in Eltseq(coords)];
    l := [Round(c) : c in eL]; // closest vector, so |l-eL| should be minimal
    // TO DO: naive assertion that it was pretty close to a lattice point
    // Check is small enough: if so, then it is the only element 
    // in the congruence class small enough to be the eigenvalue)
    // TO DO ...
    ltr := Vector(l)*tr;
    lEK := &+ [ltr[i]*B[i] : i in [1..#B]] where B is Basis(Qprod);
    De := e0 - lEK;
    // finally divide by D again
    e := De/D;

  else 
    error "The given eigenform was not set up correctly!" * please_report;
  end if;

  ee := e; // this is an aid for debugging 
  // Ensure e is in the hecke eigenvalue field
  e := E! e;
if M`HeckeMethod gt 3 then
  try
    // Check the eigenvalue bounds
    assert IsIntegral(e);
    ebound := HeckeEigenvalueBound(M, P);
    assert forall{v : v in InfinitePlaces(E) | Abs(Evaluate(e,v)) le ebound};
  catch ERR
    error "Eigenvalue computation failed!!!" * please_report;
  end try;
end if;
  
  f`hecke_eigenvalues[P] := e;
  return e;
end intrinsic;


/////////////////////////////////////////////////////////////////////
// New stuff for degree 1 newforms
// (improvements in progress)

function HeckeAlgebraGenerators(M : minimal:=true)

  if Dimension(M) eq 0 then
    return [PowerIdeal(Integers(BaseRing(M))) | ];
  end if;

  _ := hecke_algebra(M : minimal:=minimal);
  return M`hecke_algebra[2];
end function;


// For definite weight 2 ambient space, construct raw space.
// Just a stupid hacky version for now.

declare attributes ModFrmHil : RawSpace, include_eis;

function RawSpace(M)

  if assigned M`RawSpace then
    return M`RawSpace;
  end if;

  bool, k := IsParallelWeight(M);
  assert bool and k eq 2 and IsDefinite(M) and not assigned M`Ambient;

  B := BasisMatrixDefinite(M : EisensteinAllowed);
  assert B cmpeq IdentityMatrix(BaseRing(B), Nrows(B));

  Mraw := HMF0(BaseField(M), Level(M), NewLevel(M), DirichletCharacter(M), 
               Weight(M), CentralCharacter(M));
  Mraw`QuaternionOrder   := M`QuaternionOrder;
  Mraw`rids              := M`rids;
  if assigned M`ModFrmHilDirFacts then // iff NewLevel ne Level ???
    Mraw`splitting_map     := M`splitting_map;
    Mraw`ModFrmHilDirFacts := M`ModFrmHilDirFacts;
  end if;
  Mraw`weight_dimension  := M`weight_dimension;
  Mraw`weight_base_field := M`weight_base_field;

  Mraw`Dimension := Nrows(B);
  Mraw`basis_is_honest := true;
  Mraw`basis_matrix := B;
  Mraw`basis_matrix_inv := B;
  Mraw`basis_matrix_big := B;
  Mraw`basis_matrix_big_inv := B;

  Mraw`include_eis := true;

  M`RawSpace := Mraw;
  return Mraw;

end function;

//////////////////

declare attributes FldNum: NumbersOfNewformsOfDegree1;

function number_of_weight2_newforms_of_degree1(N)

  F := NumberField(Order(N));

  if not assigned F`NumbersOfNewformsOfDegree1 then
    F`NumbersOfNewformsOfDegree1 := AssociativeArray();
  end if;

  bool, n := IsDefined(F`NumbersOfNewformsOfDegree1, N);
  if not bool then
    M := HilbertCuspForms(F, N, 2);
    n := #NewformsOfDegree1(M);
    F`NumbersOfNewformsOfDegree1[N] := n;
  end if;
  return n;

end function;

//////////////////

declare attributes ModFrmHil : NewformsOfDegree1;

intrinsic NewformsOfDegree1(M::ModFrmHil) -> List
{Returns the newforms in M that have rational Fourier coefficients}

  require NewformsOfDegree1Implemented(M) :
          "Implemented only for spaces of parallel weight 2";
  assert Seqset(Weight(M)) eq {2};

  if Dimension(M) eq 0 then
    return [* *];

  elif assigned M`NewformsOfDegree1 then
    return M`NewformsOfDegree1;

  elif assigned M`NewformDecomposition then
    return [* Eigenform(N) : N in M`NewformDecomposition | Dimension(N) eq 1 *];

  elif IsBianchi(M) then
    return [* Eigenform(N) : N in NewformDecomposition(M) | Dimension(N) eq 1 *];
    // TO DO but not important
  end if;

  // Replace M by a new subspace of M with same ambient, if desirable
  bool, NS := HasAttribute(M, "NewSubspaces");
  if bool then
    NS := [t : t in NS | t[1] subset NewLevel(M) and t[1] ne NewLevel(M) and
                assigned t[2]`Ambient and IsIdentical(t[2]`Ambient, M) and
                assigned t[2]`basis_matrix and assigned t[2]`basis_matrix_inv];
    if #NS gt 0 then
      _, i := Max([Norm(t[1]) : t in NS]);
      return NewformsOfDegree1(NS[i,2]);
    end if;
  end if;

  // If definite weight 2 ambient, compute on the raw space
  // TO DO: store HeckeBig on one space only (and avoid hacky copying here)
  bool, k := IsParallelWeight(M);
  raw := bool and k eq 2 and IsDefinite(M) and not assigned M`Ambient;
  if raw then
    M0 := M;
    M := RawSpace(M0);
    /*
    M`Hecke := M0`HeckeBig;
    M`HeckeColumns := M0`HeckeBigColumns;
    */
  end if;

  vprint ModFrmHil: "NewformsOfDegree1:";
  time0 := Cputime();
  IndentPush();

  Q := Rationals();

  SetRationalBasis(M);
  assert hecke_matrix_field(M) eq Q;

  F  := BaseField(M);
  ZF := Integers(F);
  N  := Level(M);

  old_sizes := {* #Divisors(N div N0) ^^ number_of_weight2_newforms_of_degree1(N0)
                : N0 in Divisors(N) | N0 ne N *};
  vprint ModFrmHil:
    "Oldforms of degree 1 should appear with multiplicities", old_sizes;

  S := 0;
  p := 1;
  done := false;
  while not done do
    p := p + 1;
    if not IsPrime(p) then continue; end if;
    Ps := [t[1] : t in Factorization(p*ZF)];
    for P in Ps do
      if Norm(P) ne p or Norm(P + N) ne 1 then
        continue;
      end if;

      B  := Floor(HeckeEigenvalueBound(M, P));
      TP := ChangeRing(HeckeOperator(M, P), Q);

      if Type(S) eq RngIntElt then

        vprintf ModFrmHil: "Eigenspaces for prime of norm %o, bound %o : ", Norm(P), B;
        vtime ModFrmHil:
        S := [* Eigenspace(TP, e) : e in [-B..B] *];
        S := [* W : W in S | Dimension(W) gt 0 *];
        vprintf ModFrmHil: "Dimensions %o\n", [ Dimension(W) : W in S ];

      else

        S0 := [* W : W in S | Dimension(W) gt 1 *];
        S  := [* W : W in S | Dimension(W) eq 1 *];
        vprintf ModFrmHil: "Intersect with eigenspaces for norm %o, bound %o : ", Norm(P), B;
        vtime ModFrmHil:
        for W in S0 do
          BW := BasisMatrix(W);
          WTP := BW * TP;
          for e in [-B..B] do
            K := KernelMatrix(WTP - e*BW);
            if Nrows(K) gt 0 then
              Append(~S, RowSpace(K*BW) );
            end if;
          end for;
        end for;
        vprintf ModFrmHil: "Dimensions %o\n", {* Dimension(W) : W in S *};

      end if;

      W_sizes := {* Dimension(W) : W in S | Dimension(W) gt 1 *};
      /* TO DO check (this attempt is wrong; it's hard)
      assert #os le #Ws and
             forall{i : i in [1..#os] | os[i] le Ws[i]}
             where os := Sort(Sequence(old_sizes))
             where Ws := Sort(Sequence(W_sizes));
      */
      done := old_sizes eq W_sizes;
      if done then
        break;
      end if;

    end for;
  end while;

  S  := [* W : W in S | Dimension(W) eq 1 *];

  BM := basis_matrix(M); // note reassignment of M in raw case

  if raw then
    M := M0;
    // get rid of Eisenstein forms
    E := RowSpace(EisensteinBasis(M));
    S := [* W : W in S | not W subset E *];
  end if;

  if not assigned F`NumbersOfNewformsOfDegree1 then
    F`NumbersOfNewformsOfDegree1 := AssociativeArray();
  end if;
  F`NumbersOfNewformsOfDegree1[Level(M)] := #S;

  IndentPop();
  vprintf ModFrmHil: "NewformsOfDegree1: %os\n", Cputime(time0);

  // Set up newform spaces and eigenforms

  NF := [* *];

  for W in S do
      // replicate what gets done in NewformDecomposition

      N := HMF0(BaseField(M), Level(M), Level(M), DirichletCharacter(M), 
                 Weight(M), CentralCharacter(M));
      N`Ambient := TopAmbient(M);  // only used to find the raw space
      N`is_new := true;
      N`HeckeIrreducible := true;
      N`hecke_matrix_field := Q;
      if raw then
          assert IsId(BM);
          N`basis_matrix := BasisMatrix(W);
          N`basis_is_honest := true;
      else
          N`basis_matrix := ChangeRing(BasisMatrix(W), BaseRing(BM)) * BM;
          N`basis_is_honest := basis_is_honest(M);
      end if;
      N`Dimension := 1;
      N`HeckeMethod := 1;

      Append(~NF, Eigenform(N));
  end for;

  M`NewformsOfDegree1 := NF;
  return NF;

end intrinsic;


//////////////////////////////////////////////////////////////////////////
// Routines for arbitrary Hecke modules: splitting off 'oldspaces'
//////////////////////////////////////////////////////////////////////////

import "../ModFrm/operators.m" : field_of_fractions;

// Given a subspace V of the underlying vector space of M, 
// returns matrix for restriction of HeckeOperator(M, P) to V 
// (assuming this sends V into V)

function hecke_on_subspace(V, M, P)
   VM, VMtoM := VectorSpace(M);
   B := basis_matrix(M);
   TPM := HeckeOperator(M, P);
   TPV := Solution(B, B*TPM);
   return TPV;
end function;


intrinsic DecompositionOldAndNew( M::Any, M0::Any : 
                                  old_dimension:=-1, old_only:=false, 
                                  bound:=Infinity(), primes:=[] ) 
       -> ModTupFld, ModTupFld
{
Decomposition of the Hecke module M as a direct sum of the \'oldspace\' relative 
to M0 (the largest Hecke submodule of M whose irreducible submodules appear in M0), 
and the complementary submodule.  
These are returned as subspaces of the underlying vector space of M.
Both M and M0 are assumed to be semisimple, and to satisfy the same properties
regarding dimensions of old and new spaces that hold for modular forms.
At least one of the optional arguments ('old_dimension' or 'primes' or 'bound') 
must be provided.
The routine will terminate as soon as any of the following hold:
(i) the dimension of the oldspace is <= the specified 'old_dimension',
(ii) the Hecke action for all specified 'primes' has been used (or if 'primes'
     are not specified, all good primes with norm up to the specified 'bound').
}

   require old_dimension ge 0 or bound lt Infinity() or not IsEmpty(primes) :
          "At least one of the optional arguments ('old_dimension' or 'primes' or 'bound') must be specified.";
   require BaseRing(M0) eq BaseRing(M) : "The given spaces must have the same base ring";

   F := field_of_fractions(BaseRing(M));
   FF := hecke_matrix_field(M);
   N := Level(M) meet Level(M0);

   if ISA(Type(F), FldAlg) then
      require IsAbsoluteField(F) : "The base field must be an absolute extension of Q";
   end if;

   // Process the varargs
   old_dimension := Max(0, old_dimension);
   if IsEmpty(primes) then 
      if bound eq Infinity() then
         b := 10;
         primes_specified := false;
      else
         b := bound;
         primes_specified := true;
      end if;
      primes := PrimesUpTo(b, F : coprime_to:=N );
   else
      // we just use the given primes and ignore the bound
      primes_specified := true;
      require forall{P : P in primes | Minimum(P + N) eq 1} : 
             "The specified primes should be prime to the level of both spaces";
   end if;

   vprintf ModFrmHil: "Computing old%o spaces for level %o, %o of dimension %o, %o\n",
                      old_only select "" else " and new", 
                      Norm(Level(M)), Norm(Level(M0)), Dimension(M), Dimension(M0); 

   V := VectorSpace(FF, Dimension(M));
   Vold := V;
   Vnew := sub< V | >;
   p := 0;
   while Dimension(Vold) gt old_dimension do 
      p +:= 1;
      if p gt #primes then
         if primes_specified then 
            break;
         else
            repeat 
               b +:= 100;
               primes := PrimesUpTo(b, F : coprime_to:=N );
            until #primes ge p;
         end if;
      end if;
      P := primes[p];

      vprintf ModFrmHil: "Comparing Hecke for prime of norm %o\n", Norm(P);

      // Since M0 is semisimple, it suffices to use the minimal poly of T0
      // TO DO: better, eg take kernel on Vold only.
      mu := HeckeCharacteristicPolynomial(M0, P);
      mu := SquarefreePart(mu); // = the min poly
      mu := PolynomialRing(FF)! mu;
      T := HeckeOperator(M, P);
      T := MatrixAlgebra(FF,Nrows(T))! T;

      vprintf ModFrmHil, 2: "[OldAndNew] Evaluating minimal polynomial: "; 
      vtime ModFrmHil, 2:
      muT := Evaluate(mu, T);

      vprintf ModFrmHil, 2: "[OldAndNew] Kernel: "; 
      vtime ModFrmHil, 2:
      KmuT := Kernel(muT);

      vprintf ModFrmHil, 2: "[OldAndNew] Intersection: "; 
      vtime ModFrmHil, 2:
      Vold meet:= KmuT;

      if not old_only then
         vprintf ModFrmHil, 2: "[OldAndNew] Image: "; 
         vtime ModFrmHil, 2:
         ImuT := Image(muT);

         vprintf ModFrmHil, 2: "[OldAndNew] Sum: "; 
         vtime ModFrmHil, 2:
         Vnew +:= ImuT;
      end if;
   end while;

   if old_only then
      return Vold, _;
   else
      return Vold, Vnew;
   end if;
end intrinsic;


// Create full space with level N of the same flavour of modular forms as M
function space_with_level(M, N, Nnew) 
  if ISA(Type(M), ModFrmHil) then 
    F := BaseField(M);
    k := Weight(M);

      M1 := HilbertCuspForms(F, N, k);
      if not assigned M1`QuaternionOrder and assigned M`QuaternionOrder 
         and IsSuitableQuaternionOrder(M`QuaternionOrder, M1) 
      then
        set_quaternion_order(M1, M`QuaternionOrder);
      end if;
      MN := NewSubspace(M1, Nnew);
      if assigned M`QuaternionOrder and not assigned MN`QuaternionOrder 
         and IsSuitableQuaternionOrder(M`QuaternionOrder, MN) 
      then
        set_quaternion_order(MN, M`QuaternionOrder);
      end if;

    return MN;
  end if;
  error "Not implemented for that kind of modular forms";
end function;


intrinsic NewAndOldSubspacesUsingHeckeAction(M::Any, p::Any : OldOnly:=false) -> .
{Given a Hecke module M of level N and a prime p, this returns the p-new subspace of M,
and the p-old subspace, as subspaces of the underlying vector space of M.  By definition, 
the p-old subspace is the space spanned by all images in M of the space Mp of level N/p.
It is obtained by computing the dimensions of all oldspaces, and computing the Hecke action
on M and Mp for sufficiently many primes.  M is assumed to be semisimple, and to satisfy
the same properties regarding dimensions of old and new spaces that hold for modular forms}

   if Type(p) eq RngIntElt then
     p := p*Integers();
   end if;

   N := Level(M);
   Nnew := NewLevel(M);
   require N subset p : "The space is already new at p, so this should not be called.";
   require Norm(Nnew + p) eq 1 : "The given space should have new level prime to p"; 

   // Work out dimension of the p-old space by inclusion-exclusion
   Mp := space_with_level(M, N/p, Nnew);
   if Dimension(Mp) eq 0 then
      d := Dimension(M);
      F := hecke_matrix_field(M);
      Mnew := VectorSpace(F, d);
      Mold := sub< Mnew | >; 
      return Mnew, Mold;
   end if;

   old_dimension := 2*Dimension(Mp);
   if N subset p^2 then
     Mp2 := space_with_level(M, N/p^2, Nnew);
     old_dimension -:= Dimension(Mp2);
   end if;

   Mold, Mnew := DecompositionOldAndNew(M, Mp : old_dimension:=old_dimension, old_only:=OldOnly); 
   if OldOnly then
     return Mold;
   else
     return Mnew, Mold;
   end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/* SCRAPS

// code for getting an honest eigenvector when we don't have an honest basis

       if assigned MA`eisenstein_basis then
         Eis := ChangeRing(MA`eisenstein_basis, EK);
         // MA differs from the raw space that we actually compute with 
         // only because we quotiented out the Eisenstein subspace.
         // MA`basis_matrix is a complement of Eis, but it is not an 
         // "honest" Hecke-invariant complement.
         // Therefore v1 is not an honest eigenvector in the raw space, 
         // but the honest eigenvector lies in the coset v1 + Eis
         // (because v is an honest eigenvector in MA).
         // So we solve for w such that 
         //    (v1 + w*Eis) * t = e * (v1 + w*Eis)
         // Rearranging this, 
         //    w * (Eis*t - e*Eis) = v1 * (e*I - t) 
         // If the solution is not unique, then e is also the eigenvalue of
         // some Eisenstein, which means the choice of t was very unlucky!
         primes, comb := Explode(MA`hecke_algebra_generator);
         big := MA`HeckeBig;
         t1EK := ChangeRing( &+ [comb[i]*big[primes[i]] : i in [1..#primes]], EK);
         bool, w, wker := IsConsistent( Eis*t1EK - eEK*Eis, eEK*v1 - v1*t1EK );
         error if not bool,
              "Something is badly wrong in Eigenform!" * please_report;
         error if Dimension(wker) ne 0, 
              "Unlucky choice of Hecke algebra generator!" * please_report;
         nf`coords_raw := v1 + w*Eis;
       end if;

*/
