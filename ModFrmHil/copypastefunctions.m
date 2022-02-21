forward IsBianchi;
forward Ambient;
import "finitefield.m" : reduction_mod_random_large_split_prime;
/********************   from hecke.m    *********************/

debug := false;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

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

function basis_is_honest(M)
  return assigned M`basis_is_honest and M`basis_is_honest
         or assigned M`basis_matrix and not assigned M`Ambient;
         // (an ambient is automatically honest)
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


/********************   from hackobj.m    *********************/
function IsBianchi(M)
  return ISA(Type(M), ModFrmBianchi);
end function;

function Ambient(M)
  if assigned M`Ambient then
    return M`Ambient;
  else
    // must have decided how to compute M
    assert assigned M`QuaternionOrder or IsBianchi(M);
    return M;
  end if;
end function;

function TopAmbient(M)
  top := M;
  while assigned top`Ambient do
    top := top`Ambient;
  end while;
  return top;
end function;

// create Bianchi space with given ambient
function BMF_with_ambient(A)
  assert not assigned A`Ambient;
  M := New(ModFrmBianchi);
  M`Ambient := A;
  M`Field := A`Field;
  M`Level := A`Level;
  M`DirichletCharacter := 1;
  M`Weight := [2];
  M`CentralCharacter := 0;
  M`is_cuspidal := true; // always true, currently
  M`homology_coefficients := A`homology_coefficients;
  M`ModFrmData := A`ModFrmData;
  M`LevelData := A`LevelData;
  M`Hecke := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  return M;
end function;

function HMF0(F, N, Nnew, Chi, k, C)
  M := New(ModFrmHil);
  M`Field := F;
  M`Level := N;
  M`NewLevel := Nnew;
  M`DirichletCharacter := Chi;
  M`Weight := k;
  M`CentralCharacter := C;
  assert C eq Max(k) - 2; // currently
  M`is_cuspidal := true; // always true, currently
  M`Hecke    := AssociativeArray();
  M`HeckeBig := AssociativeArray();
  M`HeckeBigColumns := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  M`AL       := AssociativeArray();
  M`DegDown1 := AssociativeArray();
  M`DegDownp := AssociativeArray();
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;

/********************   from definite.m    *********************/
// Tensor product is associative; for efficiency always do
// TensorProduct(small_mat, large_mat)

function weight_map_arch(q, splittings, K, m, n)
   d := #m;
   M := MatrixRing(K,1)!1;
   for l := d to 1 by -1 do
      if m[l] eq 0 and n[l] eq 0 then
         // don't need to modify M
         continue;
      else
         matq := splittings[l](q);
         if n[l] eq 0 then
            M *:= Determinant(matq)^m[l];
         else
            if n[l] eq 1 then
               Ml := matq;
            else
               Ml := SymmetricPower2(matq, n[l]);
            end if;
            if m[l] ne 0 then
               Ml *:= Determinant(matq)^m[l];
            end if;
            if l eq d then
               M := Ml;
            else
               M := TensorProduct(Ml, M);
            end if;
         end if;
      end if;
   end for;
   return M;
end function;
