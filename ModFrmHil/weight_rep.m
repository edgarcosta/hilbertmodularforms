declare attributes AlgQuat : Splittings;

function GetOrMakeP1(Gamma, N)
  // Gamma - GrpPSL2
  // N - RngOrdIdl
  //
  // Returns the cached output of ProjectiveLine(Gamma, N)
  Z_F := Order(N);
  Z_FN := quo<Z_F | N>;
  if not assigned Gamma`P1s_dict then
    Gamma`P1s_dict := AssociativeArray();
  end if;
  if IsDefined(Gamma`P1s_dict, N) then
    return Explode(Gamma`P1s_dict[N]);
  else
    P1N, P1Nrep := ProjectiveLine(Z_FN);
    Gamma`P1s_dict[N] := <P1N, P1Nrep>;
    return P1N, P1Nrep;
  end if;
end function;

//-------------
//
// Compute the set of cosets.
//
//-------------

function LeftToRightCosets(Gamma, N, Z_FN, iota, P1N, cosets, P1Nrep)
  // Given a sequence of coset representatives for
  // Gamma(1) / Gamma(N), return a sequence of representatives
  // for Gamma(N) \ Gamma(1).
  rcosets := cosets;
  cosetsinv := [c^(-1) : c in cosets];
  for c in cosetsinv do
    v := iota(c)[2];
    // Gamma`P1Ns[N] is a tuple, the second entry
    // is a map taking v to its standard representative
    // in P1N.
    _, v := GetOrMakeP1(Gamma, N)[2](v, false, false);
    rcosets[Index(Gamma`P1N, v)] := c;
  end for;
  return rcosets;
end function;

function Gamma0Cosets(Gamma, N, Z_FN, iota, P1, P1rep : LeftCosets:=true)
  if not assigned Gamma`LevelCosets_new then
    Gamma`LevelCosets_new := AssociativeArray();
  end if;

  if IsDefined(Gamma`LevelCosets_new, N) then
    if LeftCosets then
      return Gamma`LevelCosets_new[N];
    else
      return LeftToRightCosets(Gamma, N, Z_FN, iota, P1, Gamma`LevelCosets_new[N], P1rep);
    end if;
  end if;

  if Norm(N) eq 1 then
    return [BaseRing(Gamma)!1];
  end if;

  vprintf ModFrmHil: "Computing cosets ..................................... ";
  time0 := Cputime();

  O := BaseRing(Gamma);
  B := Algebra(O);

  D := Parent(Gamma`ShimFDDisc[1]);
  mU := Gamma`ShimFDSidepairsDomain;
  i := 1;
  while i lt #mU do
    if mU[i] eq mU[i+1] then
      Remove(~mU,i);
    end if;
    i +:= 1;
  end while;
  mU := [<mU[i], i> : i in [1..#mU]];

  frontier := [<O!1,[]>];
  cosets := [<O!1,[Integers()|]> : i in [1..#P1]];
  cosetcnt := 1;

  _, v := P1rep(iota(O!1)[2], false, false);
  ind1 := Index(P1, v);

  while frontier ne [] do
    newfrontier := [];
    for delta in frontier do
      for g in mU do
        gamma := delta[1]*g[1];

        v := iota(gamma)[2];
        _, v := P1rep(v, false, false);
        ind := Index(P1, v);
        if ind ne ind1 and cosets[ind][1] eq 1 then
          // Optionally, we could keep (and return) the elements in Gamma0N that
          // we find, but as it stands now, this wastes precious time as we
          // work with the induced module, anyway.
          cosets[ind] := <gamma, delta[2] cat [g[2]]>;
          Append(~newfrontier, <gamma, [g[2]] cat delta[2]>);
          cosetcnt +:= 1;
        end if;
      end for;
    end for;
    frontier := newfrontier;
  end while;

  if #Factorization(N) gt 0 then
    assert cosetcnt eq Norm(N)*&*[1+1/Norm(pp[1]) : pp in Factorization(N)];
  end if;
  for i := 1 to #P1 do
    v := iota(cosets[i][1])[2];
    _, v := P1rep(v, false, false);
    assert v eq P1[i];
  end for;

  Gamma`LevelCosets_new[N] := [c[1] : c in cosets];
  vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  return Gamma0Cosets(Gamma, N, Z_FN, iota, P1, P1rep : LeftCosets:=LeftCosets);
end function;

//-------------
//
// Right action functions.
//
//-------------

// Gamma`LevelRPAs_new stores a dictionary keyed by level N.
// Gamma`LevelRPAs_new[N] contains a dictionary keyed by 
// the integers [-#gens ..., -1, 1, ..., #gens], where gens is
// Generators(Group(Gamma)).
//
// At a positive integer i, the dictionary stores the permutation matrix 
// induced by right action of the ith generator on coset representatives
// (which should be something like Gamma(N) \ Gamma). 
function RightPermutationActions(Gamma, N, Z_FN, iota, P1N, cosets, P1Nrep)
  if not assigned Gamma`LevelRPAs_new then
    Gamma`LevelRPAs_new := AssociativeArray();
  end if;

  if IsDefined(Gamma`LevelRPAs_new, N) then
    return Gamma`LevelRPAs_new[N];
  end if;

  vprintf ModFrmHil: "Computing right permutation actions .................. ";
  time0 := Cputime();

  U, m := Group(Gamma);
  RPAs := AssociativeArray();
  P1N, P1Nrep := GetOrMakeP1(Gamma, N);
  for i := 1 to #Generators(U) do
    delta := Quaternion(m(U.i));
    perm := [];
    for alphai in cosets do
      _, v := P1Nrep(iota(alphai*delta)[2], false, false);
      Append(~perm, Index(P1N, v));
    end for;
    RPAs[i] := PermutationSparseMatrix(Integers(), SymmetricGroup(#P1N)!perm);
    RPAs[-i] := PermutationSparseMatrix(Integers(), SymmetricGroup(#P1N)!perm^-1);
  end for;

  vprintf ModFrmHil: "Time: %o\n", Cputime(time0);

  Gamma`LevelRPAs_new[N] := RPAs;
  return RPAs;
end function;

intrinsic Splittings(B::AlgQuat) -> SeqEnum[Map], FldNum, FldNum
  {
    input:
      B - A quaternion algebra defined over a degree n field F.
    returns:
      A SeqEnum of n maps from B to M2(K), where K is the minimal field
      over which such a sequence can be defined. Each map in the sequence
      corresponds to one of the infinite places of F. 

      We also return the field K as well as (TODO abhijitm no clue why but 
      I didn't want to change it) an unoptimized version of K. 
  }
  if assigned B`Splittings then
    return Explode(B`Splittings);
  end if;

  F := BaseField(B);
  // define weight_base_field = extension K/F containing Galois closure of F and 
  // containing a root of every conjugate of the minimal polynomial of B.1
  if assigned F`SplittingField then
    K,rts := Explode(F`SplittingField);
  else
    K,rts := SplittingField(F : Abs := true, Opt := false);
    F`SplittingField := <K, rts>;
  end if;
  embeddings_F_to_K := [hom<F->K | r> : r in rts];
  B1coeffs := Coefficients(MinimalPolynomial(B.1));
  alphas := [K| ];
  for FtoK in embeddings_F_to_K do
    hh := PolynomialRing(K)! [c@FtoK : c in B1coeffs];
    if IsIrreducible(hh) then
       K := ext<K|hh>;
       alphas := ChangeUniverse(alphas,K) cat [K.1];
    else
       Append(~alphas, Roots(hh)[1][1]);
    end if;
  end for;
  // make weight_base_field an (optimized) absolute field, for efficiency in later calculations 
  weight_field := K; // names appears in verbose output 
                     // TODO abhijitm I don't really get why we can't let K be the optimized
                     // representation but I'm too lazy to think about it now and this is how
                     // it was so we return this separately. 
  K := AbsoluteField(K);
  K := OptimizedRepresentation(K);
  embeddings_F_to_K  :=  [hom<F->K | K!r> : r in rts]; // same embeddings, now into extended field K

  require B.1*B.2 eq B.3 : "We assume B.1 * B.2 == B.3 when defining\
    the splitting homomorphisms.";
  splitting_seq := [];
  for i := 1 to Degree(F) do
    h := embeddings_F_to_K[i];
    // need a splitting homomorphism (B tensor K) -> Mat_2(K) whose restriction to K is h 
    alpha := alphas[i];
    b := K! h(F!(B.2^2));
    iK := Matrix(K, 2, [alpha, 0, 0, -alpha]); 
    jK := Matrix(K, 2, [0, 1, b, 0]); 
    kK := iK*jK;
    assert K! h(B.3^2) eq (kK^2)[1,1]; 
    Append(~splitting_seq, 
        map< B -> MatrixRing(K,2)|
          q:-> h(s[1])+h(s[2])*iK+h(s[3])*jK+h(s[4])*kK where s := Eltseq(q) >);
  end for;
  B`Splittings := <splitting_seq, K, weight_field>;
  return splitting_seq, K, weight_field;
end intrinsic;
