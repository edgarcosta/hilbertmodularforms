freeze;

/**********************************************************************
*                                                                     *
*                   HILBERT MODULAR FORMS                             *
*                                                                     *
*  This file contains the basic admin for ModFrmHil                   *
*   -- definition of types: ModFrmHil and ModFrmHilElt                *
*   -- constructors of spaces: HilbertCuspForms and NewSubspace       *
*   -- functions to choose the algorithm and the QuaternionOrder      *
*   -- functions for accessing attributes                             *
*                                                                     *
*  Steve Donnelly                                                     *
*                                                                     *
***********************************************************************/

import "hecke.m" :
  basis_matrix,
  basis_is_honest,
  hecke_matrix_field;

import "definite.m":
  BasisMatrixDefinite,
  InnerProductMatrixBig;

import !"Geometry/BianchiNew/hackobj.m" : DimensionBianchi;

QuaternionOrderIntrinsic := QuaternionOrder; 

declare attributes ModFrmHil  : Diamond;
declare attributes AlgAssVOrd : ModFrmHils; 
declare attributes FldNum     : ModFrmHils;
declare attributes FldRat     : ModFrmHils;

/**********************************************************************
  ModFrmHil attributes
  Let M be a ModFrmHil over the FldNum F    
**********************************************************************/

declare type ModFrmHil [ModFrmHilElt];

declare attributes ModFrmHil :  

  Field,                     // = F = BaseField(M), required to be an absolute field (for efficiency)
  Level,                     // = Level(M) = an ideal in Integers(F)
  DirichletCharacter,        // always assigned: either the integer 1, or a GrpDrchNFElt with modulus Level(M)

  Weight,                    // = Weight(M) = a sequence of integers, corresponding to InfinitePlaces(F)
  CentralCharacter,          // Only used internally.

  NewLevel,                  // = NewLevel(M). M is the space of forms that are new at this level or higher
                             // (See intrinsic NewSubspace(M,I).  Must be assigned on creation)
  Dimension,                 

  QuaternionOrder,           // An order in a quaternion algebra (type AlgAssVOrd or AlgQuatOrd)
                             // If definite, should be maximal, and Dembele's algorithm will be used.
                             // If indefinite, the Greenberg-Voight implementation will be used.

  force_indefinite,          // Secret, not for public use

  Ambient,                   // This is a larger space on which Hecke operators are computed and stored.
                             // Hecke operators on M are obtained from those via M`basis_matrix_wrt_ambient.
                             // If not assigned but QuaternionOrder is assigned, M is its own ambient.
                             // If neither are assigned, we haven't yet decided how to compute M.

  //////  BASIS MATRICES  /////

  basis_matrix,              // The rows generate M inside the vector space V used to compute it 
  basis_matrix_inv,          // basis_matrix * basis_matrix_inv = identity
  basis_is_honest,           // IMPORTANT CONVENTION:
                             // Let B = basis_matrix.  
                             // The rowspace of B defines an image of M in some larger space.   
                             // This subspace is not required to actually be Hecke-invariant.  
                             // We only need that B maps isomorphically to V/C, where C is a  
                             // Hecke-invariant complement. 
                             // Bi = basis_matrix_inv is uniquely determined from B and C, by
                             //   B * Bi = identity
                             //   C * Bi = zero
                             // Therefore we obtain the Hecke action on V/C (wrt some basis) as
                             //   T = B * T_V * Bi 
                             
                             // Definition: we will say B is an "honest" basis_matrix if its 
                             // rowspace is a Hecke-invariant subspace.

                             // When B *is* honest, we do not require the second condition 
                             //   C * Bi = zero

                             // The reason for this convention is that in many situations, we know 
                             // the Hecke-invariant space C but not a Hecke-invariant complement B;  
                             // To compute honest B from C is expensive in general, by any method.

  basis_matrix_wrt_ambient,  // basis_matrix_wrt_ambient * Ambient`basis_matrix = basis_matrix
  basis_matrix_wrt_ambient_inv, // basis_matrix_wrt_ambient * basis_matrix_wrt_ambient_inv = identity
                             // The same convention as for basis_matrix must be observed.  
                             // These matrices must have BaseRing = hecke_matrix_field(Ambient(M))

  basis_matrix_big,          // The raw space in the definite case (see HilbertModularSpaceBasisMatrix).
  basis_matrix_big_inv,      // (It's an "honest" basis matrix: the space is invariant under the Hecke action)
  eisenstein_basis,

  InnerProduct,
  InnerProductBig,

  /////  HECKE MATRICES   /////

  Hecke,                     // Arrays indexed by primes p of Integers(F) 
  HeckeCharPoly,             //(initialized on creation)
  HeckeBig,
  HeckeBigColumns,           // Used in HeckeOperatorDefiniteBig

  AL,                        // Arrays indexed by primes dividing Level(M),
  DegDown1,                  // storing AtkinLehner and degeneracy operators
  DegDownp,
  ALBig,
  DegDown1Big,
  DegUp1Big,
  DegUppBig,

  hecke_matrix_field,        // The Hecke operators are matrices with entries in this field.
                             // Automatically assigned to be Q for parallel weight 2.
  hecke_matrix_field_is_minimal, // true iff hecke_matrix_field is the natural field (must be assigned).

  hecke_algebra,             // stores result of function hecke_algebra (this could change)
  hecke_algebra_generator,
  hecke_algebra_generator_eigenvalue,
  
  /////  NEW SUBSPACES   //////

  is_cuspidal,               // always true, currently (and must be initialized on creation)

  is_new,                    // true for spaces with NewLevel = Level

  FullSpace,                 // For a NewSubspace, this is the associated space with NewLevel = (1)
                             // DO NOT confuse with Ambient!

  NewSubspaces,              // List of tuples <I, MI> where MI is the space of NewLevel = I
                             // (this should be stored on the associated FullSpace)

  //////  EIGENSPACES   ///////

  HeckeMethod,               // [temp] method used in NewformDecomposition and Eigenform

  NewformDecomposition,      // = NewformDecomposition(M)
  NewSpace,                  // [temp?] the space whose NewformDecompostion this space is in

  HeckeIrreducible,          // True for spaces in the NewformDecomposition of a new space

  Eigenform,                 // = Eigenform(M), valid when HeckeIrreducible is true

  /////  STUFF FOR THE DEFINITE CASE 

  rids,                      // Sequence of right ideal class reps for M`QuaternionOrder, chosen and 
                             // ordered once and for all -- SHOULD ONLY BE ACCESSED VIA 'get_rids'.

  splitting_map,             // Homomorphism from QuaternionOrder(M) to 2x2 matrices over the residue ring 
                             // Integers(F)/d where d = Level(M)/Discriminant(Algebra(QuaternionOrder(M)))

  ModFrmHilDirFacts,         // Sequence of records of format ModFrmHilDirFact (defined in definite.m)

  weight_rep,                // The weight representation: B^* -> GL_2(K)^g -> GL(V_k).

  weight_dimension,          // The dimension of the weight space.

  weight_base_field;         // The base field of the weight representation,
                             // or Rationals() for parallel weight 2


/********************    Hacking for ModFrmHil    *********************/

function IsBianchi(M) 
  return ISA(Type(M), ModFrmBianchi);
end function;

function ideal_print_on_one_line(I, level)
  if Type(I) in {RngIntElt,FldRatElt} then
    printf "%o", I; return 0;
  elif Type(I) eq RngInt then 
    printf "%o", Minimum(I); return 0; 
  end if;
  gens := Generators(I);
  printf "Ideal of norm %o generated by ", Norm(I);
  for g := 1 to #gens-1 do printf "%o, ", gens[g]; end for;
  printf "%o", gens[#gens];
  return 0;
end function;

intrinsic Print(x::ModFrmHil, level::MonStgElt)
{}
  F := BaseField(x);

  assert assigned x`is_cuspidal;

  if x`is_cuspidal and assigned x`HeckeIrreducible and x`HeckeIrreducible then
    printf "Cuspidal newform space ";
  elif x`is_cuspidal and IsNew(x) and Norm(Level(x)) ne 1 then
    printf "New cuspidal space ";
  elif x`is_cuspidal then
    printf "Cuspidal space ";
  else 
    printf "Space ";
  end if;

  if IsBianchi(x) then
    printf "of Bianchi modular forms";
  else
    printf "of Hilbert modular forms";
  end if;

  if level ne "Minimal" then 
    printf " over";
    printf "\n    %o", BaseField(x);
    printf "\n    Level: "; 
    _ := ideal_print_on_one_line(Level(x), level); 
    if Norm(NewLevel(x)) ne 1 then 
      printf "\n    New level: ";
      _ := ideal_print_on_one_line(NewLevel(x), level); 
    end if;
    if x`DirichletCharacter cmpne 1 then
      printf "\n    Dirichlet character: %o", x`DirichletCharacter;
    end if;
    printf "\n    Weight: %o", Weight(x);
    if assigned x`Dimension then 
      printf "\n    Dimension %o", x`Dimension; 
    end if;
  end if;
  if level eq "Maximal" and assigned x`QuaternionOrder then 
    O := x`QuaternionOrder;
    printf "\ncomputed as automorphic forms on %o order in %o quaternion algebra of discriminant ", 
           IsMaximal(O) select "maximal" else "Eichler", 
           IsDefinite(Algebra(O)) select "definite" else "indefinite";
    _ := ideal_print_on_one_line( Discriminant(Algebra(O)), level);
  end if;
end intrinsic;

// TO DO: Provide Print too ???

intrinsic IsCoercible(x::ModFrmHil, y::.) -> BoolElt, .
{}
  if Type(y) eq ModFrmHilElt and Parent(y) cmpeq x then
    return true, y;
  end if;
  return false;
end intrinsic;

intrinsic 'in'(x::., y::ModFrmHil) -> BoolElt
{}
  if Type(x) ne ModFrmHilElt then
    return false, "The first argument should be a ModFrmHilElt";
  else
    return Parent(x) eq y;
  end if;
end intrinsic;


/*****************   Caching of spaces   *********************/

// Cache spaces on F and on the QuaternionOrder 
// iff assigned F`ModFrmHils 

intrinsic SetStoreModularForms(F::FldNum, v::BoolElt)
{If true, spaces of modular forms over F are never deleted.
(This may save time when computing other spaces over F, 
but may use a lot of memory.)}
  
  if v and not assigned F`ModFrmHils then
    F`ModFrmHils := AssociativeArray();
  elif not v and assigned F`ModFrmHils then
    for N in Keys(F`ModFrmHils), M in F`ModFrmHils[N] do
      if assigned M`QuaternionOrder and 
        assigned M`QuaternionOrder`ModFrmHils 
      then
        delete M`QuaternionOrder`ModFrmHils;
      end if;
    end for;
    delete F`ModFrmHils;
assert not assigned F`ModFrmHils;
  end if;
end intrinsic;

intrinsic ClearStoredModularForms(F::FldNum)
{Clear the cache of spaces of modular forms over F}

  if assigned F`ModFrmHils then
    F`ModFrmHils := AssociativeArray();
  end if;
end intrinsic;


/*****************   Constructors for ModFrmHil   *********************/

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

// Discriminant of an algebra or order returned as an ideal 
function _Discriminant(A)
  disc := Discriminant(A);
  if Type(disc) eq FldRatElt then disc := Integers()!disc; end if;
  if Type(disc) eq RngIntElt then disc := disc*Integers(); end if;
  return disc;
end function;

intrinsic IsSuitableQuaternionOrder(QO::AlgAssVOrd, M::ModFrmHil) -> BoolElt, MonStgElt
{True iff the given quaternion order can by used to compute the given space of Hilbert modular forms.
If false, also returns a string explaining why}

  F := BaseField(M);
  if not ISA(Type(QO), AlgAssVOrd) then 
    return false, "The optional argument QuaternionOrder should be an order in a quaternion algebra"; 
  end if;
  A := Algebra(QO);
  if BaseField(A) ne F then
    return false, "\nInvalid QuaternionOrder given: its base field should be the base field of the Hilbert modular forms space";
  elif IsDefinite(A) and Type(F) eq FldRat then
    return false, "\nModular forms over Rationals() are not supported by the 'definite' algorithm."*
                  "\nUse RationalsAsNumberField() instead.";
  end if;

  ram, inf_ram := FactoredDiscriminant(A);

  if #ram + #inf_ram eq 0 then
    return false, "\nInvalid QuaternionOrder given (must be ramified at either the infinite place or some finite prime)";
  elif not IsMaximal(QO) then
    return false, "\nInvalid QuaternionOrder given (it should be a maximal order)";
  elif not NewLevel(M) subset _Discriminant(A) then
    return false, "\nInvalid QuaternionOrder given (this quaternion algebra is ramified at some finite primes,"*
                  " so it can be used only to compute the NewSubspace relative to those primes)";
  
  elif #inf_ram eq Degree(F) then // DEFINITE
    if not IsIntegral(Level(M)/Discriminant(QO)) then
      return false, "\nInvalid QuaternionOrder given (its discriminant must divide the level of the space)";
    elif Norm(Discriminant(A) + Level(M)/Discriminant(A)) ne 1 then
      return false, "\nInvalid QuaternionOrder given (when the order is definite, the primes dividing the"*
                    " discriminant of the quaternion algebra must divide the level of the space exactly once)";
    end if;

  else // INDEFINITE
    if #inf_ram ne Degree(F) - 1 then
      return false, "\nInvalid QuaternionOrder given (it is unramifed at more than one infinite place)";
    elif Norm(_Discriminant(A) + Level(M)/_Discriminant(A)) ne 1 then
      return false, "\nInvalid QuaternionOrder given (when the order is indefinite, "*
                    "the discriminant of the quaternion algebra must exactly divide the level)";
    end if;
  end if;

  return true, _;
end intrinsic;

// NEVER assign M`QuaternionOrder by hand, use this instead!

procedure set_quaternion_order(M, QO)
   assert not assigned M`QuaternionOrder;
   assert not assigned M`Ambient;
   assert M`Field eq BaseRing(Algebra(QO));
   assert M`NewLevel eq _Discriminant(QO);
   M`QuaternionOrder := QO;

   // cache the space on QO, if caching is switched on
   if assigned M`Field`ModFrmHils then
     if not assigned QO`ModFrmHils then
       QO`ModFrmHils := AssociativeArray();
     end if;
     N := M`Level;
     if IsDefined(QO`ModFrmHils, N) then
       Append(~QO`ModFrmHils[N], M);
assert M in QO`ModFrmHils[N];
     else
       QO`ModFrmHils[N] := [M];
     end if;
   end if;
end procedure;

// Allow users to do this, but only with the check!
// TO DO: should also check if M`Ambient has a QuaternionOrder

intrinsic SetQuaternionOrder(M::ModFrmHil, QO::AlgAssVOrd)
{Sets QO as the quaternion order that will be used to compute the Hilbert modular forms M}
   if assigned M`QuaternionOrder then
     if IsIdentical(M`QuaternionOrder, QO) then 
       return;
     end if;
     error "QuaternionOrder already chosen for this space!\n" *
           "Hint: specify QuaternionOrder when creating the space.";
   end if;
   ok, message := IsSuitableQuaternionOrder(QO, M);
   error if not ok, message;
   set_quaternion_order(M, QO);
end intrinsic;

// silly tilde version for backwards compatibility
intrinsic SetQuaternionOrder(~M::ModFrmHil, QO::AlgAssVOrd)
{"} // "
   SetQuaternionOrder(M, QO);
end intrinsic;

intrinsic SetAlgorithm(M::ModFrmHil, Al::MonStgElt)
{Set the algorithm used to compute the space M of Hilbert modular forms.
The Al can be "Definite" or "Indefinite"};
   require not assigned M`QuaternionOrder : "Algorithm has already been selected";
   require Al in {"Definite", "definite", "Indefinite", "indefinite"} :
          "The second argument must be \"Definite\" or \"Indefinite\"";
   // Allow current value of force_indefinite to be overwritten
   // TO DO: force definite (not so important, since this is usually the default)
   if Al in {"Indefinite, indefinite"} then
      M`force_indefinite := true;
   end if;
end intrinsic;

// CACHING: M is cached on F = BaseField(M)
//      iff M is a fullspace ie NewLevel = 1
//      iff M is created by HMF
// (If M is a NewSubspace, it is cached on M`FullSpace)
// Also, M is cached on QO = QuaternionOrder(M)
//   iff M is an ambient ie NewLevel = Discriminant(QO)

// This returns the first cached space for N, k with QuaternionOrder = QO,
// or if QO = 0, the first cached space for N, k with QuaternionOrder assigned (preferably)

function is_cached_hmf(QO, F, N, k)
  if QO cmpne 0 and assigned QO`ModFrmHils and IsDefined(QO`ModFrmHils, N) then
    for M in QO`ModFrmHils[N] do
      if Weight(M) eq k then
        return true, M;
      end if;
    end for;
  end if;
  if assigned F`ModFrmHils and IsDefined(F`ModFrmHils, N) then
    Ms := [];
    for M in F`ModFrmHils[N] do 
      if Level(M) eq N and Weight(M) eq k then
        if QO cmpne 0 and assigned M`QuaternionOrder and IsIdentical(M`QuaternionOrder, QO) then
          return true, M;
        elif QO cmpeq 0 then 
          Append(~Ms, M);
        end if;
      end if;
    end for;
    if QO cmpeq 0 then
      if exists(M){M : M in Ms | assigned M`QuaternionOrder} then
        return true, M;
      elif #Ms gt 0 then
        return true, Ms[1];
      end if;
    end if;
  end if;
  return false, _;
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
  M`Diamond := AssociativeArray();
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;

// Constructor used for all spaces with NewLevel = 1

function HMF(F, N, k : Chi:=1, QuaternionOrder:=0)

  // TO DO: errors should be passed back to the calling intrinsic

if Chi cmpeq 1 then
  bool, M := is_cached_hmf(QuaternionOrder, F, N, k);
  if bool then
    return M;
  end if;
end if;

  bool, _, _, C := IsArithmeticWeight(F, k); assert bool; // already checked

  M := HMF0(F, N, 1*Integers(F), Chi, k, C);

  if QuaternionOrder cmpne 0 then 
    ok, message := IsSuitableQuaternionOrder(QuaternionOrder, M);
    error if not ok, message;
    set_quaternion_order(M, QuaternionOrder); // cache on QuaternionOrder
  end if;

  // cache on F
  if assigned F`ModFrmHils then
    if IsDefined(F`ModFrmHils, N) then
      Append(~F`ModFrmHils[N], M);
assert M in F`ModFrmHils[N];
    else
      F`ModFrmHils[N] := [* M *];
    end if;
  end if;

  return M;
end function;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt] : 
       QuaternionOrder:=0) -> ModFrmHil 
{The space of Hilbert modular forms over the totally real number field F, 
 with level N and weight k (or parallel weight 2, if k is not specified).  
 Here N should be an ideal in the maximal order of F, and k should be a 
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order 
 will be used for all computations of the space.}

  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  require #k eq Degree(F) : 
         "The weight k should be a sequence of d integers, where d is the degree of the field";
  require IsArithmeticWeight(F, k) :
         "The weight should be a sequence of integers that are all at least 2, and all of the same parity";
  
  return HMF(F, N, k : QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, k::RngIntElt : 
       QuaternionOrder:=0) -> ModFrmHil 
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  
  k := [k : i in [1..Degree(F)]];
  return HMF(F, N, k : QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl : QuaternionOrder:=0) 
       -> ModFrmHil 
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  
  k := [2 : i in [1..Degree(F)]];
  return HMF(F, N, k : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, k::RngIntElt : QuaternionOrder:=0)
       -> ModFrmHil
{The space of modular forms over the rationals with level N and weight k
 (or weight 2, if k is not specified).
 If the optional argument QuaternionOrder is specified, this quaternion order 
 will be used for all computations of the space.}
 
  require k eq 2 : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, [k] : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, k::RngIntElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq 2 : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), [k] : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, k : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), k : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N, [2] : QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N*Integers(), [2] : QuaternionOrder:=QuaternionOrder );
end intrinsic;

// TODO abhijitm - these will all be collapsed next commit

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] :
			   QuaternionOrder:=0) -> ModFrmHil
{The space of Hilbert modular forms over the totally real number field F,
    with level N , character chi and weight k (or parallel weight 2, if k is not specified).
 Here N should be an ideal in the maximal order of F, chi should be a Hecke character and k should be a
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order
 will be used for all computations of the space.}

  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require #k eq Degree(F) :
         "The weight k should be a sequence of d integers, where d is the degree of the field";
  // TODO : Do we still want to leave this?
  require IsArithmeticWeight(F, k) :
         "The weight should be a sequence of integers that are all at least 2, and all of the same parity";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";

  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";

  k := [k : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt
			   : QuaternionOrder:=0)
       -> ModFrmHil
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, 2) :
         "The weight should be compatible with the character.";

  k := [2 : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0)
       -> ModFrmHil
{The space of modular forms over the rationals with level N, character chi and weight k
 (or weight 2, if k is not specified).
 If the optional argument QuaternionOrder is specified, this quaternion order
 will be used for all computations of the space.}

  require k eq 2 :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, [k] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
		           k::RngIntElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq 2 :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), [k] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
		           k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N, [2] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N*Integers(), [2] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

function NewSubspaceBianchi(M, I)

    // Currently, always construct subspace and assign basis_matrix_wrt_ambient
    // (even in trivial cases)

    assert I eq Level(M);

    newspace := NewAndOldSubspaces(M);
    dim := Dimension(newspace);

    // initialize new space
    MI := BMF_with_ambient(M);
    MI`Dimension := dim;
    MI`NewLevel := I;
    
    Id := IdentityMatrix(Rationals(), dim);
    MI`basis_matrix_wrt_ambient := BasisMatrix(newspace);
    MI`basis_matrix_wrt_ambient_inv := 
                  Transpose(Solution( Transpose(MI`basis_matrix_wrt_ambient), Id));
    if assigned M`basis_matrix then
       MI`basis_matrix := MI`basis_matrix_wrt_ambient * M`basis_matrix;
       MI`basis_matrix_inv := Transpose(Solution( Transpose(MI`basis_matrix), Id));
    end if;

    return MI;
end function;

intrinsic NewSubspace(M::ModFrmHil, I::Any : QuaternionOrder:=0) 
       -> ModFrmHil
{For a space M of Hilbert modular forms of level N, and an ideal I dividing N 
 with I and N/I coprime, this constructs the subspace of M consisting of forms 
 that are new at level I or a multiple of I.
 More precisely, the NewSubspace is the complement of the space generated by all 
 images under degeneracy maps of spaces of level N/P for primes P dividing I.
 If the optional argument QuaternionOrder is specified, this quaternion order 
 will be used for all computations of the space.}

  require ISA(Type(I), RngOrdIdl) or ISA(Type(I), RngInt) : 
         "The second argument should be an ideal in the ring of integers of the base field";
  F := BaseField(M);  
  FeqQ := F cmpeq Rationals();

  if IsNew(M) or (FeqQ and Norm(NewLevel(M)) mod Norm(I) eq 0) 
              or (not FeqQ and IsIntegral(NewLevel(M)/I)) 
              or (assigned M`Dimension and M`Dimension eq 0) then 
    if QuaternionOrder cmpeq 0 and not IsBianchi(M) then
      return M; 
    end if;
  end if;
 
  N := Level(M);
  require N subset I : "The ideal should divide the level of the space";

  // arrange that (I,N/I) = (1)
  if I ne N then
    if FeqQ then
      I := &* [p^Valuation(Generator(N),p) where p is fact[1] : fact in Factorization(Generator(I))];
      I := I*Integers();
    else
      if #Factorization(I) gt 0 then
        I := &* [P^Valuation(N,P) where P is fact[1] : fact in Factorization(I)]; 
      end if;
    end if; 
  end if;

  // If QuaternionOrder is specified, it gets assigned either to MI or to MI`Ambient

  // Get the full space M1 (of same level but with NewLevel = 1)
  if Norm(NewLevel(M)) eq 1 then
    M1 := M;
  else
    assert assigned M`FullSpace;
    M1 := M`FullSpace;
  end if;
 
  // Check cache (we cache the NewSubspace on M1)
  // TO DO(?) case where QuaternionOrder is assigned to cached MI`Ambient but not MI
  if not assigned M1`NewSubspaces then 
    M1`NewSubspaces := [* *]; 
  elif exists(MI){tup[2] : tup in M1`NewSubspaces | tup[1] eq I} 
       and (QuaternionOrder cmpeq 0 or assigned MI`QuaternionOrder 
                                       and IsIdentical(QuaternionOrder, MI`QuaternionOrder)) 
  then
    return MI;
  end if;

  if IsBianchi(M) then  
    require I eq Level(M) : "The second argument must be the level of the space (currently)";
    MI := NewSubspaceBianchi(M, I);

  else
    MI := HMF0(BaseField(M), Level(M), I, DirichletCharacter(M), Weight(M), CentralCharacter(M));
    if QuaternionOrder cmpne 0 then 
      if I eq _Discriminant(QuaternionOrder) then
        ok, message := IsSuitableQuaternionOrder(QuaternionOrder, MI);
        error if not ok, "Invalid QuaternionOrder specified for NewSubspace:" * message;
        set_quaternion_order(MI, QuaternionOrder);
      else
        // Must check this here, otherwise infinite loop can occur for bad input
        I0 := _Discriminant(QuaternionOrder);
        require IsIntegral(N/I0) and Norm(I0 + N/I0) eq 1 :
               "Invalid QuaternionOrder specified for NewSubspace " *
               "(primes dividing the discriminant must divide the level of the space exactly once)";
        MI`Ambient := NewSubspace(M1, _Discriminant(QuaternionOrder) : QuaternionOrder:=QuaternionOrder);
      end if;
    end if;
  end if;

  if I eq N then 
    MI`is_new := true; 
  end if;
  MI`FullSpace := M1;
  Append(~M1`NewSubspaces, <I,MI>);

  return MI;
end intrinsic;

intrinsic NewSubspace(M::ModFrmHil : QuaternionOrder:=0) -> ModFrmHil
{For a space M of Hilbert modular forms of level N, this constructs the 
 subspace consisting of forms that are new at level N.  
 This is the same as NewSubspace(M, N).}
// This is defined as the complement of the space generated by all images 
// under degeneracy maps of spaces of level N/P for primes P dividing N.

  return NewSubspace(M, Level(M) : QuaternionOrder:=QuaternionOrder);
end intrinsic;


/************   Access to basic attributes for ModFrmHil   ************/

intrinsic BaseField(M::ModFrmHil) -> FldAlg
{The base field of the space M of Hilbert modular forms}
  return M`Field;
end intrinsic;

intrinsic BaseRing(M::ModFrmHil) -> FldAlg
{The base field of the space M of Hilbert modular forms}
  return M`Field;
end intrinsic;

intrinsic Level(M::ModFrmHil) -> RngOrdIdl
{The level of the space M of Hilbert modular forms}
  return M`Level;
end intrinsic;

intrinsic NewLevel(M::ModFrmHil) -> RngOrdIdl
{For a space M of Hilbert modular forms, this is the level at which M is new. See NewSubspace(M,I)}
  return M`NewLevel;
end intrinsic;

// This is either 1 or a GrpDrchNFElt
intrinsic DirichletCharacter(M::ModFrmHil) -> Any
{The nebentypus of the space M of Hilbert modular forms}
  return M`DirichletCharacter; 
end intrinsic;

intrinsic Weight(M::ModFrmHil) -> SeqEnum[RngIntElt]
{The weight of the space M of Hilbert modular forms}
  if Type(M) eq ModFrmBianchi then
    return M`Weight[1];
  end if;
  return M`Weight;
end intrinsic;

intrinsic CentralCharacter(M::ModFrmHil) -> RngIntElt
{An integer C such that the central character is t :-> Norm(t)^C}
  return M`CentralCharacter;
end intrinsic;

intrinsic IsParallelWeight(M::ModFrmHil) -> BoolElt, RngIntElt
{True iff the space M of Hilbert modular forms has weight [k,k,...,k]
(in which case k is also returned)}
  w := M`Weight;
  if #Seqset(w) eq 1 then
    return true, w[1];
  else
    return false, _;
  end if;
end intrinsic;

intrinsic IsCuspidal(M::ModFrmHil) -> BoolElt
{True iff M was created as (a subspace of) a space of Hilbert cusp forms}
  return M`is_cuspidal;
end intrinsic;

intrinsic IsNew(M::ModFrmHil) -> BoolElt
{True iff M was created as (a subspace of) a space of Hilbert new forms}
  if not assigned M`is_new then
    if NewLevel(M) eq Level(M) then
      M`is_new := true;
    end if;
  end if;
  return assigned M`is_new and M`is_new; // but don't set is_new to false
end intrinsic;

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

intrinsic Dimension(M::ModFrmHil : UseFormula:=true) -> RngIntElt
{The dimension of the space M of Hilbert modular forms}

  if assigned M`Dimension then 
    return M`Dimension;
  end if;

  if IsBianchi(M) then
    return DimensionBianchi(M);
  end if;

  OA := QuaternionOrder(M);
  definite := IsDefinite(M);

  if not UseFormula
      or Seqset(Weight(M)) ne {2}
  then
      if definite then
        _ := BasisMatrixDefinite(M : EisensteinAllowed);
      else
        M`Dimension := Rank(basis_matrix(M));
      end if;

  elif definite then
      discA := Discriminant(OA);
      eis := NarrowClassNumber(MaximalOrder(BaseRing(OA)));

      vprintf ModFrmHil: "Computing dimension via class numbers ... ";
      vprintf Shimura: "\n";
      vtime ModFrmHil:

      if NewLevel(M) eq discA then
        full := DefiniteClassNumber(discA, Level(M)/discA);
        M`Dimension := full - eis;

      else
        // Inclusion-exclusion to get dimension of new space from dimensions of full spaces.
        // Let f(n) = dimension of full space of level n,
        // and g(n) = dimension of new subspace of level n.
        // Then we have f(n) = Sum_{m|n} d(m)*g(n/m), because the images of a new space under
        // degeneracy maps don't intersect, and the number of maps is d(m) = # of divisors of m,
        // Inverting this, g(n) = Sum_{m|n} c(m)*f(n/m) where c is the multiplicative function
        // defined on prime powers by c(p) = -2, c(p^2) = 1, c(p^k) = 0 for k > 3.
        // One proves this using zeta generating functions: writing K for BaseField(M),
        // Zeta_d(s) := Sum_{ideals n} d(n)/n^s = Zeta_K(s)^2, hence Zeta_c(s) = Zeta_K(s)^-2

        dim := 0;
        eichler_level := Level(M)/discA;
        newLevel := NewLevel(M)/discA;
        dim := 0;
        for J in Divisors(newLevel) do
          Jfact := Factorization(J);
          if forall{tup : tup in Jfact | tup[2] le 2} then
            cJ := (-2) ^ #{tup : tup in Jfact | tup[2] eq 1};
            dimJ := DefiniteClassNumber(discA, eichler_level/J);
            dim +:= cJ * (dimJ - eis);
          end if;
        end for;
        M`Dimension := dim;
      end if;

  else // indefinite
      if BaseRing(OA) cmpeq Integers() then
        discA:= Integers()! Discriminant(OA);
        eichler_level := Integers()!(Generator(Level(M))/discA);  
        newLevel := Integers()!(Generator(NewLevel(M))/discA);
      else 
        discA := Discriminant(OA);
        eichler_level := Level(M)/discA;
        newLevel := NewLevel(M)/discA;
      end if;
      if assigned OA`FuchsianGroup and assigned OA`FuchsianGroup`ShimGroup 
                                   and eichler_level eq discA and newLevel eq discA then
        shim_group := OA`FuchsianGroup`ShimGroup;
        dim := ((#Generators(shim_group) - #Relations(shim_group) + 1) div 2)
               * NarrowClassNumber(BaseField(M));
      else
        // Inclusion-exclusion (see comment in definite case)
        dim := 0;
        use_genus := (NarrowClassNumber(BaseField(M)) eq 1) and (SequenceToSet(Weight(M)) eq {2});
        if use_genus then
          vprintf ModFrmHil: "Computing dimension via genus formula ... \n";
        else
          vprintf ModFrmHil: "Computing dimension via basis matrix ... \n";
        end if;
        vtime ModFrmHil:
        for J in Divisors(newLevel) do
          Jfact := Factorization(J);
          if forall{tup : tup in Jfact | tup[2] le 2} then
            cJ := (-2) ^ #{tup : tup in Jfact | tup[2] eq 1};
            NdivJ := Parent(J)! (eichler_level/J);
            if use_genus then
              // TODO abhijitm I'm a bit confused since use_genus is only true when
              // the narrow class number is 1
              dimJ := Genus(FuchsianGroup(BaseField(M), discA, NdivJ : ComputeAlgebra:=false))
                        * NarrowClassNumber(BaseField(M));
            else
              // Just compute the space--otherwise, we waste time computing the structure of the
              // intermediate groups; Shapiro's lemma is superior.
              Gamma := FuchsianGroup(OA);
              dimJ := Nrows(HeckeMatrix2(Gamma, NdivJ, "Infinity", Weight(M), Character(M))) div 2;
            end if;
            dim +:= cJ * dimJ;
          end if;
        end for;
      end if;
      M`Dimension := Integers()!dim;
  end if;
  return M`Dimension;
end intrinsic;

// helper for QuaternionOrder(M)

function quaternion_algebra(F, definite, disc)
  if definite and Norm(disc) eq 1 then
    if &and [IsEven(Degree(pl[1])) or IsEven(RamificationDegree(pl[1])) : pl in Decomposition(F,2)] then
      // can just use Hamiltonians, since the primes above 2 have even local degree 
      A := QuaternionAlgebra< F | -1,-1 >;       
    else  
      // take a nice algebra defined over the rationals if one exists
      if exists(p){p: p in [2..100] | IsPrime(p) and GCD(p,Discriminant(Integers(F))) eq 1
                                      and &and [IsEven(Degree(pl[1])) : pl in Decomposition(F,p)]} 
      then 
        a,b := StandardForm(QuaternionAlgebra(p));
        a := SquareFree(Numerator(a)*Denominator(a));
        b := SquareFree(Numerator(b)*Denominator(b));
        A := QuaternionAlgebra< F | a,b >;
      else
        A := QuaternionAlgebra(InfinitePlaces(F));
      end if;
    end if;
    assert IsEmpty(pl) and ploo eq InfinitePlaces(F) where pl,ploo is FactoredDiscriminant(A);
  elif definite then
    A := QuaternionAlgebra(disc, InfinitePlaces(F) : Optimized);
  else
    A := QuaternionAlgebra(disc, InfinitePlaces(F)[2..Degree(F)] : Optimized);
  end if;  
  return A;
end function;

// Choose isomorphism class of quaternion algebra to be used.
// Returns
//   true, is_definite, disc 
// or 
//   false, message

function qa_discriminant(F, N, Nnew, k, chi)
  n := Degree(F);
  if IsEven(n) then  
    return true, true, 1*Integers(F);
  else
    facts := Factorization(Nnew);
    // check facts are sorted
    norms := [Norm(t[1]) : t in facts]; 
    assert norms eq Sort(norms);
    if exists(P){t[1] : t in facts | t[2] eq 1} and (chi cmpeq 1 or IsTrivial(chi)) then
      return true, true, P;
    elif n gt 1 then
      return true, false, 1*Integers(F);
    end if;
  end if;
  // impossible
  message := "This space cannot be computed using either of the available algorithms.";
  if exists{t : t in Factorization(N) | t[2] eq 1 and Valuation(Nnew,t[1]) eq 0} then
     message *:= " (Its NewSubspace might be possible though.)";
  end if;
  return false, message, _;
end function;

intrinsic QuaternionOrder(M::ModFrmHil) -> AlgAssVOrd
{The quaternion order used to compute this space of Hilbert modular forms
 (via the Jacquet-Langlands correspondence)}

  if assigned M`QuaternionOrder then 
    return M`QuaternionOrder;
  elif assigned M`Ambient then
    return QuaternionOrder(M`Ambient);
  end if;

  require not IsBianchi(M) : "Not relevant for Bianchi modular forms";

  F := BaseField(M);
  ZF := Integers(F);
  require F cmpne Rationals() :
         "The Hilbert modular forms package is not fully implemented over Rationals(). "*
         "It's better to use RationalsAsNumberField() instead!";

  N := Level(M);
  Nnew := NewLevel(M);
  assert IsIntegral(N/Nnew) and Norm(Nnew + N/Nnew) eq 1;

  bool, definite, disc := qa_discriminant(F, N, Nnew, Weight(M), DirichletCharacter(M));
  if not bool then
    require false : definite; // 'definite' is an error message
  end if;

  // Secret option (NOT FOR EXPORT)
  if definite and assigned M`force_indefinite and M`force_indefinite then
    definite := false;
    if IsOdd(Degree(F)) then
      disc := 1*ZF;
    else
      assert exists(disc){t[1] : t in Factorization(Nnew) | t[2] eq 1};
    end if;
  end if;
 
  // When NewLevel ne disc, M is computed as a subspace of M`Ambient, 
  // which is the space with same Level, and with NewLevel = disc.
  // We now find/create it, and get/set its QuaternionOrder.

  QO := 0; // QuaternionOrder not yet known

  if disc ne Nnew then
    assert Norm(disc + Nnew/disc) eq 1; 
    assert assigned M`FullSpace; // since its NewLevel is not 1
    // Check if this space is already known
    if disc eq 1*ZF then
      Mambient := M`FullSpace;
      ambient_exists := true;
    else
      ambient_exists := exists(Mambient){tup[2] : tup in M`FullSpace`NewSubspaces | tup[1] eq disc}; 
    end if;
    if ambient_exists then
      Mambient := TopAmbient(Mambient);
      if assigned Mambient`QuaternionOrder then
        QO := Mambient`QuaternionOrder;
      end if;
    else
      // Create a new space to be M`Ambient 
      Mambient := NewSubspace(M`FullSpace, disc);
    end if;
  end if;

  // Use same QuaternionOrder as some cached space, if possible
  if assigned F`ModFrmHils and QO cmpeq 0 then
    function hasQO(XX)
      if assigned XX`QuaternionOrder then 
        XXQO := XX`QuaternionOrder;
        if definite eq IsDefinite(Algebra(XXQO)) and disc eq _Discriminant(XXQO) then
          return true, XXQO;
        end if;
      end if;
      return false, 0;
    end function;
    // check the fullspaces on F
    for N in Keys(F`ModFrmHils), MM in F`ModFrmHils[N] do 
      bool, QO := hasQO(MM);
      if bool then break N; end if;
    end for;
  end if;
  if assigned F`ModFrmHils and QO cmpeq 0 and Norm(disc) ne 1 then 
    // check the new subspaces too
    for N in Keys(F`ModFrmHils), MM in F`ModFrmHils[N] do 
      if assigned MM`NewSubspaces then
        for tup in MM`NewSubspaces do 
          bool, QO := hasQO(tup[2]);
          if bool then break N; end if;
        end for;
      end if;
    end for;
  end if;

  if QO cmpeq 0 then
    // Create new QuaternionOrder
    QO := MaximalOrder(quaternion_algebra(F, definite, disc));
  end if;

  A := Algebra(QO);
  assert IsCoercible(F,A.1^2) and IsCoercible(F,A.2^2); // standard form

  vprintf ModFrmHil: 
    "%o\nwill be computed using the %o quaternion algebra with discriminant of norm %o defined by"
    *"\n    i^2 = %o\n    j^2 = %o\n", 
    M, IsDefinite(A) select "definite" else "indefinite", Norm(Discriminant(A)), A.1^2, A.2^2;

  //"QuaternionOrder:"; TES(QO);
  //"Quaternion algebra:"; TES(Algebra(QO));

  if disc ne Nnew then
    if not assigned Mambient`QuaternionOrder then
      SetQuaternionOrder(Mambient, QO);
    end if;
    M`Ambient := Mambient;
  else
    SetQuaternionOrder(M, QO);
  end if; 

  return QO;

end intrinsic;

intrinsic IsDefinite(M::ModFrmHil) -> BoolElt
{True iff M is a space of Hilbert modular forms
computed using a definite quaternion algebra}

  if IsBianchi(M) then
    return false;
  end if;

  // Choose the QuaternionOrder now
  return IsDefinite(Algebra(QuaternionOrder(M)));
end intrinsic;

intrinsic InnerProductMatrix(M::ModFrmHil) -> Mtrx
{The natural Hecke-invariant inner product on the Hilbert modular forms space M}

  if not assigned M`InnerProduct then
    require IsDefinite(M) and basis_is_honest(M): 
                              "Not implemented for this space";
    bool, w := IsParallelWeight(M);
    require bool and w eq 2 : "Not implemented for this space"; // TO DO

    IPbig := InnerProductMatrixBig(TopAmbient(M));
    BM := basis_matrix(M);
    IP := BM * ChangeRing(IPbig, BaseRing(BM)) * Transpose(BM);
    IP := ChangeRing(IP, hecke_matrix_field(M));
    M`InnerProduct := IP;
  end if;

  return M`InnerProduct;
end intrinsic;

intrinsic InnerProduct(f::ModFrmHilElt, g::ModFrmHilElt) -> RngElt
{The inner product (f, g) between Hilbert modular forms}

  // Currently, f and g can only be created with Eigenform of a newform component
  // TO DO: handle better, in any case

  Nf := Parent(f);
  Mf := Nf`NewSpace;
  Ng := Parent(g);
  Mg := Ng`NewSpace;

  require Mf eq Mg : "The arguments should be newforms from the same space";

  if Nf ne Ng then
    // different components are orthogonal, since IP is Hecke-invariant
    return 0;
  end if;
 
  if assigned f`coords_raw and assigned g`coords_raw then
    M := TopAmbient(Nf);
    assert M eq TopAmbient(Ng);
    fc := f`coords_raw;
    gc := g`coords_raw;
    IP := InnerProductMatrixBig(M);
  elif assigned f`coords_wrt_ambient and assigned g`coords_wrt_ambient then
    fc := f`coords_wrt_ambient;
    gc := g`coords_wrt_ambient;
    IP := InnerProductMatrix(Nf`Ambient);
  elif assigned f`coords_wrt_parent and assigned g`coords_wrt_parent then
    require false : "This case is unexpected -- please report to magma-bugs@maths.usyd.edu.au";
    fc := f`coords_wrt_parent;
    gc := g`coords_wrt_parent;
    IP := InnerProductMatrix(Nf);
  else
    require false : "Not implemented in this situation";
  end if;

  fF := f`BaseField;
  gF := g`BaseField;
  if CanChangeRing(fc, gF) then
    F := gF;
  elif CanChangeRing(gc, fF) then
    F := fF;
  else
    require false : "The given forms are over incompatible base fields";
  end if;

  ip := ChangeRing(fc,F) * ChangeRing(IP,F) * ChangeRing(Transpose(Matrix(gc)),F);
  return ip[1];
end intrinsic;


/***************     Other basic stuff for ModFrmHil     *************/

intrinsic 'eq'(M1::ModFrmHil, M2::ModFrmHil) -> BoolElt
{True iff the two spaces of Hilbert modular forms are identically the same}
  return IsIdentical(M1, M2);
end intrinsic;


/**********************************************************************
  ModFrmHilElt attributes ...
  Let f be a ModFrmHilElt, contained in the ModFrmHil space M

  NOTE: Unlike ModFrmElt's, here we allow elements of M to be 
        defined over extensions of BaseField(M)
***********************************************************************/

declare type ModFrmHilElt;

declare attributes ModFrmHilElt :
  
  Parent,                       // = M

  BaseField,                    // the field over which the element is defined,

  coords_wrt_parent,            // Vector representing element wrt the rational basis of M
  coords_wrt_ambient,           //  ..... of M`ambient
  coords_wrt_top,               //  ..... of top space in chain M`ambient`ambient
                                //        [mercifully, not using the top one yet]
  coords_raw,                   // = coords_wrt_parent * M`basis_matrix

  red_coords_wrt_ambient,       // list containing reductions mod P of coords

  hecke_eigenvalues,            // array indexed by primes
  al_eigenvalues,               // TO DO

  best_column,                  // [temp?] used in HeckeEigenvalue

  EK, tEK, eEK;                 // [temp?] used in Eigenform (METHOD 3 and 4)

/****************   Hacking for ModFrmHilElt   *****************/

intrinsic Parent(x::ModFrmHilElt) -> ModFrmHil
{}
  return x`Parent;
end intrinsic;

// TO DO: Provide Print too ???

intrinsic Print(x::ModFrmHilElt, level::MonStgElt)
{}
  if level eq "Maximal" then 
    printf "Element of %o\n", Parent(x); 
    printf "defined over %o", BaseField(x); 
  else
    printf "Element of "; 
    Print(Parent(x), "Minimal");
  end if; 
end intrinsic;

intrinsic IsCoercible(x::ModFrmHilElt, y::.) -> BoolElt, .
{}
  return false;
end intrinsic;

intrinsic 'in'(x::., y::ModFrmHilElt) -> BoolElt
{}
  return false;
end intrinsic;


/**************   Basis attributes of ModFrmHilElt  *****************/

intrinsic BaseField(f::ModFrmHilElt) -> Fld
{The field over which the Hilbert modular form f is defined}
  return f`BaseField;
end intrinsic;

