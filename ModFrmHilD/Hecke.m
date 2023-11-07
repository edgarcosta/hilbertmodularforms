///////////////////////////////////////////////////
//                                               //
//                Hecke Operators                //
//                                               //
///////////////////////////////////////////////////

///////////// ModFrmHilDElt: Hecke Operators ////////////////
intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl : MaximalPrecision := false) -> ModFrmHilDElt
  {Returns T(nn)(f) for the character chi modulo the level of f}

  Mk := Parent(f);
  M := Parent(Mk);
  F := BaseField(M);
  Cl, mp := NarrowClassGroup(F);
  ZF := Integers(F);
  k0 := Max(Weight(f));
  chi := Character(Mk);

  coeffsTnnf := AssociativeArray();
  prec := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffsTnnf[bb] := AssociativeArray();
    prec[bb] := 0;
  end for;

  for bb in NarrowClassGroupReps(M) do
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    bbpinv := bbp^(-1);

    for nu in ShintaniRepsUpToTrace(M, bb, Precision(M)) do //they come sorted
      I := nu*bbpinv;  // already call nn the ideal for the Hecke operator
      c := 0;
      t := Integers()!Trace(nu);


      // loop over divisors
      // Formula 2.23 in Shimura - The Special Values
      // of the zeta functions associated with Hilbert Modular Forms
      // If a coefficient in the sum is not defined we will set prec[bb] := Trace(nu) - 1;
      for aa in Divisors(ZF!!(I + nn)) do
        if I eq 0*ZF then
          //takes care if the coefficients for the zero ideal are different
          c +:= chi(aa) * Norm(aa)^(k0 - 1) * Coefficients(f)[NarrowClassRepresentative(M, bb*nn/aa^2)][ZF!0];
        else
          b, cf := IsCoefficientDefined(f, ZF!!(aa^(-2) * (I*nn)));
          if not b then
            // stop looping through divisors if coefficient for at least one divisor
            // is not defined (if trace (aa^(-2) * (I*nn)) is greater than precision)
            prec[bb] := t-1;
            break; // breaks loop on aa
          else
            c +:= chi(aa) * Norm(aa)^(k0 - 1) * cf;
          end if;
        end if;
      end for;
      if prec[bb] ne 0 then // the loop on aa didn't finish
        break; // breaks loop on nu
      else
        coeffsTnnf[bb][nu] := c;
      end if;
    end for;
  end for;

  // Attempting to increase precision using a basis
  // This is not very efficient, as it does not remember the underlying vector space, but it works.
  if (assigned Mk`Basis) or MaximalPrecision then
      B := Basis(Mk);
      // These have different numbers of columns
      mats := [* *];
      vec := [];
      for bb in Keys(coeffsTnnf) do
	  nus := Keys(coeffsTnnf[bb]);
	  mat := Matrix([[Coefficients(f)[bb][nu] : nu in nus] : f in B]);
	  Append(~mats, mat);
	  vec cat:= [coeffsTnnf[bb][nu] : nu in nus];
      end for;
      // This does not work with a list
      // mat := HorizontalJoin(mats);
      mat := mats[1];
      for comp_idx in [2..#mats] do
	  mat := HorizontalJoin(mat, mats[comp_idx]);
      end for;
      // If the matrix is invertible, there will be a unique solutions, and we can use it.
      if Rank(mat) eq #B then
	  vec_sol := Solution(mat, Vector(vec));
	  g := &+[vec_sol[i]*B[i] : i in [1..#B]];
	  return g;
      end if;
  end if;
  
  g := HMF(Mk, coeffsTnnf : CoeffsByIdeals:=false, prec:=prec);
  return g;
end intrinsic;

// I add this function, even though it is worse than HeckeOp in Trace.m because it is a straight-forward approach that can be used to check ourselves. I started by doing this manually, but it is useful to have.

intrinsic HeckeOperator(Mk::ModFrmHilD, nn::RngOrdIdl) -> ModMatFldElt
{Returns the Hecke operator T(nn) on Mk with respecto to the basis Basis(Mk).
 This implementation uses action of Hecke operators on q-expansions.}

   basis := Basis(Mk);
   hecke_basis := [HeckeOperator(f, nn) : f in basis];
   mat, indices := CoefficientsMatrix(basis);
   Tmat, Tindices := CoefficientsMatrix(hecke_basis);
   // Need to account for precision loss in different components
   num_inds := [#x : x in indices];
   num_inds_T := [#x : x in Tindices];
   assert not IsEmpty(num_inds_T); // should have at least one component
   mat_join := Submatrix(mat,1,1,Nrows(mat), num_inds_T[1]);
   start_col := 1;
   for comp_idx in [2..#num_inds] do
       start_col +:= num_inds[comp_idx-1];
       ncols := num_inds_T[comp_idx];
       submat := Submatrix(mat,1,start_col,Nrows(mat),ncols);
       mat_join := HorizontalJoin(mat_join, submat);
   end for;
   require Rank(mat_join) eq Nrows(mat) : "Not enough precision!";
   T := Solution(mat_join, Tmat);
   return T;
end intrinsic;
