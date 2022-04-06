freeze;
 
declare attributes AlgAssV: IdPots;

idpots:= function( A )

   F:= CoefficientRing( A );
   B:= Centre( A );
   J:= JacobsonRadical( B );
   Q,hm:= quo< B | J >;

   // Let Q be the semisimple commutative associative algebra
   // Z(A)/Rad(Z(A)).
   // We calculate a complete set of orthogonal idempotents in Q
   // and then lift them to A.
   // The orthogonal idempotents in Q correspond to the decomposition
   // of Q as a direct sum of simple ideals. Now ids will contain
   // a list of ideals of Q such that the direct sum of these equals
   // Q. The variable idpots will contain the idempotents
   // corresponding to the ideals in ids.
   // The algorithms has two parts: one for small fields (of size less than
   // 2*Dimension( Q ), and one for big fields.
   // If the field is big, then using a Las Vegas algorithm we find a
   // splitting element (this is an element that generates Q). By
   // factoring the minimal polynomial of such element we can find a
   // complete set of orthogonal idempotents in one step.
   // However, if the field is small splitting elements might not exist.
   // In this case we use decomposable elements (of which the minimum
   // polynomial factors into two (or more) relatively prime factors.
   // Then using the same procedure as for splitting elements we can
   // find some idempotents. But in this case the corresponding ideals
   // might split further. So we have to find decomposable elements in
   // these and so on.
   // Decomposable elements are found as follows: first we calculate
   // the subalgebra of all elements x such that x^q=x
   // (where q=Size( F )).
   // This subalgebra is a number of copies of the ground field. So any
   // element independent from 1 of this subalgebra will have a minimum
   // polynomial that splits completely. On the other hand, if 1 is the
   // only basis vector of this subalgebra than the original algebra was
   // simple.
   // For a more elaborate description we refer to "W. Eberly and M.
   // Giesbrecht, Efficient Decomposition of Associative Algebras,
   // Proceedings of ISSAC 1996."

   idpots:= [ One( Q ) ];
   ids:= [ Q ];

   // The variable k will point to the first element of ids that
   // still has to be decomposed.

   k:=1;

   if not IsFinite(F) or #F gt 2*Dimension( Q )^2 then
     set:= [ One(F)*i : i in [ 0 .. 2*Dimension(Q)^2 ] ];
   else
     set:= [ ];
   end if;

    repeat

        if #set gt 1 then

          // We are in the case of a big field.

          repeat

            // We try to find an element of Q that generates it.
            // If we take the coefficients of such an element randomly
            // from a set of 2*Dimension(Q)^2 elements,
            // then this element generates Q with probability > 1/2

            e:= &+[ Random( set )*Q.i : i in [1..Dimension(Q)] ];
            f:= MinimalPolynomial( e );

          until Degree( f ) eq Dimension( Q );

        else

          // Here the field is small.

          q:= #F;

        // sol will be a basis of the subalgebra of the k-th ideal
        // consisting of all elements x such that x^q=x.
        // If the dimension of sol is 1
        // then the ideal is simple and we proceed to the next one. If all
        // ideals are simple then we quit the loop.

          sol:= [ ];
          while #sol lt 2 and k le #ids  do
            bQ:= Basis( ids[k] );
            eqs:= [ ];
            for i in [1..Dimension( ids[k] )] do
              eqs cat:= Coordinates( ids[k], bQ[i]^q-bQ[i] );
            end for;
            V:= VectorSpace( F, Dimension(ids[k]) );
            eqs:= Hom(V,V)!eqs;
            sol:= NullSpace( eqs );
            sol:= [ ids[k]!Eltseq(sol.i) : i in [1..Dimension(sol)] ];
            if #sol eq 1 then k:=k+1; end if;
          end while;

          if k gt #ids then break; end if;

          V:= VectorSpace( F, Dimension( ids[k] ) );
          W:= sub< V | V!Eltseq( One( ids[k] ) ) >;
          e:= sol[1];
          if V!Eltseq(e) in W then e:=sol[2]; end if;

        // We calculate the minimum polynomial of e.

          f:= MinimalPolynomial(e);

        end if;

        facs:= Factorization( f );

      // Now we find elements h1,...,hs such that hi = 1 mod facs[i] and
      // hi = 0 mod facs[j] if i ne j.
      // This is possible due to the Chinese remainder theorem.

        hlist:= [ ];
        for i in [1..#facs] do
          cf:= [ Zero( F ) : i in [1..#facs] ];
          cf[i]:= One(F);
          j:= 1;
          c:= cf[1];
          p:= facs[1][1];
          while j lt #facs do
            j:= j + 1;
            gcd,g1,g2:= XGCD( p, facs[j][1] );
            c:= p*( ( g1*(cf[j]-c) div gcd ) mod facs[j][1] )+ c;
            p:= p*facs[j][1] div gcd;
          end while;

          Append( ~hlist, c mod p );

        end for;

      // Now a set of orthogonal idempotents is given by hi(e).

        _,phi:= RegularRepresentation( ids[k] );
        id:= [ Evaluate( hlist[i], phi(e) )@@phi : i in [1..#hlist] ];

        if #set eq 0 then

        // We are in the case of a small field;
        // so we append the new idempotents and ideals
        // (and erase the old ones). (If E is an idempotent,
        // then the corresponding ideal is given by E*Q*E.)

          idpots1:= Remove( idpots, k );
          ids1:= Remove( ids, k );

          bQ:= Basis( ids[k] );
          for i in [1..#id] do
            bb:= [ id[i]*bQ[j]*id[i] : j in [1..#bQ] ];
            IQ:= ideal< ids[k] | bb >;
            Append( ~ids1, IQ );
            Append( ~idpots1, Q!id[i] );
          end for;

          ids:= ids1;
          idpots:= idpots1;

        else

        // Here the field is big so we found the complete list of idempotents
        // in one step.

          idpots:= id;
          k:= #ids+1;

        end if;

        while k le #ids and Dimension( ids[k] ) eq 1 do
          k:=k+1;
        end while;

    until k gt #ids;

      id:= [ idpots[i]@@hm : i in [1..#idpots] ];

      // Now we lift the idempotents to the algebra B.
      // The first idempotent is lifted as follows:
      // We have that id[1]^2-id[1] is an element of Rad.
      // We construct the sequences e_{i+1} = e_i + n_i - 2e_in_i,
      // and n_{i+1}=e_{i+1}^2-e_{i+1}, starting with e_0=id[1].
      // It can be proved by induction that e_q is an idempotent in A
      // because n_0^{2^q}=0.
      // Now E will be the sum of all idempotents lifted so far.
      // Then the next lifted idempotent is obtained by setting
      // ei:=id[i]-E*id[i]-id[i]*E+E*id[i]*E;
      // and lifting as above. It can be proved that in this manner we
      // get an orthogonal system of primitive idempotents.

      E:= Zero( F )*id[1];
      for i in [1..#id] do
        ei:= id[i]-E*id[i]-id[i]*E+E*id[i]*E;
        q:= 0;
        while 2^q le Dimension( J ) do
          q:= q+1;
        end while;
        ni:= ei*ei-ei;
        for j in [1..q] do
          ei:= ei+ni-2*ei*ni;
          ni:= ei*ei-ei;
        end for;
        id[i]:= ei;
        E:= E+ei;
      end for;

      // Finally the idempotents are mapped to elements of A. We also
      //construct the corresponding ideals.

      id:= [ A!id[i] : i in [1..#id] ];

      bA:= Basis( A );
      ideals:=[ ideal< A | [ id[i]*bA[j] : j in [1..#bA] ] > :
         i in [1..#id] ];

      return id,ideals;

end function;

intrinsic CentralIdempotents(A::AlgAssV) -> [ ], [ ]
{Return a full set of central orthogonal idempotents of A, along with the 
ideals they generate}

      if assigned A`IdPots then
         return A`IdPots[1],A`IdPots[2];
      end if;
      id,ideals:= idpots( A );
      A`IdPots:= [* id, ideals *];
      return id,ideals;
end intrinsic;

intrinsic DirectSumDecomposition(A::AlgAssV) -> SeqEnum
{The decomposition of A as a direct sum of indecomposable ideals}
    id, ideals := CentralIdempotents(A);
    return ideals, id;
end intrinsic;
intrinsic IndecomposableSummands(A::AlgAssV) -> SeqEnum
{The decomposition of A as a direct sum of indecomposable ideals}
    id, ideals := CentralIdempotents(A);
    return ideals, id;
end intrinsic;



LeftMultiplier:= function( A, Zbas, Z )

     // Here Zbas is a Z-basis of the Q-algebra A.
     // Let M be the Z-module spanned by Z-bas. We compute
     // the order consisting of of all x\in A such that xM\subset M.
     // We require that A have a one, otherwise an error will occur.

     one:= One( A );

     V:= VectorSpace( BaseRing(A), Dimension(A) );
     M:= VectorSpaceWithBasis( [ V!Coordinates( A, x ) : x in Zbas ] );

     ccc:= [ [ ] : i in [1..#Zbas] ];
     for i in [1..#Zbas] do
         for j in [1..#Zbas] do
             ccc[i][j]:= Coordinates( M, 
                           V!( Coordinates( A, Zbas[i]*Zbas[j] ) ) );
         end for;
     end for;

     cf:= Coordinates( M, V!Coordinates( A, one ) );
     dens:= {};
     for x in cf do
         Include( ~dens, Denominator( x, Z ) );
     end for;
     s:= Lcm( dens );

     dim:= #Zbas;
     eqs:= [ ];
     for j in [1..dim] do
         for k in [1..dim] do
             eqn:= [ ];
             for i in [1..dim] do
                 eqn[i]:= ccc[i][j][k];
             end for;
             for i in [1..(dim)^2] do
                 eqn[dim+i]:= 0;
             end for;
             eqn[ dim+(j-1)*dim+k ]:= -s*1;
             Append( ~eqs, eqn );
         end for;
     end for;

     eqs:= Transpose( Matrix( Z, eqs ) );
     sol:= Basis( NullSpace( eqs ) );

     bb:= [ 1/s*x : x in Zbas ];
     res:= [ ];
     for x in sol do
         y:= 0*bb[1];
         for i in [1..dim] do
             y:= y + x[i]*bb[i];
         end for;
         Append( ~res, y );
     end for;

     return res;

end function;


MaxOrd_sim:= function( A, CR )

     // Here we assume that A is an associative algebra over
     // the rationals, and that A is simple (but not necessarily 
     // central simple).
     // So dim A = n^2*k, for some n, where k is the dimension of the
     // centre of A, and A is isomorphic to a full
     // matrix algebra over its centre.
     // We construct a maximal Z-order in A.

     dim:= Dimension( A );
     BR := BaseRing(A);

     // n will be an integer such that n^2 = dim( A )/k,
     // where k = dim( Centre( A ) );
         
     k:= Dimension( Centre( A ) ); 
     n:= 1;
     while n^2 lt dim/k do
           n:= n+1;
     end while;
 
     // for each basis element of A we find its reduced trace.
     traces:= [ ];
     bA:= Basis(A);
     for i in [1..dim] do
         tr:= 0;
         for j in [1..dim] do
             cf:= Coordinates( A, bA[i]*bA[j] );
	     //cf[j];
             tr:= tr + cf[j];
         end for;
         Append( ~traces, tr/n );
     end for;

     V:= VectorSpace( BR, dim );

     // first we find an integer d such that the structure constants
     // relative to the basis {da_i} of A are integers (here {a_i} is a
     // basis of A).

     dens:= {};
     for i in [1..dim] do
         for j in [1..dim] do
             cf:= Coordinates( A, bA[i]*bA[j] );
             for k in [1..dim] do
                 dn:= Denominator( BR!cf[k], CR);
                 if dn ne 1 then Include( ~dens, dn ); end if;
             end for;
         end for;
     end for;
     if #dens eq 0 then
        d:= 1;
     else
        d:= Lcm( dens );
     end if;

     ord:= [ d*x : x in bA ];
     maximal:= false;

     old_disc := CR!0;
     while not maximal do

           maximal:= true;

           // get the structure constants of the order 
       
           M:= VectorSpaceWithBasis( [ V!Coordinates( A, x ) : x in ord ] );

           ccc:= [ [ ] : i in [1..dim] ];
           for i in [1..dim] do
               for j in [1..dim] do
                   ccc[i][j]:= Coordinates( M, 
                                    V!( Coordinates( A, ord[i]*ord[j] ) ) );
               end for;
           end for;

           // get the trace-matrix
           tracemat:= ScalarMatrix( BR, dim, 0 );
           for i in [1..dim] do
               for j in [i..dim] do
                   cf:= Coordinates( A, ord[i]*ord[j] );
                   tr:= 0;
                   for k in [1..dim] do
                       tr:= tr + cf[k]*traces[k];
                   end for;
                   tracemat[i][j]:= tr;
                   if i ne j then 
                      tracemat[j][i]:= tr;
                   end if;
               end for;
           end for;
           // factorize the discriminant to obtain a finite set of primes

	   if BR cmpeq Rationals() then
	       disc:= Integers()!AbsoluteValue( Determinant( tracemat ) );
	   else
	       disc:= CR!Normalise( Determinant( tracemat ) );
	   end if;
if false and Characteristic(BR) eq 0 and BR cmpne Rationals() then
"disc = ", disc;
end if;

	    assert old_disc ne disc;
	    old_disc := disc;

           facs:= Factorization( disc );
           primes:= [ u[1] : u in facs ];

           i:= 1;

           while i le #primes and maximal do

                 // maximal will become false once we found a bigger order.

                 p:= primes[i];
                 // we find the radical of L/pL:
            
if false and Characteristic(BR) eq 0 and BR cmpne Rationals() then
	    p;
end if;
		 if Type(p) eq RngValElt then
		     rp, mp := ResidueClassField(Zeros(p/1)[1]);
		 else
		     rp, mp := ResidueClassField(p);
		 end if;
	       ccc_rp := [ [ ] : i in [1..dim] ];
	       for i in [1..dim] do
		   for j in [1..dim] do
		       ccc_rp[i][j]:= [ mp(ccc[i][j][k]) : k in [1 .. dim]];
		   end for;
	       end for;

                 B:= AssociativeAlgebra< rp, Dimension(A) | ccc_rp >;
                 R:= JacobsonRadical( B );
if false and Characteristic(BR) eq 0 and BR cmpne Rationals() then
	     R;
end if;

                 bR:= [ ];
                 for j in [1..Dimension(R)] do
                     cf:= Coordinates( B, B!Basis(R)[j] );
                     Append( ~bR, [ u @@ mp : u in cf ] );
                 end for;

                 // we find maximal ideals containing the radical.

                 S,hom:= quo< B | R >;
if false and Characteristic(BR) eq 0 and BR cmpne Rationals() then
	    S;
end if;
                 if Dimension( S ) eq 0 then
                    // the only maximal ideal is the radical:
                    maxids:= [ [ B!Basis(R)[j] : j in [1..Dimension(R)] ] ];
                 else
                    _,ideals:= CentralIdempotents( S );
                    Bids:= [ [ u@@hom : u in Basis( II ) ] : II in ideals ];
                    maxids:= [ ];
                    for r in [1..#ideals] do
                        // take the pre-image in B, which will contain
                        // the radical; and map the elements into the order
                        // by making the coefficients integral:

                        basI:= [ B!Basis(R)[j] : j in [1..Dimension(R)] ];
                        for j in [1..#ideals] do
                            if j ne r then
                               basI cat:= Bids[j];
                            end if;
                        end for;
                        Append( ~maxids, basI );
                     end for;
                 end if;

                 for r in [1..#maxids] do
                     basI:= maxids[r];
                     b:= [ ];
                     for j in [1..#basI] do
                         cf:= Coordinates( B, basI[j] );
                         Append( ~b, [ u @@ mp : u in cf ] );
                     end for; 

                    // add p*ord:
                    for j in [1..dim] do
                        cf:= [ Parent(p) | 0 : k in [1..dim] ];
                        cf[j]:= p;
                        Append( ~b, cf );
                    end for;

                    // find an integral basis by taking the Hermite form:
                    b:= HermiteForm( Matrix( CR, b ) );
                    zb:= [ ];
                    for j in [1..Nrows(b)] do
                        e:= 0*ord[1];
                        for k in [1..Ncols(b)] do
                            e:= e + b[j][k]*ord[k];
                        end for;
                        if e ne 0*e then
                           Append( ~zb, e );
                        end if;
                    end for; 

                    // left multiplier:
                    gam:= LeftMultiplier( A, zb, CR );
if false and Characteristic(BR) eq 0 and BR cmpne Rationals() then
		gam;
end if;
                     
                    // see whether it is contained in the order:
                    contained:= true;
                    for u in gam do
                        cf:= Coordinates( M, V!Coordinates( A, u ) );
                        if not &and[ a in CR : a in cf ] then
                           contained:= false;
                           break u;
                        end if;
                    end for;
 
                    if not contained then
                       ord:= gam;
                       maximal:= false;
                       break r;
                    end if;                           

                 end for;
                 
                 i:= i+1;
           end while;
     end while;

     return ord, disc, ccc;

end function;

MaxOrd:= function( A, CR )


     // We do not check whether the algebra is semisimple (i.e. radical equal
     // to zero), as this costs too much time. 

     // We compute a maximal order in each central simple component of A, 
     // and put those together. This is faster than computing
     // a maximal order in A directly.
     _,I:= CentralIdempotents( A );
     max:= [ ];
     dd:= 1;
     tabs:= [ ];
     dims:= [ ];
     for B in I do
         o,d,tab:= MaxOrd_sim( B, CR );
         Append( ~tabs, tab );
         dd:= dd*d;
         max cat:= [ A!x : x in o ];
         Append( ~dims, #o );
     end for;

     // put the multiplication table together...
     T:= [ [ [ BaseRing(A) | 0 : i in [1..#max] ] : v in [1..#max] ] : u in [1..#max] ];

     for i in [1..#tabs] do
         for j in [1..#tabs[i]] do
             if i eq 1 then
                i1:= j;
             else
                i1:= &+[ dims[u] : u in [1..i-1] ] + j;
             end if;
             for k in [1..#tabs] do
                 for l in [1..#tabs[k]] do
                     if k eq 1 then
                        i2:= l; 
                     else
                        i2:= &+[ dims[u] : u in [1..k-1] ] + l;
                     end if;
                     // we get the product of the i1-th basis element
                     // and the i2-th basis element.
                     // if i is not equal to k, then this is zero.

                     if i eq k then
                        if i eq 1 then
                           offset:= 0;
                        else
                           offset:= &+[ dims[u] : u in [1..i-1] ];
                        end if;
                        for v in [1..#tabs[i][j][l]] do
                            T[i1][i2][offset+v]:= tabs[i][j][l][v];
                        end for;
                     end if;
                 end for;
             end for;
         end for;
     end for;

     return max, dd, T;

end function;


declare attributes AlgAssV: MaximalOrder;

declare attributes AlgAssVOrd: Discriminant, ReducedDiscriminant, MultiplicationTable;

intrinsic MaximalOrder( A::AlgAssV[FldRat] ) -> AlgAssVOrd
{Maximal order of the algebra A.}

     if assigned A`MaximalOrder then
        return A`MaximalOrder;
     end if;

     o,d,T:= MaxOrd( A, Integers() ); 
     
     o:= Order( Integers(), o );

     o`ReducedDiscriminant:= d;
     o`MultiplicationTable:= T;
     A`MaximalOrder:= o;

     return o;
  
end intrinsic;

intrinsic MaximalOrderFinite( A::AlgAssV[FldFunRat] ) -> AlgAssVOrd
{A maximal order of the algebra A.}

     if assigned A`MaximalOrder then
        return A`MaximalOrder;
     end if;

     require Dimension(A) mod Characteristic(A) ne 0 : "Dimension of the algebra must be non-zero mod the characteristic of the algebra";

     o,d,T:= MaxOrd( A, Integers(CoefficientRing(A)) ); 
     
     o:= Order( Integers(CoefficientRing(A)), o );

     o`ReducedDiscriminant:= d;
     o`MultiplicationTable:= T;
     A`MaximalOrder:= o;

     return o;
  
end intrinsic;

intrinsic MaximalOrderInfinite( A::AlgAssV[FldFunRat] ) -> AlgAssVOrd
{A maximal order of the algebra A.}

     if assigned A`MaximalOrderInfinite then
        return A`MaximalOrderInfinite;
     end if;

     require Dimension(A) mod Characteristic(A) ne 0 : "Dimension of the algebra must be non-zero mod the characteristic of the algebra";

     o,d,T:= MaxOrd( A, ValuationRing(CoefficientRing(A)) ); 
     
     o:= Order( ValuationRing(CoefficientRing(A)), o );

     o`ReducedDiscriminant:= d;
     o`MultiplicationTable:= T;
     A`MaximalOrderInfinite:= o;

     return o;
  
end intrinsic;

function order_maximal_order(R, O)
    A := Algebra(O);

    bO := Basis(O);
    if not ISA(Type(A), AlgAss) then
	A, Am := AssociativeAlgebra(A);
	bO := [Am(x) : x in bO];
    end if;
    B, m := ChangeBasis(A, bO);
    o, d, T := MaxOrd(B, R);

    oB := Order(R, o);

    o := [x @@ m : x in o];
    if assigned Am then
	o := [x @@ Am : x in o];
    end if;

    o:= Order( R, o );

    for i in [1 .. #T] do
	for j in [1 .. #T[i]] do
	    if assigned Am then
		T[i][j] := Coordinates(o, (B!oB!T[i][j]) @@ m @@ Am);
	    else
		T[i][j] := Coordinates(o, (B!oB!T[i][j]) @@ m);
	    end if;
	end for;
    end for;

    o`ReducedDiscriminant:= d;
    o`MultiplicationTable:= T;

    return o;
end function;

intrinsic MaximalOrder(O::AlgAssVOrd[RngInt]) -> AlgAssVOrd
{A maximal order of the algebra of O containing O}
    A := Algebra(O);
    if assigned A`MaximalOrder and &and[x in A`MaximalOrder : x in Basis(O)] then
	return A`MaximalOrder;
    end if;

    o := order_maximal_order(Integers(), O);
    if not assigned Algebra(O)`MaximalOrder then
	A := Algebra(O);
	A`MaximalOrder:= o;
    end if;
    return o;
end intrinsic;

intrinsic MaximalOrder(O::AlgAssVOrd[RngUPol]) -> AlgAssVOrd
{A maximal order of the algebra of O containing O}
    A := Algebra(O);
    if assigned A`MaximalOrder and &and[x in A`MaximalOrder : x in Basis(O)] then
	return A`MaximalOrder;
    end if;

    o := order_maximal_order(CoefficientRing(O), O);
    if not assigned Algebra(O)`MaximalOrder then
	A := Algebra(O);
	A`MaximalOrder:= o;
    end if;
    return o;
end intrinsic;

intrinsic MaximalOrder(O::AlgAssVOrd[RngVal]) -> AlgAssVOrd
{A maximal order of the algebra of O containing O}
    A := Algebra(O);
    if assigned A`MaximalOrderInfinite and &and[x in A`MaximalOrderInfinite : x in Basis(O)] then
	return A`MaximalOrderInfinite;
    end if;

    o := order_maximal_order(CoefficientRing(O), O);
    if not assigned Algebra(O)`MaximalOrderInfinite then
	A := Algebra(O);
	A`MaximalOrderInfinite := o;
    end if;
    return o;
end intrinsic;

/*
// Using extended types here [RngInt] causes ambiguous sig matches with
// the AlgQuatOrd sig
intrinsic Discriminant( O::AlgAssVOrd ) -> RngIntElt
{Discriminant of the order O.}

     require assigned O`MultiplicationTable : "Discriminant is not known";
     return O`Discriminant;

end intrinsic;
*/

intrinsic MultiplicationTable( O::AlgAssVOrd ) -> SeqEnum
{Multiplication table of the order O.}

     require assigned O`MultiplicationTable : "Multiplication Table is not known";
     return O`MultiplicationTable;

end intrinsic;


intrinsic Coordinates(O::AlgAssVOrd, a::AlgAssVElt) -> SeqEnum
{The coordinates of the element a with respect to the basis of O
 (a must be coercible into O)}

    c, s := IsCoercible(O, a);
    require c : "Element is not in the order";
    return Eltseq(s);

end intrinsic;
