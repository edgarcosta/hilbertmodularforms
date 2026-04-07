
// Test ProjectiveLine(R::RngOrdRes)
// Nov 2011, SRD

_<x> := PolynomialRing(Rationals());

pols := [ < x - 1,        36 >,
          < x^2 - x - 1,  60 >,
          < x^3 - 6,      36 >,
          < x^3 - x - 1,  60 >
];

for tup in pols do

    f, nb := Explode(tup);
    printf "f = %o, ideals up to norm %o\n", f, nb;

    F<w> := NumberField(f : DoLinearExtension);
    O := Integers(F);

    for I in IdealsUpTo(nb, F) do
        R := quo<O|I>;
        B := Basis(I) cat [O| n*Minimum(I) : n in {1..4}];

        printf "Norm : ", Norm(I);
        time 
        P1, P1rep := ProjectiveLine(R);

        for x in P1 do
           assert Minimum(ideal<O|x[1],x[2]> + I) eq 1;
           b, xx, s := P1rep(x, true, true);
           assert b and xx eq x;
           assert Minimum(s*O+I) eq 1;
        end for;

        for u,v in Elements(R) do
           b, x, s := P1rep([u,v], true, true);
           if b then
              assert x in P1;
              assert Minimum(s*O+I) eq 1;
              assert (s*u) mod I eq x[1] mod I;
              assert (s*v) mod I eq x[2] mod I;
           end if;
           u1 := u + Random(B);
           v1 := v + Random(B);
           b1, x1, s1 := P1rep([O|u1,v1], true, true);
           assert b1 eq b;
           if b1 then
              assert x1 eq x;
              assert Minimum(s1*O+I) eq 1;
              assert (s1*u1) mod I eq x[1] mod I;
              assert (s1*v1) mod I eq x[2] mod I;
           end if;
           if Minimum(I) ne 1 then
              s := Random(B);
              assert not P1rep([s*u,s*v], true, true);
           end if;
        end for;

    end for;

end for;

