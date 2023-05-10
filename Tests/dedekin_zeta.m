printf "Testing DedekindZetaExact at -1... D=";
for i in [1..10] do
    D := RandomBits(10);
    printf "%o ", D;
    K := QuadraticField(D);
    if Degree(K) eq 1 then
        continue;
    end if;
    v := DedekindZetaExact(K, -1);
    assert Abs(Evaluate(DedekindZeta(K), -1) - v)/v lt 1e-27;
end for;
