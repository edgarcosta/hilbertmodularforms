// TODO this needs to be *much* smaller, 
TOLERANCE := 0.01;

R<x> := PolynomialRing(RationalField());

// The quadratic number field Q(sqrt(3)). 

F<a> := NumberField(x^2-3);
ZF := Integers(F);
basis := Basis(ZF);
places := InfinitePlaces(F);
gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 1;
eps := gens[1];

nu := 7*ZF.1 - 4*ZF.2;
nu_prime, eps_prime := FunDomainRep(nu);
assert eps_prime eq nu;
assert nu_prime eq F!1;

nu := 10*ZF.1;
nu_prime, eps_prime := FunDomainRep(nu);
assert eps_prime eq F!1;
assert nu_prime eq nu;

nu := 45*ZF.1 + 23*ZF.2;
nu_prime, eps_prime := FunDomainRep(nu);
assert nu_prime eq nu * eps;

// "lower" wall point stay the same
nu := 2*ZF.1 + 2/3*ZF.2;
nu_prime, eps_prime := FunDomainRep(nu);
assert nu_prime eq nu;

// "upper" wall point should be reduced to the lower wall
assert F.1 eq ZF.2;
nu := 2*ZF.1 - 2/3*ZF.2;
nu_prime, eps_prime := FunDomainRep(nu);
assert nu_prime eq nu / eps;

// The cubic number field Q(zeta_7)+. 

F<a> := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);
basis := Basis(ZF);
places := InfinitePlaces(F);

gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 2;
eps_1 := gens[1];
eps_2 := gens[2];

nu := 1*basis[1] + 2*basis[2] + 3*basis[3];
nu_prime, eps_prime := FunDomainRep(nu);
assert nu_prime eq nu/eps_2;
//rep_embed := [Evaluate(rep, places[i]) : i in [1, 2, 3]];
//assert Abs(rep_embed[1] - 12.542876546957239435622233943040328966125486709642126932300421480979986755594803638458377953396537060638970481992397465334397641293479711072585112648823806882758838455) lt TOLERANCE;
//assert Abs(rep_embed[2] - 4.4178947925446465132165748450107518219373171256199260573969790264217653029157415164006286696983915185734010485386542777656639632403882414360609929478152080199995595143) lt TOLERANCE;
//assert Abs(rep_embed[3] - 2.0392286604981140511611912119489192119371961647379470103025994925982479414894548451409933769050714207876284694689482568999383954661320474913538944033609850972416020305) lt TOLERANCE;


