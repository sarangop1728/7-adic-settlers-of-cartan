// theorem-1.m -- the checks of Section 5 of "7-adic Galois representations of
// elliptic curves over the rationals via Kummer descent".
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b theorem-1.m < /dev/null
SetQuitOnError(true);
SetColumns(0);
reportStartTime := Cputime();

procedure statement(name, label, title)
     rule := &cat[ "-" : i in [1..76] ];
     printf "\n%o\n%o  %o   [%o]\n%o\n", rule, name, title, label, rule;
end procedure;

// formatting: a value on one line; a rational number as a product of prime powers;
// a sequence of strings joined; a projective point (a : b : c); a solution (x, y, w)
function joined(strings, separator)
     if #strings eq 0 then return ""; end if;
     text := strings[1];
     for s in strings[2..#strings] do text cat:= separator cat s; end for;
     return text;
end function;

function compact(value)
     return joined([ l : l in Split(Sprint(value), "\n") ], " ");
end function;

function primePowers(m)
     if m eq 1 then return "1"; end if;
     return joined([ p[2] eq 1 select Sprint(p[1]) else Sprintf("%o^%o", p[1], p[2])
                     : p in Factorization(m) ], " * ");
end function;

function factored(n)
     n := Rationals() ! n;
     if n eq 0 then return "0"; end if;
     text := (n lt 0 select "-" else "") cat primePowers(Numerator(Abs(n)));
     if Denominator(n) ne 1 then text cat:= " / " cat primePowers(Denominator(n)); end if;
     return text;
end function;

function pointString(coordinates)
     return "(" cat joined([ Sprint(c) : c in coordinates ], " : ") cat ")";
end function;

function tupleString(entries)
     return "(" cat joined([ Sprint(e) : e in entries ], ", ") cat ")";
end function;

procedure show(description, value)
     printf "  %o: %o\n", description, Type(value) eq MonStgElt select value else compact(value);
end procedure;

procedure verified()
     printf "  verified\n";
end procedure;

procedure finish(file)
     printf "\n%o: every check passed, in %o seconds of CPU time.\n", file, RealField(3) ! Cputime(reportStartTime);
end procedure;
// the base rings
QQ := Rationals();
ZZ := Integers();
polynomialRingQ<t> := PolynomialRing(QQ);
binaryFormRing<x, y> := PolynomialRing(ZZ, 2);

// the field K, the roots theta, sigma, the prime above 7, the units epsilon1, epsilon2
fSplit    := t^3 - 4*t^2 + 3*t + 1;          // X_sp^+(7)
fNonsplit := t^3 - 7*t^2 + 7*t + 7;          // X_ns^+(7)

cyclotomicField<zeta> := CyclotomicField(7);
zetaTrace := func< a | zeta^a + zeta^(-a) >;   // c_a = zeta^a + zeta^-a

K<theta> := NumberField(fSplit);             // theta = theta_sp
OK := RingOfIntegers(K);
embedInCyclotomic := hom< K -> cyclotomicField | 1 - zetaTrace(1) >;
sigma := hom< K -> K | -theta^2 + 2*theta + 2 >;
thetaSplit    := theta;
thetaNonsplit := 5 - 2*theta;

factorizationOf7 := Factorization(7*OK);
primeAbove7 := factorizationOf7[1][1];

epsilon1 := theta - 1;
epsilon2 := 2 - theta;

// the rings of ternary forms
formRingOverQ<a0, a1, a2> := PolynomialRing(QQ, 3);
formRingOverK<A0, A1, A2> := PolynomialRing(K, 3);
projectivePlane := ProjectiveSpace(formRingOverQ);

// sigma^i for i = 0, 1, 2
function sigmaPower(element, i)
     case i:
          when 0: return element;
          when 1: return sigma(element);
          when 2: return sigma(sigma(element));
     end case;
     error "sigmaPower expects i in {0,1,2}";
end function;

// coordinates in the power basis 1, theta, theta^2 of the given theta
function coordinatesInBasis(element, theta)
     basis := Matrix(QQ, [ Eltseq(K!1), Eltseq(theta), Eltseq(theta^2) ]);
     return Eltseq(Vector(QQ, Eltseq(element)) * basis^-1);
end function;

// the three components of a form over K along 1, theta, theta^2
function coordinateForms(polynomial, theta)
     coefficients := Coefficients(polynomial);
     monomials    := Monomials(polynomial);
     return [ &+[ coordinatesInBasis(coefficients[i], theta)[j]
                  * Monomial(formRingOverQ, Exponents(monomials[i]))
                : i in [1..#coefficients] ]
            : j in [1..3] ];
end function;

// Tr_{K/Q} and sigma, coefficient by coefficient
function traceOfCoefficients(polynomial)
     coefficients := Coefficients(polynomial);
     monomials    := Monomials(polynomial);
     return &+[ (QQ ! Trace(coefficients[i])) * Monomial(formRingOverQ, Exponents(monomials[i]))
              : i in [1..#coefficients] ];
end function;

function applySigmaToCoefficients(polynomial)
     coefficients := Coefficients(polynomial);
     monomials    := Monomials(polynomial);
     return &+[ sigma(coefficients[i])*monomials[i] : i in [1..#coefficients] ];
end function;

// u_0 = a_0 + a_1 theta + a_2 theta^2, and the three forms P^(n) of delta u_0^7
function genericElement(theta)
     return A0 + theta*A1 + theta^2*A2;
end function;

function PForms(delta, theta)
     return coordinateForms(delta*genericElement(theta)^7, theta);
end function;

// the chosen root of f and f'(theta)
derivativeAtThetaSplit    := Evaluate(Derivative(fSplit), thetaSplit);
derivativeAtThetaNonsplit := Evaluate(Derivative(fNonsplit), thetaNonsplit);

function rootAndDerivative(f)
     if f eq fSplit then
          return thetaSplit, derivativeAtThetaSplit;
     end if;
     return thetaNonsplit, derivativeAtThetaNonsplit;
end function;

// primitive pair (x,y) <-> gamma = (x - theta y)/f'(theta)
function gammaOfPair(pair, theta, derivativeAtTheta)
     return (pair[1] - theta*pair[2])/derivativeAtTheta;
end function;

function primitivePairOfGamma(gamma, theta, derivativeAtTheta)
     coordinates := coordinatesInBasis(gamma*derivativeAtTheta, theta);
     assert coordinates[3] eq 0;
     denominator := LCM(Denominator(coordinates[1]), Denominator(coordinates[2]));
     first  := ZZ ! ( denominator*coordinates[1]);
     second := ZZ ! (-denominator*coordinates[2]);
     common := GCD(first, second);
     first  := first  div common;
     second := second div common;
     if second lt 0 or (second eq 0 and first lt 0) then
          first := -first; second := -second;
     end if;
     return [first, second];
end function;

// the primitive solutions of f(x,y) = a, for a in a list of values
function thueSolutions(f, values)
     thueEquation := Thue(PolynomialRing(ZZ) ! f);
     solutions := &cat[ Solutions(thueEquation, a) : a in values ];
     return { (s[2] lt 0 or (s[2] eq 0 and s[1] lt 0)) select [-s[1], -s[2]] else [s[1], s[2]]
            : s in solutions | GCD(s[1], s[2]) eq 1 };
end function;

// Zywina's models: j_ns = H_ns^3/F_ns^7, j_sp = x H_sp^3/(y F_sp)^7
FNonsplit := x^3 - 7*x^2*y + 7*x*y^2 + 7*y^3;
HNonsplit := 4*x*(x^2 + 7*y^2)*(x^2 - 7*x*y + 14*y^2)*(5*x^2 - 14*x*y - 7*y^2);
FSplit    := x^3 - 4*x^2*y + 3*x*y^2 + y^3;
HSplit    := (x + y)*(x^2 - 5*x*y + y^2)*(x^2 - 5*x*y + 8*y^2)
             *(x^4 - 5*x^3*y + 8*x^2*y^2 - 7*x*y^3 + 7*y^4);

function jNonsplit(a, b)
     return Evaluate(HNonsplit, [a,b])^3 / Evaluate(FNonsplit, [a,b])^7;
end function;

function jSplit(a, b)
     return a*Evaluate(HSplit, [a,b])^3 / (b*Evaluate(FSplit, [a,b]))^7;
end function;

// the CM discriminant of a j-invariant, 0 if none
function cmDiscriminant(j)
     if j eq 0 then return -3; end if;
     if j eq 1728 then return -4; end if;
     hasCM, discriminant := HasComplexMultiplication(EllipticCurveFromjInvariant(j));
     return hasCM select discriminant else 0;
end function;
selmerGroupAt7, toSelmerAt7 := pSelmerGroup(7, { primeAbove7 });
Sigma, toSigma := quo< selmerGroupAt7 | toSelmerAt7(K!7) >;

// the class in Sigma of an element of Q^* O_K[1/7]^* K^*7
function selmerClass(element)
     return toSigma(toSelmerAt7(element));
end function;

// strip the prime-to-7 rational part, which is trivial in Sigma
function selmerClassModRationals(element)
     norm := Norm(element);
     for p in PrimeDivisors(Numerator(norm)*Denominator(norm)) do
          if p ne 7 then
               valuation := Valuation(element, Factorization(p*OK)[1][1]);
               element := element/p^valuation;
          end if;
     end for;
     return selmerClass(element);
end function;
function badPrimes(f, k)
     return PrimeDivisors(ZZ ! (k*Discriminant(f)));
end function;

function selmerGroup(f, k)
     primesAboveBad := { factor[1] : factor in Factorization((&*badPrimes(f,k))*OK) };
     return pSelmerGroup(7, primesAboveBad);
end function;

function Delta(f, k)
     selmer, toSelmer := selmerGroup(f, k);
     representatives := [ K ! (s @@ toSelmer) : s in selmer ];
     return [ d : d in representatives | IsPower(Norm(d)/k, 7) ];
end function;

pairs := [ <fNonsplit, 1>, <fNonsplit, 8>, <fNonsplit, 7>, <fNonsplit, 56>,
           <fSplit, 1>, <fSplit, 7> ];
DeltaSets := [ Delta(p[1], p[2]) : p in pairs ];
alpha := theta^2 - 5*theta + 1;

varpi := 1 + theta;
residueFieldAt7, reduceAt7 := ResidueClassField(primeAbove7);

// g = varpi^a u with u = u0 (1 + b varpi) mod varpi^2, and kappa(g) = b + 4a
function kappa(g)
     a  := Valuation(g, primeAbove7);
     u  := g/varpi^a;
     u0 := reduceAt7(u);
     b  := reduceAt7((u - (ZZ ! u0))/varpi)/u0;
     return b + 4*a;
end function;

statement("(5.1), Lemma 5.1", "lem:kappa", "the homomorphism kappa");
// (5.1): N(varpi) = 7, 7 = varpi^3 theta^-2, sigma(varpi) = varpi (4 - varpi)
assert Norm(varpi) eq 7;
assert 7 eq varpi^3*theta^-2;
assert sigma(varpi) eq varpi*(4 - varpi);
// (5.1): f'(theta) = varpi^2 (3 - 2 varpi/theta)
assert derivativeAtThetaSplit eq varpi^2*(3 - 2*varpi/theta);
show("kappa(7), kappa(2), kappa(3), kappa(-1)", [ kappa(K ! a) : a in [7, 2, 3, -1] ]);
// kappa kills Q^*: kappa(7) = kappa(2) = kappa(3) = kappa(-1) = 0
assert [ kappa(K ! a) : a in [7, 2, 3, -1] ] eq [0, 0, 0, 0];
sample := [ varpi, epsilon1, epsilon2, theta, alpha, 3*theta^2 - theta + 5, (2*theta - 9)/(theta^2 + 3) ];
show("kappa on varpi, epsilon1, epsilon2, theta, alpha", [ kappa(a) : a in sample[1..5] ]);
// kappa is a homomorphism (on a sample)
assert forall{ <a,b> : a, b in sample | kappa(a*b) eq kappa(a) + kappa(b) };
// kappa o sigma = 4 kappa (on a sample)
assert forall{ a : a in sample | kappa(sigma(a)) eq 4*kappa(a) };
verified();

statement("Lemma 5.2", "lem:V", "the space Sigma");
// (1) the units
unitGroup, toUnitGroup := UnitGroup(K);
// (1): epsilon1 = theta - 1 and epsilon2 = 2 - theta are units
assert Norm(epsilon1) in {1,-1};
assert Norm(epsilon2) in {1,-1};
// (1): -1, epsilon1, epsilon2 generate the unit group of K
assert sub< unitGroup | [ u @@ toUnitGroup : u in [K ! -1, epsilon1, epsilon2] ] > eq unitGroup;
// (1): sigma(epsilon1) = epsilon2^-1 and sigma(epsilon2) = -epsilon1 epsilon2^-1
assert sigma(epsilon1) eq epsilon2^-1;
assert sigma(epsilon2) eq -epsilon1*epsilon2^-1;

// (2) Sigma = O_K^* / (+- O_K^*7)
// (2): a unit is trivial in Sigma exactly when it is +- the seventh power of a unit:
// -1 is trivial, and epsilon1^i epsilon2^j with 0 <= i, j <= 6 is trivial only for i = j = 0
assert selmerClass(K ! -1) eq Sigma ! 0;
assert forall{ <i,j> : i, j in [0..6] |
               (selmerClass(epsilon1^i*epsilon2^j) eq Sigma ! 0) eq (i eq 0 and j eq 0) };
// (2): Sigma is generated by the classes of epsilon1 and epsilon2
assert sub< Sigma | [ selmerClass(epsilon1), selmerClass(epsilon2) ] > eq Sigma;

// (3) the structure of Sigma
SigmaGenerators := [ K ! ((Sigma.i @@ toSigma) @@ toSelmerAt7) : i in [1..2] ];
sigmaOnSigma := Matrix(GF(7), [ Eltseq(selmerClass(sigma(a))) : a in SigmaGenerators ]);
polynomialRingF7<X> := PolynomialRing(GF(7));
show("characteristic polynomial of sigma on Sigma", polynomialRingF7 ! CharacteristicPolynomial(sigmaOnSigma));
// (3): sigma acts on Sigma with eigenvalues 2 and 4
assert CharacteristicPolynomial(sigmaOnSigma) eq PolynomialRing(GF(7)) ! [1,1,1];
// (3): sigma = 2 on [epsilon1 epsilon2^2] and sigma = 4 on [epsilon1 epsilon2^4]
assert selmerClass(sigma(epsilon1*epsilon2^2)) eq 2*selmerClass(epsilon1*epsilon2^2);
assert selmerClass(sigma(epsilon1*epsilon2^4)) eq 4*selmerClass(epsilon1*epsilon2^4);
// (3): the two classes generate Sigma
assert sub< Sigma | [ selmerClass(epsilon1*epsilon2^2), selmerClass(epsilon1*epsilon2^4) ] > eq Sigma;

// (4) kappa on Sigma
show("kappa(epsilon1), kappa(epsilon2)", [ kappa(epsilon1), kappa(epsilon2) ]);
// (4): kappa(epsilon1) = 3 and kappa(epsilon2) = 2
assert kappa(epsilon1) eq 3;
assert kappa(epsilon2) eq 2;
kernelOfKappaOnSigma := sub< Sigma | [ selmerClass(a) : a in [ epsilon1^i*epsilon2^j : i, j in [0..6] ]
                                       | kappa(a) eq 0 ] >;
imageOfThreePlusSigma := sub< Sigma | [ selmerClass(a^3*sigma(a)) : a in [epsilon1, epsilon2] ] >;
// (4): ker(kappa on Sigma) = (3 + sigma) Sigma, a line
assert #kernelOfKappaOnSigma eq 7;
assert kernelOfKappaOnSigma eq imageOfThreePlusSigma;
eigenvector2 := Basis(Eigenspace(sigmaOnSigma, 2))[1];
// (4): (3 + sigma) Sigma = Sigma_2
assert imageOfThreePlusSigma eq sub< Sigma | Sigma ! Eltseq(eigenvector2) >;
verified();

statement("Proposition 5.3", "prop:seven-adic", "the 7-adic step");
show("kappa(f'(theta_sp))", kappa(derivativeAtThetaSplit));
// kappa(f'(theta)) = 4
assert kappa(derivativeAtThetaSplit) eq 4;
primitivePairsMod49 := [ [a,b] : a, b in [0..48] | GCD([a,b,7]) eq 1 ];
show("primitive pairs (x,y) mod 49", #primitivePairsMod49);
// (1): 7 | F_sp(x,y) implies kappa((x - theta y)/f'(theta)) = 0, for all primitive
// (x,y) mod 49
assert forall{ pair : pair in primitivePairsMod49 | Evaluate(FSplit, pair) mod 7 ne 0 or
               kappa(gammaOfPair(pair, thetaSplit, derivativeAtThetaSplit)) eq 0 };
// (1): 7 | F_ns(x,y) implies kappa((x - theta y)/f'(theta)) = 0, for all primitive
// (x,y) mod 49
assert forall{ pair : pair in primitivePairsMod49 | Evaluate(FNonsplit, pair) mod 7 ne 0 or
               kappa(gammaOfPair(pair, thetaNonsplit, derivativeAtThetaNonsplit)) eq 0 };
// if 7 does not divide F_sp(x,y), then kappa = 0 iff x = 4y mod 7
assert forall{ pair : pair in primitivePairsMod49 | Evaluate(FSplit, pair) mod 7 eq 0 or
               ((kappa(gammaOfPair(pair, thetaSplit, derivativeAtThetaSplit)) eq 0)
                eq ((pair[1] - 4*pair[2]) mod 7 eq 0)) };

// (3): each solution with 7 | k has a unique delta in Delta(theta,k), with kappa(delta/f'(theta)) = 0
function deltasOfPair(pair, i)
     theta, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
     return [ K ! d : d in DeltaSets[i] | IsPower((pair[1] - theta*pair[2])/(K ! d), 7) ];
end function;
solutionsWithSevenDividingK := [ <3, [ [0,1] ]>, <4, [ [7,1], [7,3] ]>, <6, [ [-1,1], [5,2], [4,3] ]> ];
// (3): each solution of Theorem 1 has a unique delta in Delta(theta,k), and
// kappa(delta/f'(theta)) = 0
for entry in solutionsWithSevenDividingK do
     i, solutions := Explode(entry);
     assert pairs[i][2] mod 7 eq 0;
     _, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
     for pair in solutions do
          deltas := deltasOfPair(pair, i);
          assert #deltas eq 1;
          assert kappa(deltas[1]/derivativeAtTheta) eq 0;
     end for;
end for;
verified();

statement("Theorem 1, (5.2)", "thm:superelliptic", "the solutions of F(x,y) = k w^7 with 7 | k");
// (5.2): -(1 + theta)/f'(theta) = 7^-3 alpha^3 sigma(alpha)
assert -(1 + theta)/derivativeAtThetaSplit eq alpha^3*sigma(alpha)/7^3;
gammaConjugates := [ sigmaPower(alpha^3*sigma(alpha), i) : i in [0..2] ];
// the gamma_i = sigma^i(alpha^3 sigma(alpha)) have trace zero
assert forall{ gamma : gamma in gammaConjugates | Trace(gamma) eq 0 };
// (5.2): f'(theta) gamma_i = -7^3(1 + theta), 7^3(5 - 2 theta), -7^3(4 - 3 theta)
assert [ derivativeAtThetaSplit*gamma : gamma in gammaConjugates ]
       eq [ -7^3*(1 + theta), 7^3*(5 - 2*theta), -7^3*(4 - 3*theta) ];
solutionsSplit := [ primitivePairOfGamma(gamma, thetaSplit, derivativeAtThetaSplit) : gamma in gammaConjugates ];
solutionsNonsplit := [ primitivePairOfGamma(gamma, thetaNonsplit, derivativeAtThetaNonsplit) : gamma in gammaConjugates ];
show("(x,y) from the gamma_i, split model", solutionsSplit);
show("F_sp(x,y)", [ Evaluate(FSplit, pair) : pair in solutionsSplit ]);
show("(x,y) from the gamma_i, nonsplit model", solutionsNonsplit);
show("F_ns(x,y)", [ Evaluate(FNonsplit, pair) : pair in solutionsNonsplit ]);
// Theorem 1 for F_sp: (x,y) = (-1,1), (5,2), (4,3), with F_sp = -7, -7, 7
assert solutionsSplit eq [ [-1,1], [5,2], [4,3] ];
assert [ Evaluate(FSplit, pair) : pair in solutionsSplit ] eq [ -7, -7, 7 ];
// Theorem 1 for F_ns: (x,y) = (7,1), (0,1), (7,3), with F_ns = 56, 7, -56
assert solutionsNonsplit eq [ [7,1], [0,1], [7,3] ];
assert [ Evaluate(FNonsplit, pair) : pair in solutionsNonsplit ] eq [ 56, 7, -56 ];
// Thue: the primitive solutions of F_sp = +-7 are exactly (-1,1), (5,2), (4,3)
assert thueSolutions(fSplit, [7, -7]) eq Seqset(solutionsSplit);
// Thue: the primitive solutions of F_ns = +-7, +-56 are exactly (0,1), (7,1), (7,3)
assert thueSolutions(fNonsplit, [7, -7, 56, -56]) eq Seqset(solutionsNonsplit);
show("CM discriminants of j at these points (0 = no CM), ns and sp",
     [ [ cmDiscriminant(jNonsplit(pair[1], pair[2])) : pair in [[0,1],[7,1],[7,3]] ],
       [ cmDiscriminant(jSplit(pair[1], pair[2])) : pair in [[-1,1],[5,2],[4,3]] ] ]);
// Table 1: j = 0 at (0,1) and (-1,1), and no CM at the other four points
assert [ cmDiscriminant(jNonsplit(pair[1], pair[2])) : pair in [[0,1],[7,1],[7,3]] ] eq [-3, 0, 0];
assert [ cmDiscriminant(jSplit(pair[1], pair[2])) : pair in [[-1,1],[5,2],[4,3]] ] eq [-3, 0, 0];
verified();

statement("Example 5.4", "ex:five-two", "the solution (5, 2, -1)");
eta := (5 - 2*theta)/derivativeAtThetaSplit;
show("eta = (5 - 2 theta)/f'(theta)", eta);
// 5 - 2 theta has norm -7 and represents a class of Delta(theta_sp, 7)
assert Norm(5 - 2*theta) eq -7;
assert exists{ d : d in DeltaSets[6] | IsPower((5 - 2*theta)/d, 7) };
// 5 - 2 theta = varpi (-2 + theta^-2 varpi^2)
assert 5 - 2*theta eq varpi*(-2 + theta^-2*varpi^2);
// kappa(5 - 2 theta) = 4 = kappa(f'(theta)), so kappa(eta) = 0
assert kappa(5 - 2*theta) eq 4;
assert kappa(derivativeAtThetaSplit) eq 4;
assert kappa(eta) eq 0;
// eta = 7^-3 sigma(alpha)^3 sigma^2(alpha)
assert eta eq sigma(alpha)^3*sigma(sigma(alpha))/7^3;
// [1] lies on Z_{theta,delta}
assert Trace(eta) eq 0;
// [sigma(alpha)] lies on Z_0
assert Trace(sigma(alpha)^3*sigma(sigma(alpha))) eq 0;
verified();

statement("Remark 5.5", "rem:no-C", "the classes with kappa = 0");
show("number of delta with kappa(delta/f'(theta)) = 0, for the six pairs",
     [ #[ d : d in DeltaSets[i] | kappa((K ! d)/derivative) eq 0 ]
       where _, derivative := rootAndDerivative(pairs[i][1]) : i in [1..#pairs] ]);
// exactly 7 classes delta in Delta with kappa(delta/f'(theta)) = 0, for each pair with
// 7 | k
assert forall{ i : i in [1..#pairs] | pairs[i][2] mod 7 ne 0 or
               #[ d : d in DeltaSets[i] | kappa((K ! d)/derivative) eq 0 ] eq 7
               where _, derivative := rootAndDerivative(pairs[i][1]) };
// the three solutions of F_sp = +-7 give three distinct classes in Sigma, all with kappa = 0
gammasOfSolutions := [ gammaOfPair(pair, thetaSplit, derivativeAtThetaSplit) : pair in [ [-1,1], [5,2], [4,3] ] ];
assert #{ selmerClassModRationals(gamma) : gamma in gammasOfSolutions } eq 3;
assert forall{ gamma : gamma in gammasOfSolutions | kappa(gamma) eq 0 };
verified();

statement("Proposition 5.6, Remark 5.7", "prop:klein-twists", "the twists of the Klein quartic");
// the eigenvectors of Lemma 5.2: [epsilon1 epsilon2^2] in Sigma_2, g = epsilon1 epsilon2^4 in Sigma_4
sigma2Generator := epsilon1*epsilon2^2;
g := epsilon1*epsilon2^4;
// kappa(epsilon1 epsilon2^2) = 0 and kappa(g) = 4
assert kappa(sigma2Generator) eq 0;
assert kappa(g) eq 4;
// sigma[g] = 4[g] in Sigma
assert selmerClassModRationals(sigma(g)) eq selmerClassModRationals(g^4);

// coordinates (s,c) in Sigma = Sigma_2 + Sigma_4
coordinatesInSigma := AssociativeArray();
for s in [0..6] do
     for c in [0..6] do
          coordinatesInSigma[selmerClassModRationals(sigma2Generator^s*g^c)] := [s, c];
     end for;
end for;
// [epsilon1 epsilon2^2] and [g] form a basis of Sigma
assert #Keys(coordinatesInSigma) eq 49;
// (1): for each of the six pairs, kappa(delta/f'(theta)) = 4c, with c the Sigma_4-coordinate
for i in [1..#pairs] do
     _, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
     etas := [ (K ! d)/derivativeAtTheta : d in DeltaSets[i] ];
     assert forall{ eta : eta in etas | kappa(eta) eq 4*coordinatesInSigma[selmerClassModRationals(eta)][2] };
end for;

// Z(eta) = { Tr(eta v^3 sigma(v)) = 0 } in the coordinates of 1, theta_sp, theta_sp^2,
// as a primitive integral form
integralFormRing := PolynomialRing(ZZ, 3);
function ZForm(eta)
     v := genericElement(thetaSplit);
     form := traceOfCoefficients(eta*v^3*applySigmaToCoefficients(v));
     form := LCM([ Denominator(a) : a in Coefficients(form) ])*form;
     return integralFormRing ! (form/GCD([ ZZ ! a : a in Coefficients(form) ]));
end function;
// sigma induces Z(eta) -> Z(sigma(eta)): Tr(sigma(g) sigma(v)^3 sigma^2(v)) = Tr(g v^3 sigma(v))
v := genericElement(thetaSplit);
sv := applySigmaToCoefficients(v);
assert traceOfCoefficients(sigma(g)*sv^3*applySigmaToCoefficients(sv)) eq traceOfCoefficients(g*v^3*sv);

function pointCount(form, p)
     reduction := Curve(ProjectiveSpace(GF(p), 2), ChangeRing(form, GF(p)));
     return IsNonsingular(reduction) select #RationalPoints(reduction) else -1;
end function;
kleinForm := integralFormRing ! (a0^3*a1 + a1^3*a2 + a2^3*a0);
threeForms := [ ZForm(K ! 1), ZForm(g), ZForm(g^3) ];
show("#Z(1)(F_29), #Z(g)(F_29), #Z(g^3)(F_29), #Klein(F_29)",
     [ pointCount(form, 29) : form in threeForms cat [kleinForm] ]);
// (2): Z(1), Z(g), Z(g^3) are smooth mod 29, with 24, 45, 17 points (pointCount is -1
// on a singular reduction)
assert [ pointCount(form, 29) : form in threeForms ] eq [24, 45, 17];
// (2): the Klein quartic has 24
assert pointCount(kleinForm, 29) eq 24;
// (2): #Z(eta)(F_29) only depends on the sigma-orbit of c, for all 49 classes
function expectedCount(c)
     return c eq 0 select 24 else (c in {1,2,4} select 45 else 17);
end function;
assert forall{ <s,c> : s, c in [0..6] | pointCount(ZForm(sigma2Generator^s*g^c), 29) eq expectedCount(c) };
show("point counts of the three curves at p < 29, p ne 7",
     [ <p, [ pointCount(form, p) : form in threeForms ]> : p in PrimesUpTo(28) | p ne 7 ]);
// Remark 5.7: the three curves are smooth with equal point counts at every prime p < 29, p ne 7
for p in [ p : p in PrimesUpTo(28) | p ne 7 ] do
     counts := { pointCount(form, p) : form in threeForms };
     assert #counts eq 1;
     assert Rep(counts) ge 0;
end for;
verified();

finish("theorem-1.m");
quit;
