// kummer.m -- the checks of Section 3 of "7-adic Galois representations of
// elliptic curves over the rationals via Kummer descent".
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b kummer.m < /dev/null
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

statement("Table 3", "tab:descent-data", "the data of the descent");
printf "  %-6o %-22o %-10o %-4o %-8o %-10o %o\n", "", "f", "disc(f)", "k", "S", "#K(7,S)", "#Delta";
for i in [1..#pairs] do
     f, k := Explode(pairs[i]);
     printf "  %-6o %-22o %-10o %-4o %-8o %-10o %o\n", f eq fSplit select "sp" else "ns",
            f eq fSplit select "t^3 - 4t^2 + 3t + 1" else "t^3 - 7t^2 + 7t + 7",
            factored(Discriminant(f)), k, Sprint(badPrimes(f, k)),
            factored(#selmerGroup(f, k)), #DeltaSets[i];
end for;
// #K(7,S) = 7^3 for f_sp and 7^4 for f_ns
assert forall{ p : p in pairs | #selmerGroup(p[1], p[2]) eq (p[1] eq fSplit select 7^3 else 7^4) };
// S = {7} for f_sp and {2,7} for f_ns, for every k
assert forall{ p : p in pairs | badPrimes(p[1], p[2]) eq (p[1] eq fSplit select [7] else [2,7]) };
// #Delta = 49 for all six pairs (F,k)
assert forall{ D : D in DeltaSets | #D eq 49 };

varpi := 1 + theta;
primeAbove2 := Factorization(2*OK)[1][1];
unitGroup, toUnits := UnitGroup(OK);
// 2 is inert in K
assert #Factorization(2*OK) eq 1;
assert Degree(primeAbove2) eq 3;
// varpi = 1 + theta generates the prime above 7
assert ideal< OK | OK ! varpi > eq primeAbove7;
// varpi has norm 7
assert Norm(varpi) eq 7;
// O_K^* = +-<epsilon1, epsilon2>
assert sub< unitGroup | [ (OK ! u) @@ toUnits : u in [-1, epsilon1, epsilon2] ] > eq unitGroup;
// valuations at (7) and (2): varpi has (1,0), 2 has (0,1), epsilon1 and epsilon2 have (0,0)
function valuationsAt7And2(a)
     return [ Valuation(K ! a, P) : P in [primeAbove7, primeAbove2] ];
end function;
assert valuationsAt7And2(varpi) eq [1,0];
assert valuationsAt7And2(2) eq [0,1];
assert valuationsAt7And2(epsilon1) eq [0,0];
assert valuationsAt7And2(epsilon2) eq [0,0];
verified();

statement("Lemma 3.4", "lem:trace-form", "the trace form");
show("Tr(theta_sp^i / f_sp'(theta_sp)), i = 0, 1, 2",
     [ Trace(thetaSplit^i/derivativeAtThetaSplit) : i in [0..2] ]);
show("Tr(theta_ns^i / f_ns'(theta_ns)), i = 0, 1, 2",
     [ Trace(thetaNonsplit^i/derivativeAtThetaNonsplit) : i in [0..2] ]);
// Euler: Tr(theta^i / f'(theta)) = 0, 0, 1 for both f
assert [ Trace(thetaSplit^i/derivativeAtThetaSplit) : i in [0..2] ] eq [0,0,1];
assert [ Trace(thetaNonsplit^i/derivativeAtThetaNonsplit) : i in [0..2] ] eq [0,0,1];

function secondFormIsTraceForm(pairs, DeltaSets)
     for i in [1..#pairs] do
          theta, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
          u0SeventhPower := genericElement(theta)^7;
          for delta in DeltaSets[i] do
               if PForms(delta, theta)[3]
                  ne traceOfCoefficients((delta/derivativeAtTheta)*u0SeventhPower) then
                    return false;
               end if;
          end for;
     end for;
     return true;
end function;

// P^(2) = Tr(delta u_0^7 / f'(theta)) for every delta of the six sets Delta
assert secondFormIsTraceForm(pairs, DeltaSets);
show("P^(2) for f_sp and delta = f'(theta), the untwisted septic",
     PForms(derivativeAtThetaSplit, thetaSplit)[3]);
verified();

statement("Lemma 3.5", "lem:fermat-twist", "the covering curves are twists of the Fermat septic");
toFormRingOverK := hom< formRingOverQ -> formRingOverK | A0, A1, A2 >;

function diagonalSepticData(pairs, DeltaSets)
     identityHolds := true;
     coefficientsNonzero := true;
     for i in [1..#pairs] do
          theta, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
          u0 := genericElement(theta);
          u1 := applySigmaToCoefficients(u0);
          u2 := applySigmaToCoefficients(u1);
          for delta in DeltaSets[i] do
               eta := delta/derivativeAtTheta;
               identityHolds and:= toFormRingOverK(traceOfCoefficients(eta*u0^7))
                    eq sigmaPower(eta,0)*u0^7 + sigmaPower(eta,1)*u1^7 + sigmaPower(eta,2)*u2^7;
               coefficientsNonzero and:= forall{ i : i in [0..2] | sigmaPower(eta,i) ne 0 };
          end for;
     end for;
     return identityHolds, coefficientsNonzero;
end function;

identityHolds, coefficientsNonzero := diagonalSepticData(pairs, DeltaSets);
// (1): P^(2) = eta u_0^7 + sigma(eta) u_1^7 + sigma^2(eta) u_2^7, for every delta of
// the six sets Delta
assert identityHolds;
// (1): the three coefficients sigma^i(eta) are nonzero, so the septic is smooth, of
// genus (7-1)(7-2)/2 = 15
assert coefficientsNonzero;
show("det(sigma^i(theta)^n)^2 for theta_sp, theta_ns",
     [ Determinant(Matrix(K, 3, 3, [ sigmaPower(th, i)^n : i in [0..2], n in [0..2] ]))^2
       : th in [thetaSplit, thetaNonsplit] ]);
// u_i is a linear change of coordinates over K: det(sigma^i(theta)^n)^2 = disc(f)
function vandermondeSquared(th)
     return Determinant(Matrix(K, 3, 3, [ sigmaPower(th, i)^n : i in [0..2], n in [0..2] ]))^2;
end function;
assert vandermondeSquared(thetaSplit) eq Discriminant(fSplit);
assert vandermondeSquared(thetaNonsplit) eq Discriminant(fNonsplit);
verified();

statement("Lemma 3.6", "lem:one-family", "one family of curves for the six descents");
show("Sigma, an abelian group with invariants", Invariants(Sigma));
// (2): Sigma is F_7^2
assert #Sigma eq 49;
assert Exponent(Sigma) eq 7;
// (2): #Delta = 49 for each of the six pairs
assert forall{ D : D in DeltaSets | #D eq 49 };

// the norm map K(7,S) -> Q_S^*/Q_S^*7 is a homomorphism, recorded by the exponent
// vector modulo 7 (-1 is a seventh power); its image is spanned by the images of
// the generators of K(7,S), so its order is 7^rank
function normImageSize(f, k)
     selmer, toSelmer := selmerGroup(f, k);
     S := badPrimes(f, k);
     images := Matrix(GF(7), [ [ Valuation(Norm(K ! (selmer.i @@ toSelmer)), p) : p in S ]
                                 : i in [1..Ngens(selmer)] ]);
     return 7^Rank(images);
end function;
// (2): the norm map K(7,S) -> Q_S^*/Q_S^*7 is onto a group of order 7^#S
assert forall{ p : p in pairs | normImageSize(p[1], p[2]) eq 7^#badPrimes(p[1], p[2]) };
// (2): f'(theta_sp) is a 7-unit of norm -49
assert Norm(derivativeAtThetaSplit) eq -49;
// (2): f'(theta_ns) = 4 f'(theta_sp)
assert derivativeAtThetaNonsplit eq 4*derivativeAtThetaSplit;

function deltaToSigmaIsBijective(pairs, DeltaSets)
     for i in [1..#pairs] do
          theta, derivativeAtTheta := rootAndDerivative(pairs[i][1]);
          if #{ selmerClassModRationals(delta/derivativeAtTheta) : delta in DeltaSets[i] } ne 49 then
               return false;
          end if;
     end for;
     return true;
end function;
// (2): delta -> [delta / f'(theta)] is a bijection Delta -> Sigma, for all six pairs
assert deltaToSigmaIsBijective(pairs, DeltaSets);

// (3): the six descents give the same 49 classes eta, hence the same septics Tr(eta omega^7) = 0
classesOfPair := [ { selmerClassModRationals((K ! delta)/derivative) : delta in DeltaSets[i] }
                   where _, derivative := rootAndDerivative(pairs[i][1]) : i in [1..#pairs] ];
// (3): the six pairs give the same 49 classes in Sigma
assert #Seqset(classesOfPair) eq 1;
// (3): t_ns = 5 - 2 t_sp, as theta_ns = 5 - 2 theta_sp
assert thetaNonsplit eq 5 - 2*thetaSplit;
verified();

finish("kummer.m");
quit;
