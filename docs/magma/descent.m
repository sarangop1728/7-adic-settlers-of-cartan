// descent.m -- the Kummer descent of "7-adic Galois representations of elliptic
// curves over the rationals via Kummer descent", run from the Selmer sets to Table 1.
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b descent.m < /dev/null
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
alpha := theta^2 - 5*theta + 1;
TSplit    := thueSolutions(fSplit, [1, -1, 7, -7]);
TNonsplit := thueSolutions(fNonsplit, [1, -1, 8, -8, 7, -7, 56, -56]);

statement("Step 1", "descent-selmer", "the Selmer sets of the six pairs (F,k)");
curveOfPair := [ "X_ns^+(49)", "X_ns^+(49)", "X_ns^#(49)", "X_ns^#(49)", "X_sp^#(49)", "X_sp^#(49)" ];
printf "  %-11o %-4o %-4o %-7o %-9o %-7o %o\n", "curve", "F", "k", "S", "#K(7,S)", "#Delta", "#{[delta/f'(theta)]}";
classesOfPair := [];
for i in [1..#pairs] do
     f, k := Explode(pairs[i]);
     _, derivative := rootAndDerivative(f);
     classes := { selmerClassModRationals((K ! delta)/derivative) : delta in DeltaSets[i] };
     Append(~classesOfPair, classes);
     printf "  %-11o %-4o %-4o %-7o %-9o %-7o %o\n", curveOfPair[i], f eq fSplit select "F_sp" else "F_ns",
            k, Sprint(badPrimes(f, k)), factored(#selmerGroup(f, k)), #DeltaSets[i], #classes;
end for;
// #Delta = 49 for the six pairs
assert forall{ D : D in DeltaSets | #D eq 49 };
// delta -> [delta/f'(theta)] is a bijection onto Sigma
assert #Sigma eq 49;
assert forall{ c : c in classesOfPair | #c eq 49 };
// the same 49 classes for the six pairs
assert #Seqset(classesOfPair) eq 1;
// the classes of epsilon1^i epsilon2^j, 0 <= i, j <= 6, are the 49 classes of Sigma
assert #{ selmerClass(epsilon1^i*epsilon2^j) : i, j in [0..6] } eq 49;
verified();

statement("Step 2", "descent-sieve", "the local sieve on the 49 twists C_eta");
// coordinates (s,c) in Sigma = Sigma_2 + Sigma_4, in the basis [epsilon1 epsilon2^2], [epsilon1 epsilon2^4]
coordinatesInSigma := AssociativeArray();
for s, c in [0..6] do
     coordinatesInSigma[selmerClass(epsilon1^s*epsilon2^(2*s)*(epsilon1*epsilon2^4)^c)] := [s, c];
end for;

function twistForm(eta)
     return traceOfCoefficients(eta*genericElement(thetaSplit)^7);       // C_eta : Tr(eta omega^7) = 0
end function;

survivors := [];             // < eta, [i,j], rational points >
sieved := [];                // < eta, [i,j], the prime p with no Q_p-point >
printf "  %-7o %-7o %-6o %o\n", "(i,j)", "(s,c)", "kappa", "C_eta";
for i, j in [0..6] do
     eta := epsilon1^i*epsilon2^j;
     curve := Curve(projectivePlane, twistForm(eta));
     points := [ Eltseq(P) : P in PointSearch(curve, 100) ];
     if #points gt 0 then
          Append(~survivors, < eta, [i,j], points >);
          verdict := "rational point " cat pointString(points[1]);
     else
          primes := [ p : p in PrimesUpTo(19) | not IsLocallySolvable(curve, p) ];
          error if #primes eq 0, "a twist with no point found and no local obstruction below 20:", [i,j];
          Append(~sieved, < eta, [i,j], primes[1] >);
          verdict := "no Q_p-point for p = " cat Sprint(primes[1]);
     end if;
     printf "  %-7o %-7o %-6o %o\n", tupleString([i,j]), tupleString(coordinatesInSigma[selmerClass(eta)]),
            Sprint(kappa(eta)), verdict;
end for;
show("twists with no Q_p-point for some p < 20", #sieved);
show("twists with a rational point", #survivors);
show("primes that do the sieving", { s[3] : s in sieved });
// 40 twists are discarded by the local sieve, and 9 have rational points
assert #sieved eq 40;
assert #survivors eq 9;
// kappa(eta) = 4c for each of the 49 classes
units := [ epsilon1^i*epsilon2^j : i, j in [0..6] ];
assert forall{ eta : eta in units | kappa(eta) eq 4*coordinatesInSigma[selmerClass(eta)][2] };
verified();

statement("Step 3", "descent-twelve", "the rational points on the surviving twists");
twelvePoints := {};          // < (x,y) in the split model, the class (s,c) >
for survivor in survivors do
     eta, exponents, points := Explode(survivor);
     for P in points do
          omega := &+[ P[n+1]*thetaSplit^n : n in [0..2] ];
          gamma := eta*omega^7;
          // a point of C_eta gives gamma of trace zero
          assert Trace(gamma) eq 0;
          Include(~twelvePoints, < primitivePairOfGamma(gamma, thetaSplit, derivativeAtThetaSplit),
                                   coordinatesInSigma[selmerClass(eta)] >);
     end for;
end for;
twelvePoints := Sort(Setseq(twelvePoints));

function asSolution(pair, F)
     // (x,y,w) with F(x,y) = k w^7, k > 0, w = +-1, and x > 0 (or x = 0, y > 0)
     if pair[1] lt 0 or (pair[1] eq 0 and pair[2] lt 0) then pair := [-pair[1], -pair[2]]; end if;
     value := Evaluate(F, pair);
     return < pair[1], pair[2], Sign(value) >, Abs(value);
end function;

printf "  %-12o %-6o %-13o %-12o %-6o %-13o %o\n",
       "(x,y)_sp", "k_sp", "(x,y,w)_sp", "(x,y)_ns", "k_ns", "(x,y,w)_ns", "(s,c)";
for point in twelvePoints do
     pairSplit, sc := Explode(point);
     gamma := gammaOfPair(pairSplit, thetaSplit, derivativeAtThetaSplit);
     pairNonsplit := primitivePairOfGamma(gamma, thetaNonsplit, derivativeAtThetaNonsplit);
     solutionSplit, kSplit := asSolution(pairSplit, FSplit);
     solutionNonsplit, kNonsplit := asSolution(pairNonsplit, FNonsplit);
     printf "  %-12o %-6o %-13o %-12o %-6o %-13o %o\n", tupleString(pairSplit), kSplit, tupleString(solutionSplit),
            tupleString(pairNonsplit), kNonsplit, tupleString(solutionNonsplit), tupleString(sc);
end for;
pairsFound := { point[1] : point in twelvePoints };
// twelve pairs (x,y), one class each
assert #pairsFound eq 12;
assert #twelvePoints eq 12;
// they are the set T: the primitive solutions of F_sp = +-1, +-7 (Magma's Thue solver)
assert pairsFound eq TSplit;
// each surviving twist carries at least one of them
assert #{ point[2] : point in twelvePoints } eq 9;
verified();

statement("Step 4", "descent-seven", "the pairs with 7 | k: the kappa step, the Klein quartic, Table 1");
// Proposition 5.3(1), a finite check modulo 49
primitivePairsMod49 := [ [a,b] : a, b in [0..48] | GCD([a,b,7]) eq 1 ];
// Proposition 5.3: 7 | F(x,y) implies kappa((x - theta y)/f'(theta)) = 0, both models
assert forall{ pair : pair in primitivePairsMod49 | Evaluate(FSplit, pair) mod 7 ne 0 or
               kappa(gammaOfPair(pair, thetaSplit, derivativeAtThetaSplit)) eq 0 };
assert forall{ pair : pair in primitivePairsMod49 | Evaluate(FNonsplit, pair) mod 7 ne 0 or
               kappa(gammaOfPair(pair, thetaNonsplit, derivativeAtThetaNonsplit)) eq 0 };
show("kappa on the nine surviving twists, by (i,j)",
     joined([ tupleString(s[2]) cat ": " cat Sprint(kappa(s[1])) : s in survivors ], ", "));
kleinClasses := { selmerClass(s[1]) : s in survivors | kappa(s[1]) eq 0 };
show("surviving twists with kappa = 0", #kleinClasses);

// the rational points of the Klein quartic, recomputed (Lemma 4.5)
kleinRing<v0, v1, v2> := PolynomialRing(QQ, 3);
kleinQuartic := Curve(ProjectiveSpace(kleinRing), v0^3*v1 + v1^3*v2 + v2^3*v0);
cyclicPermutation := iso< kleinQuartic -> kleinQuartic | [v1, v2, v0], [v2, v0, v1] >;
cyclicGroup := AutomorphismGroup(kleinQuartic, [cyclicPermutation]);
quotientCurve, toQuotient := CurveQuotient(cyclicGroup);
ellipticQuotient, quotientToElliptic := EllipticCurve(quotientCurve, toQuotient(kleinQuartic ! [1,0,0]));
minimalModel := MinimalModel(ellipticQuotient);
mordellWeil, fromMordellWeil := MordellWeilGroup(ellipticQuotient);
kleinPoints := {@ @};
for element in mordellWeil do
     fiber := (fromMordellWeil(element) @@ quotientToElliptic) @@ toQuotient;
     kleinPoints join:= {@ kleinQuartic ! Eltseq(pt) : pt in RationalPoints(fiber) @};
end for;
show("rational points of the Klein quartic", joined([ pointString(Eltseq(pt)) : pt in kleinPoints ], ", "));
// the Klein quartic has exactly three rational points
assert { Eltseq(pt) : pt in kleinPoints } eq { [1,0,0], [0,1,0], [0,0,1] };

// they are [alpha], [sigma alpha], [sigma^2 alpha] on Z_0 (Corollary 4.7), and gamma = v^3 sigma(v)
certificates := [ sigmaPower(alpha^3*sigma(alpha), i) : i in [0..2] ];
// the classes of the certificates sigma^i(alpha^3 sigma(alpha)) are the three
// surviving twists with kappa = 0
assert { selmerClassModRationals(gamma) : gamma in certificates } eq kleinClasses;

tableOne := [];
for model in [ <"F_ns", thetaNonsplit, derivativeAtThetaNonsplit, FNonsplit, jNonsplit>,
               <"F_sp", thetaSplit, derivativeAtThetaSplit, FSplit, jSplit> ] do
     name, th, derivative, F, jMap := Explode(model);
     for gamma in certificates do
          solution, k := asSolution(primitivePairOfGamma(gamma, th, derivative), F);
          j := jMap(solution[1], solution[2]);
          Append(~tableOne, < name, k, solution, solution[1]/solution[2],
                              j eq 0 select "0" else (cmDiscriminant(j) eq 0 select "non-CM" else "CM") >);
     end for;
end for;
tableOne := Sort(tableOne, func< a, b | a[1] ne b[1] select (a[1] lt b[1] select -1 else 1) else a[2] - b[2] >);
printf "\n  Table 1\n";
printf "  %-11o %-13o %-8o %o\n", "(F,k)", "(x,y,w)", "t = x/y", "j(t)";
for row in tableOne do
     printf "  %-11o +-%-12o %-8o %o\n", "(" cat row[1] cat "," cat Sprint(row[2]) cat ")",
            tupleString(row[3]), Sprint(row[4]), row[5];
end for;
// Table 1 of the paper: the six solutions (x,y,w) of F(x,y) = k w^7
assert { <row[1], row[2], row[3]> : row in tableOne } eq
       { <"F_ns", 7, <0,1,1>>, <"F_ns", 56, <7,1,1>>, <"F_ns", 56, <7,3,-1>>,
         <"F_sp", 7, <1,-1,1>>, <"F_sp", 7, <5,2,-1>>, <"F_sp", 7, <4,3,1>> };
// j = 0 at t = 0 and t = -1
assert [ row[5] : row in tableOne | row[4] in {0, -1} ] eq [ "0", "0" ];
// no CM at the other four
assert forall{ row : row in tableOne | row[4] in {0, -1} or row[5] eq "non-CM" };
verified();

statement("Step 5", "descent-other", "the pairs with 7 not dividing k (complete by Furio-Lombardo)");
for model in [ <"F_ns", [1, 8], thetaNonsplit, derivativeAtThetaNonsplit, FNonsplit>,
               <"F_sp", [1], thetaSplit, derivativeAtThetaSplit, FSplit> ] do
     name, ks, th, derivative, F := Explode(model);
     for k in ks do
          solutions := Sort([ s : s in { asSolution(primitivePairOfGamma(
                                gammaOfPair(point[1], thetaSplit, derivativeAtThetaSplit), th, derivative), F)
                              : point in twelvePoints } | Abs(Evaluate(F, [s[1], s[2]])) eq k ]);
          printf "  (%o,%o): (x,y,w) = %o\n", name, k, joined([ "+-" cat tupleString(s) : s in solutions ], ", ");
     end for;
end for;
// the twelve points split as 3 + 6 + 1 + 2 over k = 1, 8, 7, 56 for F_ns
assert [ #{ p : p in TNonsplit | Abs(Evaluate(FNonsplit, p)) eq k } : k in [1, 8, 7, 56] ] eq [3, 6, 1, 2];
// and as 9 + 3 over k = 1, 7 for F_sp
assert [ #{ p : p in TSplit | Abs(Evaluate(FSplit, p)) eq k } : k in [1, 7] ] eq [9, 3];
verified();

finish("descent.m");
quit;
