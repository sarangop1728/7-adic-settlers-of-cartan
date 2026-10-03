// theorem-2.m -- the checks of Section 6 of "7-adic Galois representations of
// elliptic curves over the rationals via Kummer descent".
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b theorem-2.m < /dev/null
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
Zmod49  := Integers(49);
GL2mod49 := GL(2, Zmod49);

function matrixMod49(a, b, c, d)
     return GL2mod49 ! [a, b, c, d];
end function;

function teichmullerLift(a)            // the Teichmuller lift of a in F_7^*
     return (Zmod49 ! a)^7;
end function;

leastNonResidueMod7 := 3;

// I + 7V, for a list of matrices spanning V
function kernelGenerators(spanningSet)
     return [ GL2mod49 ! [1 + 7*A[1], 7*A[2], 7*A[3], 1 + 7*A[4]] : A in spanningSet ];
end function;

VSplit    := [ [1,0,0,1], [0,1,0,0], [0,0,1,0] ];      // (a b; c a)
VNonsplit := [ [1,0,0,0], [0,0,0,1],
               [0, leastNonResidueMod7, -1, 0] ];      // (a eps*b; -b d)

// lifts of C^+(7) of order prime to 7
generatorOfF49 := matrixMod49(1, leastNonResidueMod7, 1, 1);   // 1 + sqrt(eps)
GNonsplitSharp := sub< GL2mod49 |
     [ generatorOfF49^49, matrixMod49(1, 0, 0, -1) ] cat kernelGenerators(VNonsplit) >;
GSplitSharp := sub< GL2mod49 |
     [ matrixMod49(teichmullerLift(3), 0, 0, 1),
       matrixMod49(1, 0, 0, teichmullerLift(3)),
       matrixMod49(0, 1, 1, 0) ] cat kernelGenerators(VSplit) >;

statement("Lemma 6.1", "lem:criterion-groups", "the Frobenius criterion on G^#(49)");
function isRegular(g)
     return (ZZ ! Trace(g)) mod 7 ne 0 and (ZZ ! (Trace(g)^2 - 4*Determinant(g))) mod 7 ne 0;
end function;
show("regular elements of G_ns^#(49), of G_sp^#(49)",
     [ #[ g : g in G | isRegular(g) ] : G in [GNonsplitSharp, GSplitSharp] ]);
// the criterion holds on all of G_ns^#(49)
assert forall{ g : g in GNonsplitSharp | not isRegular(g) or IsScalar(g^48) };
// the criterion holds on all of G_sp^#(49)
assert forall{ g : g in GSplitSharp | not isRegular(g) or IsScalar(g^48) };
fullKernelGenerators := kernelGenerators([ [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1] ]);
fullPreimageNonsplit := sub< GL2mod49 | [ generatorOfF49^49, matrixMod49(1,0,0,-1) ] cat fullKernelGenerators >;
fullPreimageSplit := sub< GL2mod49 |
     [ matrixMod49(teichmullerLift(3), 0, 0, 1), matrixMod49(1, 0, 0, teichmullerLift(3)),
       matrixMod49(0, 1, 1, 0) ] cat fullKernelGenerators >;
// it is not vacuous: it fails on 6/7 of the regular elements of the full preimage of C_ns^+(7)
regular := [ g : g in fullPreimageNonsplit | isRegular(g) ];
assert 7*#[ g : g in regular | not IsScalar(g^48) ] eq 6*#regular;
// and on 6/7 of the regular elements of the full preimage of C_sp^+(7), of order 72 * 7^4
assert #fullPreimageSplit eq 72*7^4;
regular := [ g : g in fullPreimageSplit | isRegular(g) ];
assert 7*#[ g : g in regular | not IsScalar(g^48) ] eq 6*#regular;
verified();

TSplit    := thueSolutions(fSplit, [1, -1, 7, -7]);
TNonsplit := thueSolutions(fNonsplit, [1, -1, 8, -8, 7, -7, 56, -56]);

statement("Section 6.2", "candidates-T", "the set T of candidates");
show("T in the split model, (x,y) with F_sp(x,y) = +-1, +-7", Sort(Setseq(TSplit)));
show("T in the nonsplit model, (x,y) with F_ns(x,y) = +-1, +-8, +-7, +-56", Sort(Setseq(TNonsplit)));
// 12 primitive solutions of F_sp = +-1, +-7 and of F_ns = +-1, +-8, +-7, +-56
assert #TSplit eq 12;
assert #TNonsplit eq 12;
// the substitution (x,y) -> (x - 5y, -2y) matches the two sets
assert { primitivePairOfGamma(gammaOfPair(pair, thetaNonsplit, derivativeAtThetaNonsplit),
                              thetaSplit, derivativeAtThetaSplit) : pair in TNonsplit } eq TSplit;
// T_ns is Kenku's list: t = 0, oo, 1, -1, 2, 3, 5, -3/5, 7, 7/3, 11/2, 19/9
assert TNonsplit eq { [0,1],[1,0],[1,1],[-1,1],[2,1],[3,1],[5,1],[-3,5],[7,1],[7,3],[11,2],[19,9] };
verified();

statement("Table 4, Corollary 6.2", "tab:candidates", "the candidates and the criterion");
// first prime p < 100 of good reduction at which the criterion fails, with a_p
function firstCriterionFailure(j)
     curve := MinimalModel(EllipticCurveFromjInvariant(j));
     discriminant := ZZ ! Discriminant(curve);
     for p in PrimesUpTo(100) do
          if p eq 7 or discriminant mod p eq 0 then continue; end if;
          ap := TraceOfFrobenius(curve, p);
          if ap mod 7 eq 0 or (ap^2 - 4*p) mod 7 eq 0 then continue; end if;
          if not IsScalar(Matrix(Zmod49, 2, 2, [0, -p, 1, ap])^48) then
               return <p, ap>;
          end if;
     end for;
     return <0, 0>;
end function;

procedure reportCandidates(name, jMap, points)
     printf "  candidates on %o\n", name;
     for pair in Sort(Setseq(points)) do
          if name eq "X_sp^+(7)" and pair[2] eq 0 then
               printf "    t = oo: cusp\n";
               continue;
          end if;
          j := jMap(pair[1], pair[2]);
          failure := (j eq 0 or j eq 1728) select <0,0> else firstCriterionFailure(j);
          printf "    t = %o: CM discriminant %o, j = %o, criterion fails at (p, a_p) = %o\n",
                 pair[2] eq 0 select "oo" else Sprint(pair[1]/pair[2]), cmDiscriminant(j), factored(j),
                 failure[1] eq 0 select "-" else tupleString([failure[1], failure[2]]);
     end for;
end procedure;
reportCandidates("X_ns^+(7)", jNonsplit, TNonsplit);
reportCandidates("X_sp^+(7)", jSplit, TSplit);

function everyNonCMCandidateViolates(jMap, points, isSplit)
     for pair in points do
          if isSplit and pair[2] eq 0 then continue; end if;
          j := jMap(pair[1], pair[2]);
          if j eq 0 or j eq 1728 then continue; end if;
          if firstCriterionFailure(j)[1] eq 0 then return false; end if;
     end for;
     return true;
end function;
// every candidate with j not in {0, 1728} violates the criterion at some p < 100
assert everyNonCMCandidateViolates(jNonsplit, TNonsplit, false);
assert everyNonCMCandidateViolates(jSplit, TSplit, true);

paperTable := [
     < "ns", [7,1],   2^3*5^3*7^5,                                        <3,1>   >,
     < "ns", [7,3],   2^15*7^5,                                           <3,2>   >,
     < "sp", [5,2],   3^3*5*7^5/2^7,                                      <11,2>  >,
     < "sp", [4,3],   -2^8*5^3*7^5*37^3/3^7,                              <13,2>  >,
     < "sp", [3,2],   3*5^3*11^3*17^3*43^3/2^7,                           <23,4>  >,
     < "sp", [-1,4],  3^3*37^3*149^3*2389^3/2^14,                         <5,1>   >,
     < "sp", [13,9],  -2^18*5^3*11^3*13*29^3*37^3*67^3*127^3/3^14,        <17,3>  >,
     < "sp", [14,5],  2^4*3^3*7^4*19^3*23^3*43^3*163^3/5^7,               <31,10> >,
     < "ns", [11,2],  2^6*11^3*23^3*149^3*269^3,                          <3,1>   >,
     < "ns", [19,9],  2^9*17^6*19^3*29^3*149^3,                           <3,2>   >,
     < "sp", [1,1],   -2^15*3^3,                                          <5,1>   >,
     < "sp", [2,1],   2^4*3^3*5^3,                                        <13,2>  >,
     < "sp", [3,1],   -2^15*3*5^3,                                        <13,5>  > ];

function paperTableHolds(rows)
     for row in rows do
          j := row[1] eq "ns" select jNonsplit(row[2][1], row[2][2]) else jSplit(row[2][1], row[2][2]);
          failure := firstCriterionFailure(j);
          if not (j eq row[3] and failure[1] eq row[4][1] and Abs(failure[2]) eq row[4][2]) then
               return false;
          end if;
     end for;
     return true;
end function;
// Table 4: the j-invariants and (p, |a_p|)
assert paperTableHolds(paperTable);
// in every row j is p-integral and not 0 or 1728 mod p, so some quadratic twist has
// good reduction at p
for row in paperTable do
     jInvariant, prime := Explode(<row[3], row[4][1]>);
     assert Valuation(jInvariant, prime) ge 0;
     assert (GF(prime) ! jInvariant) notin { GF(prime) ! 0, GF(prime) ! 1728 };
end for;
// the displayed instance: t = 5/2 has a_11 = +-2
assert Abs(TraceOfFrobenius(MinimalModel(EllipticCurveFromjInvariant(jSplit(5,2))), 11)) eq 2;
// and (0 -11; 1 2)^48 = (43 42; 14 22) mod 49, which is not scalar
frobenius48 := Matrix(Zmod49, 2, 2, [0, -11, 1, 2])^48;
assert frobenius48 eq Matrix(Zmod49, 2, 2, [43, 42, 14, 22]);
assert not IsScalar(frobenius48);
verified();

statement("Theorem 2", "thm:modular-curves", "the CM points");
rationalCMjInvariants := [ 0, 1728, -3375, 8000, -32768, 54000, 287496, -12288000, 16581375,
                           -884736, -884736000, -147197952000, -262537412640768000 ];
show("rational CM j-invariants divisible by 7", [ j : j in rationalCMjInvariants | j mod 7 eq 0 ]);
// the thirteen rational CM j-invariants
assert forall{ j : j in rationalCMjInvariants | cmDiscriminant(j) ne 0 };
// only 0 is divisible by 7
assert [ j : j in rationalCMjInvariants | j mod 7 eq 0 ] eq [ 0 ];
// j = 1728: a_5(y^2 = x^3 - x) = -2
assert TraceOfFrobenius(EllipticCurve([0,0,0,-1,0]), 5) eq -2;
// for a_5 in {2, 4} the criterion fails at p = 5
for a in [2, 4] do
     assert (a*(a^2 - 20)) mod 7 ne 0;
     assert not IsScalar(Matrix(Integers(49), 2, 2, [0, -5, 1, a])^48);
end for;
rationalFunctionField<tt> := FunctionField(QQ);
show("degrees of the factors of the numerator of j_sp(t) - 1728",
     [ Degree(factor[1]) : factor in Factorization(Numerator(jSplit(tt, 1) - 1728)) ]);
// j_sp(t) = 1728 has no rational solution: the numerator is a product of four
// irreducible quartics
assert [ Degree(factor[1]) : factor in Factorization(Numerator(jSplit(tt, 1) - 1728)) ] eq [4,4,4,4];
verified();

finish("theorem-2.m");
quit;
