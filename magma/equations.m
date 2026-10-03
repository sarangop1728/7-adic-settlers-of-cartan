// equations.m -- the checks of Sections 1 and 2 of "7-adic Galois representations
// of elliptic curves over the rationals via Kummer descent".
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b equations.m < /dev/null
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

statement("(1.4), (1.5)", "eq:thetas", "the field K, the roots theta, and sigma");
show("theta_sp", "1 - (zeta + zeta^-1), a root of " cat Sprint(fSplit));
show("theta_ns", "3 + 2(zeta + zeta^-1) = 5 - 2 theta_sp, a root of " cat Sprint(fNonsplit));
show("sigma(theta_sp)", sigma(theta));
show("class number of K", ClassNumber(K));
show("disc(f_sp), disc(f_ns), disc(O_K)",
     joined([ factored(Discriminant(fSplit)), factored(Discriminant(fNonsplit)),
              factored(Discriminant(OK)) ], ", "));
// theta_ns = 5 - 2 theta_sp is a root of f_ns
assert Evaluate(fNonsplit, thetaNonsplit) eq 0;
// theta_sp = 1 - (zeta + zeta^-1)
assert embedInCyclotomic(thetaSplit) eq 1 - zetaTrace(1);
// theta_ns = 3 + 2 (zeta + zeta^-1)
assert embedInCyclotomic(thetaNonsplit) eq 3 + 2*zetaTrace(1);
// sigma is induced by zeta -> zeta^2
assert embedInCyclotomic(sigma(theta)) eq 1 - zetaTrace(2);
// sigma(theta_sp) = -theta_sp^2 + 2 theta_sp + 2
assert sigma(theta) eq -theta^2 + 2*theta + 2;
// sigma has order 3
assert sigma(theta) ne theta;
assert sigma(sigma(sigma(theta))) eq theta;
// K has class number one
assert ClassNumber(K) eq 1;
// disc(f_sp) = 7^2 = disc(O_K), so O_K = Z[theta_sp]
assert Discriminant(fSplit) eq 49;
assert Discriminant(OK) eq 49;
// disc(f_ns) = 2^6 7^2, so [O_K : Z[theta_ns]] = 8
assert Discriminant(fNonsplit) eq 2^6*7^2;
// 2 is inert in K: one prime, unramified, of degree 3
factorizationOf2 := Factorization(2*OK);
assert #factorizationOf2 eq 1;
assert factorizationOf2[1][2] eq 1;
assert Degree(factorizationOf2[1][1]) eq 3;
// 7 is totally ramified in K
assert #factorizationOf7 eq 1;
assert factorizationOf7[1][2] eq 3;
// (1.5): f_ns'(theta_ns) = 4 f_sp'(theta_sp)
assert derivativeAtThetaNonsplit eq 4*derivativeAtThetaSplit;
// (1.5): Norm(f_sp'(theta_sp)) = -disc(f_sp) = -7^2
assert Norm(derivativeAtThetaSplit) eq -49;
verified();

statement("(2.1), (2.2)", "eq:jns", "the j-maps of Zywina's models");
show("CM discriminants of j_ns at t = oo, 0, 1, -1, 2, 3, 5, -3/5",
     [ cmDiscriminant(jNonsplit(pair[1], pair[2]))
       : pair in [[1,0],[0,1],[1,1],[-1,1],[2,1],[3,1],[5,1],[-3,5]] ]);
show("CM discriminants of j_sp at t = 0, -1, 1, 2, 3",
     [ cmDiscriminant(jSplit(pair[1], pair[2])) : pair in [[0,1],[-1,1],[1,1],[2,1],[3,1]] ]);
// CM values of j_ns
assert [ cmDiscriminant(jNonsplit(pair[1], pair[2]))
         : pair in [[1,0],[0,1],[1,1],[-1,1],[2,1],[3,1],[5,1],[-3,5]] ]
       eq [ -8, -3, -11, -16, -67, -4, -43, -163 ];
// CM values of j_sp
assert [ cmDiscriminant(jSplit(pair[1], pair[2])) : pair in [[0,1],[-1,1],[1,1],[2,1],[3,1]] ]
       eq [ -3, -3, -19, -12, -27 ];
jFunctionNonsplit := Evaluate(HNonsplit, [t, 1])^3/Evaluate(FNonsplit, [t, 1])^7;
jFunctionSplit := t*Evaluate(HSplit, [t, 1])^3/Evaluate(FSplit, [t, 1])^7;
// j_ns has degree 21 and j_sp has degree 28
assert Max(Degree(Numerator(jFunctionNonsplit)), Degree(Denominator(jFunctionNonsplit))) eq 21;
assert Max(Degree(Numerator(jFunctionSplit)), Degree(Denominator(jFunctionSplit))) eq 28;
// the poles of j_sp: order 7 at the roots of f_sp and at oo
assert Denominator(jFunctionSplit) eq fSplit^7;
assert Degree(Numerator(jFunctionSplit)) - Degree(Denominator(jFunctionSplit)) eq 7;
verified();

statement("Lemma 2.1", "lem:arithmetic-of-forms", "the arithmetic of the forms");
resultantNonsplit := Resultant(FNonsplit, HNonsplit, x);
resultantSplit := Resultant(FSplit, HSplit, x);
show("Res_x(F_ns, H_ns)", factored(Coefficients(resultantNonsplit)[1]) cat " * y^" cat Sprint(TotalDegree(resultantNonsplit)));
show("Res_x(F_sp, H_sp)", factored(Coefficients(resultantSplit)[1]) cat " * y^" cat Sprint(TotalDegree(resultantSplit)));
// F_ns, F_sp are the norm forms of x - theta y (on a sample of pairs)
samplePairs := [[1,0],[0,1],[1,1],[2,-3],[5,7]];
assert forall{ pair : pair in samplePairs | Norm(pair[1] - thetaNonsplit*pair[2]) eq Evaluate(FNonsplit, pair) };
assert forall{ pair : pair in samplePairs | Norm(pair[1] - thetaSplit*pair[2]) eq Evaluate(FSplit, pair) };

// (1): Res_x(F_ns, H_ns) = +-2^21 7^7 y^21
assert resultantNonsplit in { 2^21*7^7*y^21, -2^21*7^7*y^21 };
// (1): Res_x(F_sp, H_sp) = +-7^7 y^27
assert resultantSplit in { 7^7*y^27, -7^7*y^27 };
// (1): both forms F are x^3 mod y
assert Evaluate(FSplit, [x, 0]) eq x^3;
assert Evaluate(FNonsplit, [x, 0]) eq x^3;
// (1): H_sp = x^9 mod y
assert Evaluate(HSplit, [x, 0]) eq x^9;
// (1): F_sp = y^3 mod x
assert Evaluate(FSplit, [0, y]) eq y^3;

// (2) and (3): F mod 7, 49, 2, 8, 16 on primitive pairs
function primitiveZerosModulo(F, modulus)
     return [ [a,b] : a, b in [0..modulus-1] |
              GCD([a,b,modulus]) eq 1 and Evaluate(F, [a,b]) mod modulus eq 0 ];
end function;

show("primitive zeros of F_ns mod 7", primitiveZerosModulo(FNonsplit, 7));
show("primitive zeros of F_sp mod 7", primitiveZerosModulo(FSplit, 7));
// (2): F_ns = 0 and F_sp = 0 mod 49 have no primitive solutions
assert #primitiveZerosModulo(FNonsplit, 49) eq 0;
assert #primitiveZerosModulo(FSplit, 49) eq 0;
// (2a): 7 | F_ns iff 7 | x
assert forall{ pair : pair in primitiveZerosModulo(FNonsplit, 7) | pair[1] eq 0 };
// (2b): 7 | F_sp iff 7 | x + y
assert forall{ pair : pair in primitiveZerosModulo(FSplit, 7) | (pair[1] + pair[2]) mod 7 eq 0 };
// (3): F_ns = 0 mod 16 has no primitive solutions, and F_ns = 0 mod 8 does
assert #primitiveZerosModulo(FNonsplit, 16) eq 0;
assert #primitiveZerosModulo(FNonsplit, 8) gt 0;
// (3): F_ns is even only for x, y odd, and then 8 | F_ns
assert forall{ pair : pair in primitiveZerosModulo(FNonsplit, 2) | IsOdd(pair[1]) and IsOdd(pair[2]) };
oddPairsMod8 := [ [a,b] : a, b in [0..7] | IsOdd(a) and IsOdd(b) ];
assert forall{ pair : pair in oddPairsMod8 | Evaluate(FNonsplit, pair) mod 8 eq 0 };
// (3): F_sp is odd on primitive pairs
assert #primitiveZerosModulo(FSplit, 2) eq 0;

// (4): F_ns(x,y) = F_sp(x - 5y, -2y)
assert FNonsplit eq Evaluate(FSplit, [x - 5*y, -2*y]);
verified();

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

statement("Lemma 2.2", "lem:groups", "the groups G^#(49)");
show("#G_ns^#(49), index in GL_2(Z/49)", [ #GNonsplitSharp, Index(GL2mod49, GNonsplitSharp) ]);
show("#G_sp^#(49), index in GL_2(Z/49)", [ #GSplitSharp, Index(GL2mod49, GSplitSharp) ]);
// 1 + sqrt(3) generates F_49^*
assert Order(GL(2, GF(7)) ! [1, leastNonResidueMod7, 1, 1]) eq 48;
// #G_ns^# = 2 * 7^3 * 48, of index 147
assert #GNonsplitSharp eq 2*7^3*48;
assert Index(GL2mod49, GNonsplitSharp) eq 147;
// #G_sp^# = 2 * 7^3 * 36, of index 196
assert #GSplitSharp eq 2*7^3*36;
assert Index(GL2mod49, GSplitSharp) eq 196;
// -I lies in both groups
minusIdentity := GL2mod49 ! [-1,0,0,-1];
assert minusIdentity in GNonsplitSharp;
assert minusIdentity in GSplitSharp;
// det is surjective on both groups
function determinantImage(G)
     return sub< GL(1, Zmod49) | [ GL(1, Zmod49) ! [Determinant(g)] : g in Generators(G) ] >;
end function;
assert #determinantImage(GNonsplitSharp) eq 42;
assert #determinantImage(GSplitSharp) eq 42;
// both reduce onto C^+(7), of orders 2*48 and 2*36, so (by the orders above) they meet
// the kernel of reduction in a group of order 7^3, which is I + 7V
function reductionMod7(G)
     return sub< GL(2, GF(7)) | [ GL(2, GF(7)) ! ChangeRing(Matrix(g), GF(7)) : g in Generators(G) ] >;
end function;
assert #reductionMod7(GNonsplitSharp) eq 2*48;
assert #reductionMod7(GSplitSharp) eq 2*36;
verified();

statement("Lemma 2.4", "lem:nilpotents", "nilpotent matrices in V");
F7 := GF(7);
function liesInV(matrix, whichCartan)
     if whichCartan eq "sp" then
          return matrix[1][1] eq matrix[2][2];                           // (a b; c a)
     end if;
     return matrix[1][2] eq -leastNonResidueMod7*matrix[2][1];          // (a eps*b; -b d)
end function;
nilpotents := [ m : m in MatrixAlgebra(F7, 2) | m ne 0 and m^2 eq 0 ];
show("nonzero nilpotent matrices of M_2(F_7)", #nilpotents);
show("of which in V_sp, in V_ns", [ #[ m : m in nilpotents | liesInV(m, "sp") ],
                                   #[ m : m in nilpotents | liesInV(m, "ns") ] ]);
// the nilpotents of V_sp are the nonzero multiples of E_12 and E_21
assert { m : m in nilpotents | liesInV(m, "sp") } eq
       { a*Matrix(F7, 2, 2, [0,1,0,0]) : a in F7 | a ne 0 }
       join { a*Matrix(F7, 2, 2, [0,0,1,0]) : a in F7 | a ne 0 };
// V_ns contains no nonzero nilpotent matrix
assert forall{ m : m in nilpotents | not liesInV(m, "ns") };
verified();

statement("Lemma 2.5", "lem:cusp-reduction", "the rational cusp of X_sp^+(7)");
planeMod7 := VectorSpace(GF(7), 2);
linesMod7 := [ sub< planeMod7 | planeMod7 ! vec > : vec in [ [1,0] ] cat [ [a,1] : a in [0..6] ] ];
pairsOfLines := { {L1, L2} : L1, L2 in linesMod7 | L1 ne L2 };
unipotentGroup := [ Matrix(GF(7), 2, 2, [e, e*b, 0, e]) : b in [0..6], e in [1,-1] ];
// g acts on column vectors; on the row vector spanning a line this is vec -> vec g^T
function moveLine(g, L)
     return sub< planeMod7 | Basis(L)[1]*Transpose(g) >;
end function;
cuspOrbits := {};
remainingPairs := pairsOfLines;
while #remainingPairs gt 0 do
     pair := Rep(remainingPairs);
     orbit := { { moveLine(g, L) : L in pair } : g in unipotentGroup };
     Include(~cuspOrbits, orbit);
     remainingPairs diff:= orbit;
end while;
show("unordered pairs of lines, cusps, orbit sizes",
     [* #pairsOfLines, #cuspOrbits, [ #orbit : orbit in cuspOrbits ] *]);
// the cusps of X_sp^+(7): four orbits of seven unordered pairs of lines
assert #pairsOfLines eq 28;
assert #cuspOrbits eq 4;
assert forall{ orbit : orbit in cuspOrbits | #orbit eq 7 };
muOrbit := { pair : pair in pairsOfLines | linesMod7[1] in pair };
// the seven pairs containing the line mu_7 form one orbit
assert muOrbit in cuspOrbits;
// Galois acts on the cusps through the cyclotomic character, by diag(d, 1)
cyclotomicMatrices := [ Matrix(GF(7), 2, 2, [d, 0, 0, 1]) : d in [1..6] ];
function moveOrbit(g, orbit)
     return { { moveLine(g, L) : L in pair } : pair in orbit };
end function;
otherCusps := cuspOrbits diff { muOrbit };
// diag(d,1) fixes the mu_7 orbit
assert forall{ g : g in cyclotomicMatrices | moveOrbit(g, muOrbit) eq muOrbit };
// and permutes the other three cusps transitively
assert forall{ g : g in cyclotomicMatrices | forall{ o : o in otherCusps | moveOrbit(g, o) in otherCusps } };
assert #{ moveOrbit(g, Rep(otherCusps)) : g in cyclotomicMatrices } eq 3;
verified();

statement("Remark 2.7", "rem:FL-split", "the cusp widths of X^#(49)");
function cuspWidths(G)
     action := CosetAction(GL2mod49, G);
     return Sort([ #orbit : orbit in Orbits(sub< Codomain(action) | action(GL2mod49 ! [1,1,0,1]) >) ]);
end function;
show("cusp widths of X_ns^#(49)", cuspWidths(GNonsplitSharp));
show("cusp widths of X_sp^#(49)", cuspWidths(GSplitSharp));
// cusp widths of X_ns^#(49): 49, 49, 49
assert cuspWidths(GNonsplitSharp) eq [49, 49, 49];
// cusp widths of X_sp^#(49): 7 (seven times), 49, 49, 49
assert cuspWidths(GSplitSharp) eq [7,7,7,7,7,7,7,49,49,49];
verified();

finish("equations.m");
quit;
