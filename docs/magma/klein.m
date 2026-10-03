// klein.m -- the checks of Section 4 of "7-adic Galois representations of
// elliptic curves over the rationals via Kummer descent".
// Tangled from 7-adic-settlers-of-cartan.org.  Run with:  magma -b klein.m < /dev/null
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

statement("Lemma 4.1", "lem:quotient-map", "the quotient map psi");
function psi(u)
     return u^3*applySigmaToCoefficients(applySigmaToCoefficients(u));    // sigma^2 = sigma^-1
end function;

for theta in [thetaSplit, thetaNonsplit] do
     u0 := genericElement(theta);
     u1 := applySigmaToCoefficients(u0);
     u2 := applySigmaToCoefficients(u1);
     // psi(u_0)^3 sigma(psi(u_0)) = (u_0 u_1 u_2)^3 u_0^7
     assert psi(u0)^3*applySigmaToCoefficients(psi(u0)) eq (u0*u1*u2)^3*u0^7;
end for;

// the forms: Q^(n) o psi = (u0 u1 u2)^3 P^(n), for delta = 2 - theta (any delta would do)
delta := 2 - theta;
u0 := genericElement(theta);
normForm := u0*applySigmaToCoefficients(u0)*applySigmaToCoefficients(applySigmaToCoefficients(u0));
QOfPsi := coordinateForms(delta*psi(u0)^3*applySigmaToCoefficients(psi(u0)), theta);
P := PForms(delta, theta);
toFormRingOverK := hom< formRingOverQ -> formRingOverK | A0, A1, A2 >;
// Q^(n)(psi) = N(u_0)^3 P^(n) for n = 0, 1, 2 (delta = 2 - theta)
assert forall{ n : n in [1..3] | toFormRingOverK(QOfPsi[n]) eq normForm^3*toFormRingOverK(P[n]) };
show("degree of psi on the coordinates", TotalDegree(psi(u0)));
verified();

statement("Remark 4.2", "rem:elkies-map", "the other quotient maps");
characterSpace := VectorSpace(GF(7), 3);
characterQuotient, toQuotient := quo< characterSpace | characterSpace ! [1,1,1] >;
characterLines := { sub< characterQuotient | vec > : vec in characterQuotient | vec ne 0 };
function shiftLine(L)
     vec := Basis(L)[1] @@ toQuotient;
     return sub< characterQuotient | toQuotient(characterSpace ! [vec[3], vec[1], vec[2]]) >;
end function;
stableLines := { L : L in characterLines | shiftLine(L) eq L };
otherOrbits := { { L, shiftLine(L), shiftLine(shiftLine(L)) } : L in characterLines diff stableLines };
show("lines of mu_7^3/mu_7, stable lines, other orbits", [ #characterLines, #stableLines, #otherOrbits ]);
// mu_7^3/mu_7 has eight lines
assert #characterLines eq 8;
// two of them are stable under the cyclic shift, the other six form two orbits of three
assert #stableLines eq 2;
assert #otherOrbits eq 2;
assert forall{ o : o in otherOrbits | #o eq 3 };
quarticWithSigmaInverse := Curve(projectivePlane,
     traceOfCoefficients(genericElement(theta)^3
          * applySigmaToCoefficients(applySigmaToCoefficients(genericElement(theta)))));
show("Tr(v^3 sigma^-1(v))", DefiningEquation(quarticWithSigmaInverse));
// Tr(v^3 sigma^-1(v)) = 0 is a smooth quartic with no Q_2-points
assert IsNonsingular(quarticWithSigmaInverse);
assert not IsLocallySolvable(quarticWithSigmaInverse, 2);
verified();

statement("Lemma 4.3", "lem:twisting", "seventh powers are norms times (3 + sigma)-th powers");
// lambda = u_0 = a_0 + a_1 theta + a_2 theta^2, the generic element; with
// nu = lambda^2/sigma(lambda), N(lambda) nu^3 sigma(nu) = lambda^7 becomes, after
// multiplying by sigma(lambda)^3 sigma^2(lambda), an identity of polynomials:
lambda := genericElement(theta);
lambdaConjugate1 := applySigmaToCoefficients(lambda);
lambdaConjugate2 := applySigmaToCoefficients(lambdaConjugate1);
normOfLambda := lambda*lambdaConjugate1*lambdaConjugate2;
// lambda^7 = N(lambda) nu^3 sigma(nu), nu = lambda^2/sigma(lambda), for the generic lambda
assert lambda^7*lambdaConjugate1^3*lambdaConjugate2 eq normOfLambda*lambda^6*lambdaConjugate1^2;
// the same identity on a sample of elements of K
assert forall{ l : l in [theta, 2*theta^2 - 3, (theta + 5)/(theta - 7)] |
               l^7 eq Norm(l)*nu^3*sigma(nu) where nu := l^2/sigma(l) };
verified();

alpha := theta^2 - 5*theta + 1;

statement("Proposition 4.4", "prop:klein-identity", "Klein's identity");
show("alpha", alpha);
sqrtMinus7 := zeta + zeta^2 + zeta^4 - zeta^3 - zeta^5 - zeta^6;
// sqrt(-7) = zeta + zeta^2 + zeta^4 - zeta^3 - zeta^5 - zeta^6
assert sqrtMinus7^2 eq -7;
// (4.7): alpha = sqrt(-7) (zeta^4 - zeta^-4) = 4 c_1 + 2 c_2 + c_4
assert embedInCyclotomic(alpha) eq sqrtMinus7*(zeta^4 - zeta^-4);
assert embedInCyclotomic(alpha) eq 4*zetaTrace(1) + 2*zetaTrace(2) + zetaTrace(4);

// Klein's coordinates v_0, v_1, v_2, over K
kleinRingOverK<v0, v1, v2> := PolynomialRing(K, 3);
alpha0 := alpha/7;                                  // alpha_i = sigma^i(alpha0)
vartheta0 := alpha0*v0 + sigmaPower(alpha0,1)*v1 + sigmaPower(alpha0,2)*v2;
vartheta1 := applySigmaToCoefficients(vartheta0);
vartheta2 := applySigmaToCoefficients(vartheta1);
// Klein's identity: Tr(vartheta^3 sigma(vartheta)) = v_0^3 v_1 + v_1^3 v_2 + v_2^3 v_0
assert vartheta0^3*vartheta1 + vartheta1^3*vartheta2 + vartheta2^3*vartheta0
       eq v0^3*v1 + v1^3*v2 + v2^3*v0;

// Klein's involution, as in [Elkies, (1.3)]; its entries are sigma^i(alpha)/7
embeddedAlpha := [ embedInCyclotomic(sigmaPower(alpha0, i)) : i in [0..2] ];
kleinInvolution := Matrix(cyclotomicField, 3, 3,
     [ embeddedAlpha[2], embeddedAlpha[3], embeddedAlpha[1],
       embeddedAlpha[3], embeddedAlpha[1], embeddedAlpha[2],
       embeddedAlpha[1], embeddedAlpha[2], embeddedAlpha[3] ]);
elkiesInvolution := (-1/sqrtMinus7) * Matrix(cyclotomicField, 3, 3,
     [ zeta - zeta^6,   zeta^2 - zeta^5, zeta^4 - zeta^3,
       zeta^2 - zeta^5, zeta^4 - zeta^3, zeta - zeta^6,
       zeta^4 - zeta^3, zeta - zeta^6,   zeta^2 - zeta^5 ]);
// Klein's matrix [Elkies (1.3)] has entries sigma^i(alpha)/7
assert kleinInvolution eq elkiesInvolution;
// it has order 2 and determinant 1
assert kleinInvolution^2 eq 1;
assert Determinant(kleinInvolution) eq 1;

function kleinQuarticForm(coordinates)
     return coordinates[1]^3*coordinates[2] + coordinates[2]^3*coordinates[3]
          + coordinates[3]^3*coordinates[1];
end function;
kleinRingOverL := PolynomialRing(cyclotomicField, 3);   // v_0, v_1, v_2 over Q(zeta_7)
// Klein's matrix preserves the quartic form
kleinVariables := [ kleinRingOverL.j : j in [1..3] ];
movedKleinVariables := [ &+[ kleinInvolution[i][j]*kleinVariables[j] : j in [1..3] ] : i in [1..3] ];
assert kleinQuarticForm(movedKleinVariables) eq kleinQuarticForm(kleinVariables);
verified();

statement("Lemma 4.5", "lem:hurwitz", "the rational points of the Klein quartic (Hurwitz)");
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
show("the quotient by the cyclic permutation, minimal model", minimalModel);
show("its conductor, rank, and number of rational points",
     [ Conductor(minimalModel), Rank(minimalModel), #TorsionSubgroup(minimalModel) ]);
show("rational points of the Klein quartic", joined([ pointString(Eltseq(pt)) : pt in kleinPoints ], ", "));
// the Klein quartic is smooth of genus 3
assert IsNonsingular(kleinQuartic);
assert Genus(kleinQuartic) eq 3;
// the quotient by the cyclic permutation has genus 1
assert Genus(quotientCurve) eq 1;
// it is an elliptic curve of conductor 49, rank 0, with 2 rational points
assert Conductor(minimalModel) eq 49;
assert Rank(minimalModel) eq 0;
assert #TorsionSubgroup(minimalModel) eq 2;
// the Klein quartic has exactly the three rational points (1:0:0), (0:1:0), (0:0:1)
assert { Eltseq(pt) : pt in kleinPoints } eq { [1,0,0], [0,1,0], [0,0,1] };
verified();

statement("Corollary 4.7", "cor:Z0", "the untwisted quartic Z_0");
Z0Form := traceOfCoefficients(genericElement(theta)^3*applySigmaToCoefficients(genericElement(theta)));
Z0 := Curve(projectivePlane, Z0Form);
QForms := coordinateForms(derivativeAtThetaSplit*genericElement(theta)^3
                          *applySigmaToCoefficients(genericElement(theta)), theta);
show("Z_0", Z0Form);
// Z_0 = {Tr(v^3 sigma(v)) = 0} is Z_{theta, f'(theta)}
assert QForms[3] eq Z0Form;
// it is a smooth plane quartic of genus 3
assert IsNonsingular(Z0);
assert Genus(Z0) eq 3;
alphaConjugates := [ coordinatesInBasis(sigmaPower(alpha, i), theta) : i in [0..2] ];
tValues := [ Evaluate(QForms[1], c) / -Evaluate(QForms[2], c) : c in alphaConjugates ];
show("[alpha], [sigma(alpha)], [sigma^2(alpha)] in the coordinates a_0, a_1, a_2", alphaConjugates);
show("their images t = x/y under varphi", tValues);
// [alpha], [sigma(alpha)], [sigma^2(alpha)] lie on Z_0
assert forall{ c : c in alphaConjugates | Evaluate(Z0Form, c) eq 0 };
// they lie over t = -1, 5/2, 4/3
assert tValues eq [ -1, 5/2, 4/3 ];
verified();

finish("klein.m");
quit;
