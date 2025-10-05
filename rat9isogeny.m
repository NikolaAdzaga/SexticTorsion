//This code is checking the 2nd case in the proof of Proposition 3.4, i.e.
//if E has a rational 9-isogeny (and G_E(2)=2B),
// then its torsion over sextic K is not C3 + C18.

Q := Rationals();
R<t> := FunctionField(Q);

// curve coefficients given in Ingram's Appendix
// for an EC E with a rational 9-isogeny
// (more precisely: E can be a twist of this E_t)

A := -3*t*(t^3 - 24);
B :=  2*(t^6 - 36*t^3 + 216);
E_t := EllipticCurve([0,0,0,A,B]);


jInvariant(E_t);
//(t^12 - 72*t^9 + 1728*t^6 - 13824*t^3)/(t^3 - 27)
// = t^3*(t^3-24)^3 / (t^3-27)

Discriminant(E_t);
//2985984*t^3 - 80621568
// = 2^12 * 3^6 * (t^3-27)

// specialize at t = -6
E1 := EllipticCurve([0,0,0, Evaluate(A,-6), Evaluate(B,-6)]);
HasComplexMultiplication(E1);
//true -27

// specialize at t = 0
E2 := EllipticCurve([0,0,0, Evaluate(A,0), Evaluate(B,0)]);
HasComplexMultiplication(E2);
//true -3



C := EllipticCurve([0, 0, 0, 0, -27]);
RankBounds(C);
//0 0

TorsionSubgroup(C);
//Abelian Group isomorphic to Z/2
//Defined on 1 generator
//Relations:
//    2*$.1 = 0

// Hence C has only two rational points:
// [3 : 0 : 1] and a point at infinity
// However, we need points over K=Q(zeta3)
// such that the first coordinate is in Q

P<x> := PolynomialRing(Rationals());
K<zeta3> := NumberField(x^2+3);
CK := BaseChange(C, K);
RankBounds(CK);
// 0 0
// so the only K-points are torsion points

PointsK := [];
T, m := TorsionSubgroup(CK);
gens := Generators(T);
torsion_gens := [m(g) : g in gens];
gen1 := torsion_gens[1];
gen2 := torsion_gens[2];

for a in [0..5] do
    for b in [0..1] do
        P := a * gen1 + b * gen2;
        
        Append(~PointsK, P);
        printf "P(%o,%o) = %o\n", a, b, P;
    end for;
end for;

// P(0,0) = (0 : 1 : 0)
// P(0,1) = (1/2*(-3zeta3 - 3) : 0 : 1)
// P(1,0) = (-6 : 9zeta3 : 1)
// P(1,1) = (-3zeta3 + 3 : 9zeta3 : 1)
// P(2,0) = (0 : 3zeta3 : 1)
// P(2,1) = (3zeta3 + 3 : -9zeta3 : 1)
// P(3,0) = (3 : 0 : 1)
// P(3,1) = (1/2(3zeta3 - 3) : 0 : 1)
// P(4,0) = (0 : -3zeta3 : 1)
// P(4,1) = (3zeta3 + 3 : 9zeta3 : 1)
// P(5,0) = (-6 : -9zeta3 : 1)
// P(5,1) = (-3zeta3 + 3 : -9*zeta3 : 1)
