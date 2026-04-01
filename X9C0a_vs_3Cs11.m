// This script proves the now improved part of Prop 3.8
// namely, that 3Cs.1.1 is incompatible
// with 9C0-9a (hence also with 9J0-9a and 9J0-9b),
// for non-CM elliptic curves over Q.

A2<t,y> := AffineSpace(Rationals(), 2);
C := Curve(A2, y^3 - t^3 - 27);
PC := ProjectiveClosure(C);

// Put the curve into Weierstrass form
E, phi := EllipticCurve(PC, PC![1,1,0]);
RankBounds(E);
//0 0

// All rational points on E are torsion
Tor, m := TorsionSubgroup(E);
ptsE := m([P : P in Tor]);

print "Rational points on the Weierstrass model:";
ptsE;

// Pull back to the projective cubic PC
ptsPC := [* *];
for pt in ptsE do
    pre := pt @@ phi;
    if Dimension(pre) eq 0 then
        for P in Points(pre) do
            Append(~ptsPC, P);
        end for;
    end if;
end for;

print "Pulled back rational points on the projective cubic:";
ptsPC;

// Convert projective points to affine (u,t)-points when possible
pts_aff := [];
for P in ptsPC do
    if P[3] ne 0 then
        Append(~pts_aff, <P[1]/P[3], P[2]/P[3]>);
    else
        print "Point at infinity on the cubic:", P;
    end if;
end for;

print "Affine rational points (t,y) on y^3 = t^3 + 27:";
pts_aff;