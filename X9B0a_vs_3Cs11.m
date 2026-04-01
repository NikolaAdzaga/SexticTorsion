// This script is analogous to X9C0a_vs_3Cs11.m.
// It treats the case G_E(3) = 3Cs.1.1 versus level-9 subgroup 9B0-9a.
//
// Since the j-map on 3Cs.1.1 is a cube, and
// j_{9B0-9a}(t) = ((t+3)^3*(t^3+9*t^2+27*t+3)^3)/(t*(t^2+9*t+27)),
// any rational point giving rise to such an elliptic curve
// must correspond to a rational point on
//
//     y^3 = t*(t^2 + 9*t + 27).
//
// We show that this cubic is an elliptic curve of rank 0,
// enumerate its rational points, and check which t-values
// can occur. The only affine rational points lead either
// to a cusp (t=0) or to j=0 (CM).

A2<t,y> := AffineSpace(Rationals(), 2);
C := Curve(A2, y^3 - t*(t^2 + 9*t + 27));
PC := ProjectiveClosure(C);

// Put the curve into Weierstrass form.
// The point (1:1:0) is a rational point at infinity on the projective cubic.
E, phi := EllipticCurve(PC, PC![1,1,0]);

print "Weierstrass model:";
E;

print "Rank bounds:";
RankBounds(E);   // expected: 0 0

// All rational points on E are torsion.
Tor, m := TorsionSubgroup(E);
print "Torsion subgroup:";
Tor;

// Rational points on the Weierstrass model
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

// Convert projective points to affine (t,y)-points when possible
pts_aff := [* *];
for P in ptsPC do
    if P[3] ne 0 then
        tt := P[1]/P[3];
        yy := P[2]/P[3];
        Append(~pts_aff, <tt, yy>);
    else
        print "Point at infinity on the cubic:", P;
    end if;
end for;

print "Affine rational points (t,y) on y^3 = t*(t^2+9*t+27):";
pts_aff;

// The 9B0-9a j-map
j9B0 := function(tt)
    return ((tt+3)^3 * (tt^3 + 9*tt^2 + 27*tt + 3)^3) /
           (tt * (tt^2 + 9*tt + 27));
end function;

print "Analyzing affine rational points:";
good_nonCM := [* *];

for P in pts_aff do
    tt := P[1];
    yy := P[2];

    printf "Point (t,y) = (%o,%o):\n", tt, yy;

    // Denominator zero means the j-map is undefined there,
    // i.e. this is a cusp / degenerate parameter.
    if tt eq 0 or (tt^2 + 9*tt + 27) eq 0 then
        print "   denominator of j_{9B0-9a}(t) is zero;";
        print "   this does not give an elliptic curve in the family.";
        continue;
    end if;

    j := j9B0(tt);
    printf "   j = %o\n", j;

    if j eq 0 then
        print "   This is CM (j=0).";
    else
        print "   This would be a non-CM candidate.";
        Append(~good_nonCM, <tt, yy, j>);
    end if;
end for;

print "---------------------------------------------";
if #good_nonCM eq 0 then
    print "Conclusion:";
    print "No affine rational point on y^3 = t*(t^2+9*t+27)";
    print "gives a non-CM elliptic curve from the 9B0-9a family.";
else
    print "Unexpected non-CM candidates found:";
    good_nonCM;
end if;
print "---------------------------------------------";