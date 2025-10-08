//This code is checking the 1st case in the proof of Proposition 3.4, i.e.
//E does not have a rational 9-isogeny, has a rational 3-isogeny and G_E(2)=2B

A<x,y>:=AffineSpace(Rationals(),2);
// Define the affine curve C from the proposition.
C:=Curve(A,(x+3)*(x^2-3*x+9)*(x^3+3)^3*y-256*(y+1)^3*x^3);
// Work with the projective closure.
PC:=ProjectiveClosure(C);
R<x,y>:=PolynomialRing(Rationals(),2);

// Check if the curve is hyperelliptic and get a model X.
tr,X:=IsHyperelliptic(PC);
// tr;
// true

// Find a simplified y^2 = h(x) model for X.
simplX,f:=SimplifiedModel(X);
// This map f2 takes us from the simplified model back to X.
f2:=Inverse(f);

printf "\n ================== Analyzing the simplified model ================== \n";
// The simplified model is of genus 2.
simplX;
// Hyperelliptic Curve defined by y^2 = x^6 - 34*x^3 + 1 over Rational Field

// Compute the Jacobian of the simplified curve.
J:=Jacobian(simplX);
printf "Rank bound for the Jacobian is %o\n", RankBounds(J);
// 0

// We need the full map from the simplified model back to our original curve PC.
tr,g:=IsIsomorphic(PC, X);
printf "Computing isomorphism (%o)\n", tr;
tr,g2:=IsInvertible(g);
printf "Computing its inverse (%o)\n", tr;
tr;
g2:=Inverse(g);
// The total map is g2(f2(P)).

printf "\n ================== Finding all rational points ================== \n";
// Since the rank is 0, classical method can find all rational points on simplX.
pts:=Chabauty0(J);
printf "We find all the points on our simplified hyperelliptic curve:\n %o \n\n", pts;
// {@ (0 : 0 : 1), (3 : 9 : 1), (3 : -9 : 1), (1 : 0 : 0) @}

// Map these points back to our original curve PC.
printf "The rational points on the original curve are: \n";
for i:=1 to #pts do
    g2(f2(pts[i]));
end for;
// (3 : -16 : 1)
// (-3 : -1 : 1)
// (0 : 0 : 1)
// (1 : -1 : 0)

printf "\n ================== Conclusion ================== \n";
printf "The only points on PC for which xy is not 0 are (3,-16,1) and (-3,-1,1).
Plugging in y=-16 and y=-1 in the j-map j(E)=256(y+1)^3/y, we get that
j(E)=54000 for y=-16, and j(E)=0 for y=-1.
In both of these cases, the corresponding elliptic curve E has complex multiplication (CM).\n\n";