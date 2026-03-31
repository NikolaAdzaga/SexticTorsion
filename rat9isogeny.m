// This is for the second case in Proposition 3.5.
// We test possible G_E(9), assuming that E has
// a rational 9-isogeny.

// Let Hsub = G_E(9) <= GL(2,Z/9Z), and let
// N = ker(Hsub -> GL(2,F_3)).
// Since K = Q(E[3]), the field K cuts out exactly this kernel.
// Therefore E(K) contains a point of order 9
// iff N fixes a primitive vector in (Z/9Z)^2.
//
// We go through tabulated level-9 groups H, and for each candidate
// subgroup Hsub with <Hsub,-I> = H:
//
// a.) check whether the mod-3 image is conjugate to 3B.1.1 or 3B.1.2;
// b1.) form N = ker(Hsub -> GL(2,F_3));
// b2.) test whether N fixes a primitive order-9 vector;
// c.) for surviving candidates, compute the Hsub-stable cyclic
//     subgroups of order 9 in (Z/9Z)^2.

// We now avoid use of Stabilizer since Magma acts on the right,
// while tabulated groups from https://math.mit.edu/~drew/SZ16/g0groups.m
// are intended to act on the left.

Z9 := Integers(9);
Z3 := Integers(3);

G9 := GL(2, Z9);
G3 := GL(2, Z3);

I3 := Identity(G3);
negI := G9!(-IdentityMatrix(Z9,2));

ToVec := func< a,b | Vector(Z9,[a,b]) >;
IsOrd9 := func< v | (not IsZero(v)) and (Gcd([Integers()!x : x in Eltseq(v)] cat [9]) eq 1) >;
V9 := [ ToVec(a,b) : a in Z9, b in Z9 | IsOrd9(ToVec(a,b)) ];

// The two mod-3 groups from Table 1
B311 := sub< G3 |
    G3![1,0,0,2],
    G3![1,1,0,1]
>;

B312 := sub< G3 |
    G3![2,0,0,1],
    G3![1,1,0,1]
>;

// Reduce an element of GL(2,Z/9Z) mod 3
ReduceMod3 := function(g)
    return G3![ Z3!(Integers()!x) : x in Eltseq(g) ];
end function;

// Image of a subgroup mod 3
ReductionImage := function(Hsub)
    return sub< G3 | [ ReduceMod3(g) : g in Generators(Hsub) ] >;
end function;

// Kernel of reduction Hsub -> GL(2,F_3)
KernelMod3 := function(Hsub)
    kerelts := [ g : g in Hsub | ReduceMod3(g) eq I3 ];
    return sub< Hsub | kerelts >;
end function;

// Check whether mod-3 image is conjugate to one of the two groups
HasTargetMod3Image := function(Hbar)
    for g in G3 do
        if Conjugate(Hbar, g) eq B311 then
            return true, "3B.1.1";
        end if;
        if Conjugate(Hbar, g) eq B312 then
            return true, "3B.1.2";
        end if;
    end for;
    return false, "";
end function;

HasFixedOrd9Vector := function(J)
    for v in V9 do
        if Stabilizer(J, v) eq J then
            return true, v;
        end if;
    end for;
    return false, ToVec(0,0);
end function;

// Degree over Q of the field of definition of the point represented by v
DegreeOfVector := function(Hsub, v)
    return Index(Hsub, Stabilizer(Hsub, v));
end function;

// Representatives of Hsub-stable cyclic subgroups of order 9
// this is testing for rational 9-isogeny.
SameCyclicSubgroup := function(v, w)
    return { (Z9!k)*v : k in [0..8] } eq { (Z9!k)*w : k in [0..8] };
end function;

HasStableCyclicOrd9Subgroup := function(Hsub)
    for v in V9 do
        stable := true;
        for g in Generators(Hsub) do
            if not SameCyclicSubgroup(v, v*g) then
                stable := false;
                break;
            end if;
        end for;
        if stable then
            return true, v;
        end if;
    end for;
    return false, ToVec(0,0);
end function;


GroupDataFormat := recformat< label: MonStgElt, gens: SeqEnum >;
gl2tab := AssociativeArray();

gl2tab["9A0-9a"] := rec<GroupDataFormat | label:="9A0-9a", gens:=[[0,2,4,0],[1,1,4,5],[1,0,0,2]]>;
gl2tab["9B0-9a"] := rec<GroupDataFormat | label:="9B0-9a", gens:=[[1,1,0,1],[2,0,0,5],[1,0,0,2]]>;
gl2tab["9C0-9a"] := rec<GroupDataFormat | label:="9C0-9a", gens:=[[2,0,0,5],[4,2,3,4],[1,0,0,2]]>;
gl2tab["9D0-9a"] := rec<GroupDataFormat | label:="9D0-9a", gens:=[[2,0,0,5],[1,3,3,1],[0,2,4,0],[1,0,0,2]]>;
gl2tab["9E0-9a"] := rec<GroupDataFormat | label:="9E0-9a", gens:=[[1,3,0,1],[2,1,1,1],[4,2,0,5]]>;
gl2tab["9F0-9a"] := rec<GroupDataFormat | label:="9F0-9a", gens:=[[0,2,4,1],[4,3,5,4],[4,5,0,5]]>;
gl2tab["9G0-9a"] := rec<GroupDataFormat | label:="9G0-9a", gens:=[[0,4,2,3],[5,1,1,4],[5,3,0,4]]>;
gl2tab["9H0-9a"] := rec<GroupDataFormat | label:="9H0-9a", gens:=[[1,3,0,1],[5,0,3,2],[1,0,2,2]]>;
gl2tab["9H0-9b"] := rec<GroupDataFormat | label:="9H0-9b", gens:=[[1,3,0,1],[5,0,3,2],[2,1,0,1]]>;
gl2tab["9H0-9c"] := rec<GroupDataFormat | label:="9H0-9c", gens:=[[1,3,0,1],[5,0,3,2],[4,2,0,5]]>;
gl2tab["9I0-9a"] := rec<GroupDataFormat | label:="9I0-9a", gens:=[[2,1,0,5],[1,2,3,2]]>;
gl2tab["9I0-9b"] := rec<GroupDataFormat | label:="9I0-9b", gens:=[[2,1,0,5],[4,0,3,5]]>;
gl2tab["9I0-9c"] := rec<GroupDataFormat | label:="9I0-9c", gens:=[[2,2,0,5],[2,2,3,1]]>;
gl2tab["9J0-9a"] := rec<GroupDataFormat | label:="9J0-9a", gens:=[[1,3,0,1],[2,2,3,8],[1,2,0,2]]>;
gl2tab["9J0-9b"] := rec<GroupDataFormat | label:="9J0-9b", gens:=[[1,3,0,1],[2,2,3,8],[2,1,0,1]]>;
gl2tab["9J0-9c"] := rec<GroupDataFormat | label:="9J0-9c", gens:=[[1,3,0,1],[5,2,3,5],[4,0,0,5]]>;

labels := Sort([k : k in Keys(gl2tab)]);
survivors := [* *];

for label in labels do
    data := gl2tab[label];

    printf "\n============================================================\n";
    printf "===== Analyzing H: %o =====\n", data`label;
    print  "============================================================\n";

    H := sub<G9 | [G9!g : g in data`gens]>;

    // Possible actual images G_E(9) with <Hsub,-I> = H
    CandidateHsubs := [* H *];
    for rec in Subgroups(H : IndexLimit := 2) do
        Hsub := rec`subgroup;
        if Index(H, Hsub) eq 2 and not (negI in Hsub) then
            Append(~CandidateHsubs, Hsub);
        end if;
    end for;

    hcount := 0;
    for Hsub in CandidateHsubs do
        hcount +:= 1;

        printf "\n-- Candidate Hsub #%o (index(H,Hsub)=%o, |Hsub|=%o)\n",
               hcount, Index(H,Hsub), #Hsub;

        Hbar := ReductionImage(Hsub);
        ok3, which3 := HasTargetMod3Image(Hbar);

        if not ok3 then
            printf "   mod-3 image is not conjugate to 3B.1.1 or 3B.1.2; skipping.\n";
            continue;
        end if;

        printf "   mod-3 image is conjugate to %o (|image|=%o).\n", which3, #Hbar;

        N := KernelMod3(Hsub);
        printf "   |N| = |ker(Hsub -> GL(2,F_3))| = %o\n", #N;

        ok9, v9 := HasFixedOrd9Vector(N);
        if ok9 then
            degv := DegreeOfVector(Hsub, v9);
            printf "   N fixes a primitive order-9 vector v=%o\n", v9;
            printf "   Degree of this point over Q (inside Q(E[9])) is %o\n", degv;
            printf "   Hence E(Q(E[3])) can contain a point of order 9 for this candidate.\n";

            okIso, vIso := HasStableCyclicOrd9Subgroup(Hsub);
            if okIso then
              printf "   Hsub stabilizes a cyclic subgroup of order 9, generated for example by v=%o\n", vIso;
            else
              printf "   Hsub stabilizes no cyclic subgroup of order 9.\n";
            end if;

            Append(~survivors, <label, hcount, which3, Hsub, v9, degv, okIso, vIso>);
        else
            printf "   N fixes no primitive order-9 vector.\n";
            printf "   Hence E(Q(E[3])) cannot contain a point of order 9 for this candidate.\n";
        end if;
    end for;
end for;


printf "\n============================================================\n";
printf "==================== FINAL SUMMARY ==========================\n";
printf "============================================================\n";

if #survivors eq 0 then
    printf "No candidate level-9 image survives.\n";
    printf "Therefore no non-CM E/Q with mod-3 image 3B.1.1 or 3B.1.2\n";
    printf "can have a point of order 9 over K=Q(E[3]).\n";
else
    printf "Surviving candidates:\n";
    for rec in survivors do
       printf "   H label=%o, candidate #%o, mod-3 type=%o, example v=%o, degree=%o, rational-9-isogeny-test=%o\n",
           rec[1], rec[2], rec[3], rec[5], rec[6], rec[7];
    end for;
end if;