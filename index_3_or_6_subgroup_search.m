// This is a part of the proof of Theorem 3.1.
// We go through possible G_E(9) by analyzing the action on (Z/9Z)^2.

// More precisely, for each tabulated level-9 group H
// and each candidate Hsub=G_E(9) with <Hsub,-I> = H,
// we search for primitive order-9 vectors v whose stabilizer
// has index 3 or 6 in Hsub.
// The computation shows two things
// 1.) There is a point of order 9 of degree 6 in our E(K).
// 2.) What are the possible exceptional G_E(9), which
//	are then further analyzed in separate files,
//	e.g. X1hyp.m.


Z9 := Integers(9);
G  := GL(2, Z9);
negI := G!(-IdentityMatrix(Z9,2));

ToVec := func< a,b | Vector(Z9,[a,b]) >;
IsOrd9 := func< v | (not IsZero(v)) and (Gcd([Integers()!x : x in Eltseq(v)] cat [9]) eq 1) >;
V9 := [ ToVec(a,b) : a in Z9, b in Z9 | IsOrd9(ToVec(a,b)) ];

HasFixedOrd9Vector := function(J)
    for v in V9 do
        if Stabilizer(J, v) eq J then
            return true, v;
        end if;
    end for;
    return false, ToVec(0,0);
end function;

CountIndexSubgroupsFixingOrd9 := function(Hsub, d)
    n := 0;
    v0 := ToVec(0,0);
    for rec in Subgroups(Hsub : IndexLimit := d) do
        J := rec`subgroup;
        if Index(Hsub, J) ne d then
            continue;
        end if;
        ok, v := HasFixedOrd9Vector(J);
        if ok then
            n +:= 1;
            if n eq 1 then v0 := v; end if;
        end if;
    end for;
    return n, v0;
end function;

FindStabIndex6Vector := function(Hsub)
    for v in V9 do
        if Index(Hsub, Stabilizer(Hsub, v)) eq 6 then
            return true, v;
        end if;
    end for;
    return false, ToVec(0,0);
end function;

FindStabIndex3Vector := function(Hsub)
    for v in V9 do
        if Index(Hsub, Stabilizer(Hsub, v)) eq 3 then
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
for label in labels do
    data := gl2tab[label];

    printf "\n============================================================\n";
    printf "===== Analyzing H: %o =====\n", data`label;
    print  "============================================================\n";

    H := sub<G | [G!g : g in data`gens]>;

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

        n3, v3 := CountIndexSubgroupsFixingOrd9(Hsub, 3);
        printf "   Index-3 subgroups of Hsub fixing a primitive order-9 vector: %o\n", n3;
        if n3 gt 0 then
            printf "      example vector fixed by some index-3 subgroup: v=%o\n", v3;
            printf "      stabilizer index in Hsub for this v: %o\n", Index(Hsub, Stabilizer(Hsub, v3));
        end if;

        ok3, vstab3 := FindStabIndex3Vector(Hsub);
        if ok3 then
            printf "      sanity: found vector with stabilizer index 3: v=%o\n", vstab3;
            printf "      stabilizer index in Hsub for this v: %o\n", Index(Hsub, Stabilizer(Hsub, vstab3));
        else
            printf "      sanity: no vector with stabilizer index 3 found.\n";
        end if;

        n6, v6 := CountIndexSubgroupsFixingOrd9(Hsub, 6);
        printf "   Index-6 subgroups of Hsub fixing a primitive order-9 vector: %o\n", n6;
        if n6 gt 0 then
            printf "      example vector fixed by some index-6 subgroup: v=%o\n", v6;
            printf "      stabilizer index in Hsub for this v: %o\n", Index(Hsub, Stabilizer(Hsub, v6));
        end if;

        ok6, vstab6 := FindStabIndex6Vector(Hsub);
        if ok6 then
            printf "      sanity: found vector with stabilizer index 6: v=%o\n", vstab6;
            printf "      stabilizer index in Hsub for this v: %o\n", Index(Hsub, Stabilizer(Hsub, vstab6));
        else
            printf "      sanity: no vector with stabilizer index 6 found.\n";
        end if;

    end for;
end for;
