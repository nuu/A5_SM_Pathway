# M62_E6_trinification_v2.gap
# Registry verification of E₆ maximal subalgebra selection
# No Lie algebra package required - pure data walk
#
# Date: 2026-03-29

Print("=== M62/M63: E₆ Maximal Subalgebra Selection ===\n\n");

# ─── 1. Registry data (Dynkin 1957, Slansky 1981) ───

# E₆ maximal subalgebras: 6 total
# 3 regular (from extended Dynkin diagram node removal)
# 3 special (S-type embeddings)

names := ["SO(10)xU(1)", "SU(6)xSU(2)", "SU(3)^3", 
          "SU(3)xG2", "Sp(8)", "F4"];

reg_or_spec := ["regular", "regular", "regular",
                "special", "special", "special"];

# Simple factor types: list of [type_string, rank] pairs
# U(1) is abelian, encoded as ["U",1]
factors := [
    [["D",5], ["U",1]],                  # SO(10) x U(1)
    [["A",5], ["A",1]],                  # SU(6) x SU(2)
    [["A",2], ["A",2], ["A",2]],         # SU(3)^3
    [["A",2], ["G",2]],                  # SU(3) x G2
    [["C",4]],                           # Sp(8)
    [["F",4]]                            # F4
];

# Adjoint dimensions
adj_dims := [46, 38, 24, 22, 36, 52];

# 27 branching: list of component dimensions
branch_27 := [
    [16, 10, 1],                         # SO(10)xU(1): 16+10+1
    [12, 15],                            # SU(6)xSU(2): (6,2)+(15,1)
    [9, 9, 9],                           # SU(3)^3: (3,3b,1)+(1,3,3b)+(3b,1,3)
    [21],                                # SU(3)xG2: (3,7)
    [27],                                # Sp(8): irreducible
    [26, 1]                              # F4: 26+1
];

# Total rank of simple (non-abelian) factors
total_ranks := [5, 6, 6, 4, 4, 4];

Print("Registry of E_6 maximal subalgebras:\n");
Print("─────────────────────────────────────────────────\n");

for i in [1..6] do
    Print("  ", names[i], " (", reg_or_spec[i], ")\n");
    Print("    Factors: ", factors[i], "\n");
    Print("    adj dim: ", adj_dims[i], "\n");
    Print("    27 -> ", branch_27[i], 
          " (sum=", Sum(branch_27[i]), ")\n");
    Print("    total rank: ", total_ranks[i], "\n\n");
od;

# ─── 2. Verification checks ───

Print("=== Verification ===\n\n");

# All 27 branchings sum to 27
all_sum_ok := true;
for i in [1..6] do
    if Sum(branch_27[i]) <> 27 then
        all_sum_ok := false;
        Print("ERROR: ", names[i], " branching sum = ", 
              Sum(branch_27[i]), "\n");
    fi;
od;
Print("All 27 branchings sum to 27: ", all_sum_ok, "\n\n");

# ─── 3. M62: All simple factors isomorphic ───

Print("=== M62: All non-abelian factors isomorphic? ===\n\n");

for i in [1..6] do
    facs := factors[i];
    # Filter out abelian factors
    nonab := Filtered(facs, f -> f[1] <> "U");
    
    if Length(nonab) <= 1 then
        Print("  ", names[i], ": n/a (", Length(nonab), 
              " non-abelian factor)\n");
    else
        all_iso := true;
        for j in [2..Length(nonab)] do
            if nonab[j] <> nonab[1] then
                all_iso := false;
            fi;
        od;
        Print("  ", names[i], ": all_isomorphic = ", all_iso, "\n");
    fi;
od;

# Count
count_m62 := 0;
m62_names := [];
for i in [1..6] do
    facs := factors[i];
    nonab := Filtered(facs, f -> f[1] <> "U");
    if Length(nonab) >= 2 then
        all_iso := true;
        for j in [2..Length(nonab)] do
            if nonab[j] <> nonab[1] then
                all_iso := false;
            fi;
        od;
        if all_iso then
            count_m62 := count_m62 + 1;
            Add(m62_names, names[i]);
        fi;
    fi;
od;

Print("\nSubalgebras passing M62: ", m62_names, "\n");
if count_m62 = 1 and m62_names[1] = "SU(3)^3" then
    Print("*** M62 PASS: SU(3)^3 is unique ***\n\n");
else
    Print("*** M62 result: ", count_m62, " candidates ***\n\n");
fi;

# ─── 4. M63: 27 decomposes into equal-dim components ───

Print("=== M63: 27 equal-dimension branching? ===\n\n");

for i in [1..6] do
    b := branch_27[i];
    if Length(b) >= 2 then
        all_eq := (Length(Set(b)) = 1);
        Print("  ", names[i], ": dims = ", b, 
              ", all_equal = ", all_eq, "\n");
    else
        Print("  ", names[i], ": dims = ", b, 
              ", irreducible (n/a)\n");
    fi;
od;

count_m63 := 0;
m63_names := [];
for i in [1..6] do
    b := branch_27[i];
    if Length(b) >= 2 and Length(Set(b)) = 1 then
        count_m63 := count_m63 + 1;
        Add(m63_names, names[i]);
    fi;
od;

Print("\nSubalgebras passing M63: ", m63_names, "\n");
if count_m63 = 1 and m63_names[1] = "SU(3)^3" then
    Print("*** M63 PASS: SU(3)^3 is unique ***\n\n");
else
    Print("*** M63 result: ", count_m63, " candidates ***\n\n");
fi;

# ─── 5. Combined selection ───

Print("=== Combined selection table ===\n\n");
Print("Subalgebra       | T1(SM) | T2(iso) | T3(eq27) | Result\n");
Print("──────────────────+────────+─────────+──────────+───────\n");

for i in [1..6] do
    # T1: rank >= 4
    t1 := (total_ranks[i] >= 4);
    
    # T2: all non-abelian factors isomorphic, >= 2 factors
    facs := factors[i];
    nonab := Filtered(facs, f -> f[1] <> "U");
    t2 := false;
    if Length(nonab) >= 2 then
        t2 := true;
        for j in [2..Length(nonab)] do
            if nonab[j] <> nonab[1] then t2 := false; fi;
        od;
    fi;
    
    # T3: equal-dim 27 branching
    b := branch_27[i];
    t3 := (Length(b) >= 2 and Length(Set(b)) = 1);
    
    result := "FAIL";
    if t1 and t2 and t3 then result := "PASS"; fi;
    
    # Format
    t1s := "  "; if t1 then t1s := " Y"; fi;
    t2s := "  "; if t2 then t2s := " Y"; fi;
    t3s := "  "; if t3 then t3s := " Y"; fi;
    
    name_padded := names[i];
    while Length(name_padded) < 17 do
        name_padded := Concatenation(name_padded, " ");
    od;
    
    Print(name_padded, " |   ", t1s, "   |   ", t2s, 
          "    |    ", t3s, "    | ", result, "\n");
od;

Print("──────────────────+────────+─────────+──────────+───────\n\n");

Print("=== Summary ===\n\n");
Print("M62: 'All non-abelian factors isomorphic (>=2)' selects SU(3)^3 uniquely\n");
Print("M63: '27 equal-dim branching' selects SU(3)^3 uniquely\n");
Print("T2 alone is sufficient for uniqueness.\n");
Print("T3 alone is sufficient for uniqueness.\n");
Print("T2 AND T3 together: still SU(3)^3 only.\n\n");

Print("=== Analysis complete ===\n");
