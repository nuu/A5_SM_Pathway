# B4_node_removal.gap
# Affine Ê₈ McKay graph: single-node removal → residual Dynkin type
# 
# McKay graph of 2I (binary icosahedral) = affine Ê₈
# Nodes labeled 0–8 with marks (= dim of 2I irrep):
#   Node 0: mark 1 (ρ₁, affine)
#   Node 8: mark 2 (spinorial)  
#   Node 7: mark 3 (ρ₃')
#   Node 6: mark 4 (spinorial)
#   Node 5: mark 5 (ρ₅)
#   Node 4: mark 6 (spinorial)
#   Node 3: mark 4 (ρ₄)
#   Node 1: mark 2 (spinorial)
#   Node 2: mark 3 (ρ₃)
#
# Adjacency (McKay graph):
#   0 — 8 — 7 — 6 — 5 — 4 — 3 — 1
#                           |
#                           2
#
# Date: 2026-03-29

Print("=== B4: Affine Ê₈ single-node removal analysis ===\n\n");

# ─── 1. Define the adjacency matrix (9×9, 0-indexed → 1-indexed) ───
# Mapping: node k → index k+1 in GAP

adj := NullMat(9, 9);

# Edge list (0-indexed node pairs)
edges := [[0,8], [8,7], [7,6], [6,5], [5,4], [4,3], [3,1], [4,2]];

for e in edges do
    adj[e[1]+1][e[2]+1] := 1;
    adj[e[2]+1][e[1]+1] := 1;
od;

# Marks (dimensions of 2I irreps)
marks := [1, 2, 3, 4, 5, 6, 4, 2, 3];
# Index:  0  1  2  3  4  5  6  7  8  (but stored as 1-9 in GAP)

# Labels
labels := ["rho1(affine)", "spin", "rho3", "rho4", "spin", 
           "rho5", "spin", "rho3'", "spin"];

Print("Mark sum = ", Sum(marks), " (should be 30 = Coxeter number)\n\n");

# ─── 2. Connected components after node removal ───

ConnectedComponents := function(adjmat, nodeset)
    # Find connected components of the subgraph induced by nodeset
    local visited, components, comp, queue, v, w;
    visited := [];
    components := [];
    for v in nodeset do
        if not v in visited then
            comp := [];
            queue := [v];
            while Length(queue) > 0 do
                w := queue[1];
                Remove(queue, 1);
                if not w in visited then
                    Add(visited, w);
                    Add(comp, w);
                    for v in nodeset do
                        if not v in visited and adjmat[w][v] = 1 then
                            Add(queue, v);
                        fi;
                    od;
                fi;
            od;
            Sort(comp);
            Add(components, comp);
        fi;
    od;
    return components;
end;

# ─── 3. Classify Dynkin diagram type ───

ClassifyDynkin := function(adjmat, nodes)
    # Given a connected subgraph, classify its Dynkin type
    local n, degrees, max_deg, branch_nodes, arms, d, nbrs, arm, 
          current, prev, a;
    
    n := Length(nodes);
    if n = 0 then return "empty"; fi;
    if n = 1 then return "A1"; fi;
    
    # Compute degree of each node within the subgraph
    degrees := [];
    for d in nodes do
        degrees[d] := 0;
        for a in nodes do
            if adjmat[d][a] = 1 then
                degrees[d] := degrees[d] + 1;
            fi;
        od;
    od;
    
    max_deg := Maximum(List(nodes, d -> degrees[d]));
    
    # Case 1: max degree <= 2 → chain → A_n
    if max_deg <= 2 then
        return Concatenation("A", String(n));
    fi;
    
    # Case 2: max degree = 3 → exactly one trivalent node
    if max_deg = 3 then
        branch_nodes := Filtered(nodes, d -> degrees[d] = 3);
        if Length(branch_nodes) <> 1 then
            return Concatenation("UNKNOWN(", String(n), " nodes, multiple branches)");
        fi;
        
        # Find arm lengths from branch point
        d := branch_nodes[1];
        nbrs := Filtered(nodes, a -> a <> d and adjmat[d][a] = 1);
        arms := [];
        for a in nbrs do
            # Follow chain from branch point through a
            arm := 0;
            current := a;
            prev := d;
            while current in nodes do
                arm := arm + 1;
                # Find next node
                nbrs := Filtered(nodes, 
                    w -> w <> prev and adjmat[current][w] = 1);
                if Length(nbrs) = 0 then break; fi;
                prev := current;
                current := nbrs[1];
            od;
            Add(arms, arm);
        od;
        Sort(arms);  # ascending
        
        # Classify by arms (sorted ascending: [p, q, r] with p ≤ q ≤ r)
        if arms[1] = 1 and arms[2] = 1 then
            # D_{n}: arms [1, 1, n-3]
            return Concatenation("D", String(n));
        elif arms = [1, 2, 2] then
            return "E6";
        elif arms = [1, 2, 3] then
            return "E7";
        elif arms = [1, 2, 4] then
            return "E8";
        else
            return Concatenation("UNKNOWN(arms=", String(arms), ")");
        fi;
    fi;
    
    return Concatenation("UNKNOWN(max_deg=", String(max_deg), ")");
end;

# ─── 4. Main computation: remove each node ───

Print("Single-node removal results:\n");
Print("─────────────────────────────────────────────────────\n");
Print("Removed | Mark | Rep        | Residual type\n");
Print("─────────────────────────────────────────────────────\n");

for removed in [0..8] do
    remaining := Filtered([1..9], i -> i <> removed + 1);
    comps := ConnectedComponents(adj, remaining);
    
    types := [];
    for comp in comps do
        Add(types, ClassifyDynkin(adj, comp));
    od;
    Sort(types);
    
    result := JoinStringsWithSeparator(types, " + ");
    
    rank_sum := Sum(List(comps, Length));
    
    Print("  ", removed, "     |  ", marks[removed+1], "   | ", 
          labels[removed+1]);
    # Pad to align
    for a in [1..15 - Length(labels[removed+1])] do Print(" "); od;
    Print("| ", result, "\n");
od;

Print("─────────────────────────────────────────────────────\n\n");

# ─── 5. Verification: mark check ───

Print("=== Verification ===\n\n");

# Check: sum of marks = 30
Print("Sum of marks = ", Sum(marks), " (expect 30)\n");

# Check: adjacency matrix is symmetric
sym := true;
for a in [1..9] do
    for d in [1..9] do
        if adj[a][d] <> adj[d][a] then sym := false; fi;
    od;
od;
Print("Adjacency symmetric: ", sym, "\n");

# Check: total edges
total_edges := Sum(List([1..9], i -> Sum(adj[i]))) / 2;
Print("Total edges = ", total_edges, " (expect 8 for tree on 9 nodes)\n");

# ─── 6. E₈ Cartan matrix verification ───

Print("\n=== E₈ Cartan matrix (finite, nodes 1-8 in McKay numbering) ===\n");
Print("(Remove affine node 0, relabel remaining as finite E₈)\n\n");

# Extract 8×8 submatrix for finite E₈ (nodes 1-8 → indices 2-9)
finite_nodes := [2..9];  # GAP indices for McKay nodes 1-8
cartan := NullMat(8, 8);
for a in [1..8] do
    cartan[a][a] := 2;
    for d in [1..8] do
        if a <> d and adj[finite_nodes[a]][finite_nodes[d]] = 1 then
            cartan[a][d] := -1;
        fi;
    od;
od;

Print("Cartan matrix:\n");
for a in [1..8] do
    Print("  ", cartan[a], "\n");
od;

# Determinant
Print("\ndet(Cartan) = ", DeterminantMat(cartan), " (expect 1 for E₈)\n");

# Characteristic polynomial
x := Indeterminate(Rationals, "x");
char_poly := CharacteristicPolynomial(cartan, x);
Print("Characteristic polynomial = ", char_poly, "\n");

# Eigenvalues (as roots of char poly)
Print("\n=== Eigenvalue structure ===\n");
Print("Char poly coefficients: ", CoefficientsOfUnivariatePolynomial(char_poly), "\n");

# ─── 7. Multi-node removal: trinification chain ───

Print("\n=== Key breaking chains ===\n\n");

# Chain 1: E₈ → E₆ × A₂ (remove node 7)
Print("Step 1: Remove node 7 (ρ₃') → ");
rem1 := Filtered([1..9], i -> i <> 8);  # node 7 = index 8
comps1 := ConnectedComponents(adj, rem1);
types1 := List(comps1, c -> ClassifyDynkin(adj, c));
Print(JoinStringsWithSeparator(types1, " + "), "\n");

# Chain 2: From E₆ part, further removals toward SU(3)³
Print("\nE₆ nodes (from Step 1): ");
e6_comp := First(comps1, c -> Length(c) = 6);
e6_nodes_mckay := List(e6_comp, i -> i - 1);
Print(e6_nodes_mckay, "\n");

# Try removing each node from E₆ part
Print("\nE₆ single-node removals:\n");
for rem in e6_comp do
    sub := Filtered(e6_comp, i -> i <> rem);
    sub_comps := ConnectedComponents(adj, sub);
    sub_types := List(sub_comps, c -> ClassifyDynkin(adj, c));
    Print("  Remove McKay node ", rem-1, " (mark ", marks[rem], 
          "): ", JoinStringsWithSeparator(sub_types, " + "), "\n");
od;

Print("\n=== B4 analysis complete ===\n");
