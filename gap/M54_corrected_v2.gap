# =============================================================
# M54 corrected v2: sigma = GaloisCyc(x, 2)
# GAP 4.15.1
# =============================================================

Print("========================================\n");
Print("  M54 corrected: sigma = GaloisCyc(x, 2)\n");
Print("========================================\n\n");

# --- sqrt(5) confirmation ---
sqrt5_cyc := E(5) + E(5)^4 - E(5)^2 - E(5)^3;;
Print("sqrt(5) = ", sqrt5_cyc, "\n");
Print("GaloisCyc(sqrt5, 2) = ", GaloisCyc(sqrt5_cyc, 2), "\n");
Print("-sqrt(5) = ", -sqrt5_cyc, "\n");
Print("match: ", GaloisCyc(sqrt5_cyc, 2) = -sqrt5_cyc, "\n\n");

# --- phi and -1/phi ---
phi_cyc := -E(5)^2 - E(5)^3;;
neg_inv_phi := -E(5) - E(5)^4;;
Print("phi = ", phi_cyc, "\n");
Print("-1/phi = ", neg_inv_phi, "\n");
Print("sigma(phi) = ", GaloisCyc(phi_cyc, 2), "\n");
Print("sigma(phi) = -1/phi ? ", GaloisCyc(phi_cyc, 2) = neg_inv_phi, "\n");
Print("sigma(-1/phi) = phi ? ", GaloisCyc(neg_inv_phi, 2) = phi_cyc, "\n\n");

# --- 2I character table ---
t_2I := CharacterTable("2.A5");;
irr_2I := Irr(t_2I);;
dims := List(irr_2I, x -> x[1]);;
fs := List(irr_2I, x -> Indicator(t_2I, [x], 2)[1]);;

# --- sigma action ---
Print("--- sigma action on 9 irreps ---\n\n");

sigma_map := [];;
for i in [1..Length(irr_2I)] do
    sigma_chi := List(irr_2I[i], x -> GaloisCyc(x, 2));;
    target := 0;;
    for j in [1..Length(irr_2I)] do
        if sigma_chi = List(irr_2I[j], x -> x) then
            target := j;
            break;
        fi;
    od;
    Add(sigma_map, target);
    if i = target then
        Print("  Rep ", i, " (dim ", dims[i], "): FIXED\n");
    else
        Print("  Rep ", i, " (dim ", dims[i],
              ") --> Rep ", target, " (dim ", dims[target], ")\n");
    fi;
od;

Print("\nsigma permutation: ", sigma_map, "\n\n");

# --- involution check ---
is_involution := true;;
for i in [1..Length(sigma_map)] do
    if sigma_map[sigma_map[i]] <> i then
        Print("  FAIL at Rep ", i, "\n");
        is_involution := false;
    fi;
od;
Print("sigma^2 = id: ", is_involution, "\n\n");

# --- fixed points and transpositions ---
fixed_pts := Filtered([1..9], i -> sigma_map[i] = i);;
transpositions := [];;
for i in [1..9] do
    if sigma_map[i] > i then
        Add(transpositions, [i, sigma_map[i]]);
    fi;
od;

Print("Fixed points: ", fixed_pts, "\n");
Print("  dims: ", List(fixed_pts, i -> dims[i]), "\n");
Print("  FS:   ", List(fixed_pts, i -> fs[i]), "\n");
Print("Transpositions: ", transpositions, "\n");
for pair in transpositions do
    Print("  Rep ", pair[1], " (dim ", dims[pair[1]], ", FS=", fs[pair[1]],
          ") <-> Rep ", pair[2], " (dim ", dims[pair[2]], ", FS=", fs[pair[2]], ")\n");
od;
Print("\n");

# --- summary table ---
Print("--- Summary Table ---\n\n");
Print("Rep  dim  FS   type        sigma\n");
Print("---  ---  ---  ----------  --------\n");
for i in [1..9] do
    if fs[i] = 1 then
        Print(" ", i, "    ", dims[i], "    ", fs[i], "   A5_type    ");
    else
        Print(" ", i, "    ", dims[i], "   ", fs[i], "   spinorial  ");
    fi;
    if sigma_map[i] = i then
        Print("FIXED\n");
    else
        Print("--> Rep ", sigma_map[i], "\n");
    fi;
od;
Print("\n");

# --- dim=3 A5-type Galois pair ---
Print("--- dim=3 A5-type Galois pair ---\n\n");
orders := OrdersClassRepresentatives(t_2I);;
c5_classes := Filtered([1..Length(orders)], i -> orders[i] = 5);;
Print("Order-5 classes: ", c5_classes, "\n");

dim3_a5 := Filtered([1..9], i -> dims[i] = 3 and fs[i] = 1);;
Print("dim=3 A5-type reps: ", dim3_a5, "\n");

if Length(dim3_a5) = 2 then
    r1 := dim3_a5[1];;
    r2 := dim3_a5[2];;
    for k in c5_classes do
        v1 := irr_2I[r1][k];;
        v2 := irr_2I[r2][k];;
        Print("  class ", k, ": Rep", r1, "=", v1);
        if v1 = phi_cyc then Print(" [=phi]"); fi;
        if v1 = neg_inv_phi then Print(" [=-1/phi]"); fi;
        Print(", Rep", r2, "=", v2);
        if v2 = phi_cyc then Print(" [=phi]"); fi;
        if v2 = neg_inv_phi then Print(" [=-1/phi]"); fi;
        Print(", sigma(v1)=v2? ", GaloisCyc(v1, 2) = v2, "\n");
    od;
    Print("\nsigma swaps Rep", r1, " <-> Rep", r2, ": ",
          sigma_map[r1] = r2, "\n");
fi;

# --- M49 consistency ---
Print("\n--- M49 consistency ---\n\n");
a5_dims := SortedList(List(Filtered([1..9], i -> fs[i]=1), i -> dims[i]));;
sp_dims := SortedList(List(Filtered([1..9], i -> fs[i]=-1), i -> dims[i]));;
Print("A5-type dims (sorted): ", a5_dims, "  expect [1,3,3,4,5]: ",
      a5_dims = [1,3,3,4,5], "\n");
Print("Spin dims (sorted):    ", sp_dims, "  expect [2,2,4,6]: ",
      sp_dims = [2,2,4,6], "\n");
Print("Sum A5: ", Sum(List(a5_dims, x->x^2)), "  expect 60: ",
      Sum(List(a5_dims, x->x^2)) = 60, "\n");
Print("Sum spin: ", Sum(List(sp_dims, x->x^2)), "  expect 60: ",
      Sum(List(sp_dims, x->x^2)) = 60, "\n");

# --- final verdict ---
Print("\n========================================\n");
Print("  FINAL VERDICT\n");
Print("========================================\n\n");

pass_all := true;;
if not is_involution then pass_all := false; fi;
Print("1. sigma^2 = id:              ", is_involution, "\n");

chk2 := Length(transpositions) = 2;;
if not chk2 then pass_all := false; fi;
Print("2. exactly 2 transpositions:  ", chk2, "\n");

chk3 := Length(fixed_pts) = 5;;
if not chk3 then pass_all := false; fi;
Print("3. exactly 5 fixed points:    ", chk3, "\n");

chk4 := (Length(dim3_a5) = 2 and sigma_map[dim3_a5[1]] = dim3_a5[2]);;
if not chk4 then pass_all := false; fi;
Print("4. dim-3 A5 pair swapped:     ", chk4, "\n");

chk5 := a5_dims = [1,3,3,4,5] and sp_dims = [2,2,4,6];;
if not chk5 then pass_all := false; fi;
Print("5. M49 dims consistent:       ", chk5, "\n");

if pass_all then
    Print("\n*** M54 PASS (all checks) ***\n");
else
    Print("\n*** M54 FAIL ***\n");
fi;
Print("\n");
