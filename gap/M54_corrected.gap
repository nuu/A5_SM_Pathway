# =============================================================
# M54 修正版：sigma = GaloisCyc(x, 2) で直接検証
# GAP 4.15.1 用
# =============================================================
# 
# 背景：
#   Q(zeta_5) における Galois 群は (Z/5Z)* = {1, 2, 3, 4}
#   sigma: sqrt(5) -> -sqrt(5) は zeta_5 -> zeta_5^2 に対応
#   (∵ sqrt(5) = zeta_5 + zeta_5^4 - zeta_5^2 - zeta_5^3)
#   GaloisCyc(x, -1) は複素共役 (zeta -> zeta^{-1}) であり
#   sqrt(5) を不変に保つので sigma ではない
# =============================================================

Print("========================================\n");
Print("  M54 修正版: sigma = GaloisCyc(x, 2)\n");
Print("========================================\n\n");

# --- sqrt(5) の表現確認 ---
sqrt5_cyc := E(5) + E(5)^4 - E(5)^2 - E(5)^3;;
Print("sqrt(5) in cyclotomic form: ", sqrt5_cyc, "\n");
Print("GaloisCyc(sqrt5, 2) = ", GaloisCyc(sqrt5_cyc, 2), "\n");
Print("期待: -sqrt(5) = ", -sqrt5_cyc, "\n");
Print("一致: ", GaloisCyc(sqrt5_cyc, 2) = -sqrt5_cyc, "\n\n");

# --- phi と -1/phi の確認 ---
phi_cyc := -E(5)^2 - E(5)^3;;  # (1+sqrt5)/2
neg_inv_phi := -E(5) - E(5)^4;; # (1-sqrt5)/2 = -1/phi
Print("phi = (1+sqrt5)/2 = ", phi_cyc, "\n");
Print("-1/phi = (1-sqrt5)/2 = ", neg_inv_phi, "\n");
Print("sigma(phi) = GaloisCyc(phi, 2) = ", GaloisCyc(phi_cyc, 2), "\n");
Print("sigma(phi) = -1/phi ? ", GaloisCyc(phi_cyc, 2) = neg_inv_phi, "\n");
Print("sigma(-1/phi) = phi ? ", GaloisCyc(neg_inv_phi, 2) = phi_cyc, "\n\n");

# --- 2I の指標表 ---
t_2I := CharacterTable("2.A5");;
irr_2I := Irr(t_2I);;
dims := List(irr_2I, x -> x[1]);;

# --- 正しい sigma 作用の検証 ---
Print("--- sigma = GaloisCyc(chi, 2) の作用 ---\n\n");

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
        Print("  Rep ", i, " (dim ", dims[i], "): sigma-固定\n");
    else
        Print("  Rep ", i, " (dim ", dims[i],
              ") --sigma--> Rep ", target, " (dim ", dims[target], ")\n");
    fi;
od;

Print("\nsigma 置換: ", sigma_map, "\n\n");

# --- involution 検証 ---
Print("--- involution 検証 (sigma^2 = id) ---\n");
is_involution := true;;
for i in [1..Length(sigma_map)] do
    if sigma_map[sigma_map[i]] <> i then
        Print("  FAIL at Rep ", i, "\n");
        is_involution := false;
    fi;
od;
if is_involution then
    Print("  sigma^2 = id: PASS\n\n");
else
    Print("  sigma^2 = id: FAIL\n\n");
fi;

# --- 固定点と transposition の集計 ---
fixed_pts := Filtered([1..9], i -> sigma_map[i] = i);;
transpositions := [];;
for i in [1..9] do
    if sigma_map[i] > i then
        Add(transpositions, [i, sigma_map[i]]);
    fi;
od;

Print("固定点: ", fixed_pts, "\n");
Print("  次元: ", List(fixed_pts, i -> dims[i]), "\n");
Print("transpositions: ", transpositions, "\n");
for pair in transpositions do
    Print("  Rep ", pair[1], " (dim ", dims[pair[1]],
          ") <-> Rep ", pair[2], " (dim ", dims[pair[2]], ")\n");
od;
Print("\n");

# --- Frobenius-Schur による型分類 ---
fs := List(irr_2I, x -> Indicator(t_2I, [x], 2)[1]);;

Print("--- sigma 作用 + 型分類の統合 ---\n\n");
Print("| Rep | dim | FS | 型        | sigma    |\n");
Print("|-----|-----|----|-----------|----------|\n");
for i in [1..9] do
    typ := "??";;
    if fs[i] = 1 then typ := "A5 型    "; fi;
    if fs[i] = -1 then typ := "spinorial"; fi;
    sig := "??";;
    if sigma_map[i] = i then
        sig := Concatenation("固定");
    else
        sig := Concatenation("-> Rep ", String(sigma_map[i]));
    fi;
    Print("|  ", i, "  |  ", dims[i], "  | ", fs[i],
          "  | ", typ, " | ", sig, "\n");
od;
Print("\n");

# --- dim=3 Galois 対の指標値詳細 ---
Print("--- dim=3 Galois 対の C5 指標値 ---\n\n");
orders := OrdersClassRepresentatives(t_2I);;
c5_classes := Filtered([1..Length(orders)], i -> orders[i] = 5);;
Print("位数 5 の共役類: ", c5_classes, "\n");

dim3_a5 := Filtered([1..9], i -> dims[i] = 3 and fs[i] = 1);;
if Length(dim3_a5) = 2 then
    r1 := dim3_a5[1];;
    r2 := dim3_a5[2];;
    Print("\nRep ", r1, " (候補 rho3/rho3'):\n");
    for k in c5_classes do
        v := irr_2I[r1][k];;
        Print("  class ", k, ": ", v);
        if v = phi_cyc then Print(" = phi"); fi;
        if v = neg_inv_phi then Print(" = -1/phi"); fi;
        Print("\n");
    od;
    Print("\nRep ", r2, " (候補 rho3'/rho3):\n");
    for k in c5_classes do
        v := irr_2I[r2][k];;
        Print("  class ", k, ": ", v);
        if v = phi_cyc then Print(" = phi"); fi;
        if v = neg_inv_phi then Print(" = -1/phi"); fi;
        Print("\n");
    od;

    # sigma で交換されるか
    Print("\nRep ", r1, " と Rep ", r2, " は sigma で交換される: ",
          sigma_map[r1] = r2 and sigma_map[r2] = r1, "\n");

    # rho3 の同定: C5+ 上で phi を取る方
    # (どちらの C5 class が C5+ かは convention だが、
    #  一方で phi, 他方で -1/phi を取ることが本質)
    Print("\n同定:\n");
    for k in c5_classes do
        if irr_2I[r1][k] = phi_cyc then
            Print("  Rep ", r1, " は class ", k,
                  " で phi → rho3 と同定\n");
            Print("  Rep ", r2, " は rho3' と同定\n");
            break;
        elif irr_2I[r1][k] = neg_inv_phi then
            Print("  Rep ", r1, " は class ", k,
                  " で -1/phi → rho3' と同定\n");
            Print("  Rep ", r2, " は rho3 と同定\n");
            break;
        fi;
    od;
fi;

# --- M49 との整合性検証 ---
Print("\n--- M49 整合性 ---\n\n");
Print("A5 型 nodes: dims = ", List(Filtered([1..9],
      i -> fs[i]=1), i -> dims[i]), "\n");
Print("期待: [1, 3, 3, 4, 5] (= rho1, rho3, rho3', rho4, rho5)\n");
a5_dims := SortedList(List(Filtered([1..9],
            i -> fs[i]=1), i -> dims[i]));;
Print("ソート済: ", a5_dims, "\n");
Print("一致: ", a5_dims = [1, 3, 3, 4, 5], "\n\n");

Print("spinorial nodes: dims = ", List(Filtered([1..9],
      i -> fs[i]=-1), i -> dims[i]), "\n");
Print("期待: [2, 2, 4, 6]\n");
sp_dims := SortedList(List(Filtered([1..9],
            i -> fs[i]=-1), i -> dims[i]));;
Print("ソート済: ", sp_dims, "\n");
Print("一致: ", sp_dims = [2, 2, 4, 6], "\n\n");

# --- 最終判定 ---
Print("========================================\n");
Print("  最終判定\n");
Print("========================================\n\n");

pass_all := true;;

# 1. sigma は involution か
if not is_involution then pass_all := false; fi;
Print("sigma^2 = id: ", is_involution, "\n");

# 2. transposition は正確に 2 組か
if Length(transpositions) <> 2 then pass_all := false; fi;
Print("transposition 数 = 2: ", Length(transpositions) = 2, "\n");

# 3. dim-3 A5 型が sigma で交換されるか
dim3_swapped := (Length(dim3_a5) = 2 and
                 sigma_map[dim3_a5[1]] = dim3_a5[2]);;
if not dim3_swapped then pass_all := false; fi;
Print("dim-3 A5 型 Galois 対: ", dim3_swapped, "\n");

# 4. 固定点は 5 個か
if Length(fixed_pts) <> 5 then pass_all := false; fi;
Print("固定点 = 5: ", Length(fixed_pts) = 5, "\n");

if pass_all then
    Print("\n*** M54 PASS (全検証項目合格) ***\n");
else
    Print("\n*** M54 FAIL ***\n");
fi;

Print("\n========================================\n");
Print("  検証完了\n");
Print("========================================\n");
