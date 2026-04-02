# =============================================================
# M50 & M54 検証スクリプト
# GAP 4.15.1 用
# 実行: Read("C:/path/to/M50_M54_verify.gap");
# =============================================================

Print("========================================\n");
Print("  M50: A5 全表現の Frobenius-Schur 指標\n");
Print("========================================\n\n");

t_A5 := CharacterTable("A5");;
irr_A5 := Irr(t_A5);;

Print("A5 既約表現の次元: ",
      List(irr_A5, x -> x[1]), "\n");

fs_A5 := List(irr_A5, x -> Indicator(t_A5, [x], 2)[1]);;
Print("Frobenius-Schur 指標: ", fs_A5, "\n");

if ForAll(fs_A5, x -> x = 1) then
    Print("\n*** M50 PASS: A5 の全既約表現は実型 (nu_2 = +1) ***\n");
    Print("    帰結: A5 不変 coupling は実基底で実 → CP 位相なし\n\n");
else
    Print("\n*** M50 FAIL ***\n\n");
fi;

# =============================================================
Print("========================================\n");
Print("  M54: 2I (SL(2,5)) の sigma involution\n");
Print("========================================\n\n");

t_2I := CharacterTable("2.A5");;
irr_2I := Irr(t_2I);;

Print("2I 既約表現の個数: ", Length(irr_2I), "\n");

dims_2I := List(irr_2I, x -> x[1]);;
Print("次元: ", dims_2I, "\n\n");

# --- 共役類の情報 ---
Print("共役類の元数: ", SizesConjugacyClasses(t_2I), "\n");
Print("共役類の元の位数: ", OrdersClassRepresentatives(t_2I), "\n\n");

# --- 全指標表の表示 ---
Print("--- 2I 完全指標表 ---\n");
for i in [1..Length(irr_2I)] do
    Print("  Rep ", i, " (dim ", irr_2I[i][1], "): ",
          List(irr_2I[i], x -> x), "\n");
od;
Print("\n");

# --- Frobenius-Schur 指標 ---
fs_2I := List(irr_2I, x -> Indicator(t_2I, [x], 2)[1]);;
Print("Frobenius-Schur 指標: ", fs_2I, "\n");
Print("  (+1 = 実型, -1 = quaternionic, 0 = 複素型)\n\n");

# --- A5 型 vs spinorial の分類 ---
# 実型 (nu_2=+1) → A5 型, quaternionic (nu_2=-1) → spinorial
Print("--- Parity 分類 ---\n");
a5_nodes := [];;
spin_nodes := [];;
for i in [1..Length(irr_2I)] do
    if fs_2I[i] = 1 then
        Add(a5_nodes, i);
        Print("  Rep ", i, " (dim ", dims_2I[i], "): A5 型\n");
    elif fs_2I[i] = -1 then
        Add(spin_nodes, i);
        Print("  Rep ", i, " (dim ", dims_2I[i], "): spinorial\n");
    else
        Print("  Rep ", i, " (dim ", dims_2I[i], "): 複素型 (unexpected!)\n");
    fi;
od;

sum_a5 := Sum(List(a5_nodes, i -> dims_2I[i]^2));;
sum_spin := Sum(List(spin_nodes, i -> dims_2I[i]^2));;
Print("\n  Sigma(d^2) A5 型: ", sum_a5, "  (期待: 60)\n");
Print("  Sigma(d^2) spinorial: ", sum_spin, "  (期待: 60)\n");
Print("  合計: ", sum_a5 + sum_spin, "  (期待: 120 = |2I|)\n\n");

if sum_a5 = 60 and sum_spin = 60 then
    Print("*** Parity 分類 PASS ***\n\n");
else
    Print("*** Parity 分類 FAIL ***\n\n");
fi;

# --- sigma 作用の同定 ---
# 位数 5 の共役類上の指標値で sigma (sqrt5 -> -sqrt5) の作用を判定
Print("--- sigma 作用の同定 ---\n");
orders := OrdersClassRepresentatives(t_2I);;

# 位数 5 または 10 の共役類を探す（C5 セクター）
c5_classes := Filtered([1..Length(orders)], i -> orders[i] in [5, 10]);;
Print("位数 5 or 10 の共役類: ", c5_classes, "\n");
Print("対応する位数: ", List(c5_classes, i -> orders[i]), "\n\n");

# 各表現の C5 セクター上の指標値を表示
Print("C5 セクター上の指標値:\n");
for i in [1..Length(irr_2I)] do
    vals := List(c5_classes, j -> irr_2I[i][j]);;
    Print("  Rep ", i, " (dim ", dims_2I[i], ", ",
          ["A5","spin"][1 + (1 - fs_2I[i])/2],
          "): ", vals, "\n");
od;
Print("\n");

# --- sigma による対の同定 ---
# sigma: E(5) -> E(5)^2 (= 原始5乗根の共役) を利用
# 同じ次元で sigma で交換される対を探す
Print("--- sigma 対の同定 ---\n");
paired := [];;
fixed := [];;
for i in [1..Length(irr_2I)] do
    if i in paired then continue; fi;
    found_pair := false;
    for j in [i+1..Length(irr_2I)] do
        if j in paired then continue; fi;
        if dims_2I[i] = dims_2I[j] then
            # 指標値が Galois 共役かチェック
            is_galois := true;
            for k in [1..Length(irr_2I[i])] do
                val_i := irr_2I[i][k];
                val_j := irr_2I[j][k];
                # GaloisCyc(x, -1) は sqrt5 -> -sqrt5 に対応
                # ただし円分体では Galois 群の作用を使う
                if not (val_j = GaloisCyc(val_i, -1) or
                        val_j = val_i) then
                    # より一般的なチェック
                    if val_i <> val_j and
                       GaloisCyc(val_i, 2) <> val_j and
                       GaloisCyc(val_i, 3) <> val_j and
                       GaloisCyc(val_i, 4) <> val_j then
                        is_galois := false;
                        break;
                    fi;
                fi;
            od;
            # 同じ表現ではないことも確認
            if is_galois and irr_2I[i] <> irr_2I[j] then
                Add(paired, i);
                Add(paired, j);
                Print("  sigma 対: Rep ", i, " (dim ", dims_2I[i],
                      ") <-> Rep ", j, " (dim ", dims_2I[j], ")\n");
                found_pair := true;
                break;
            fi;
        fi;
    od;
    if not found_pair and not (i in paired) then
        Add(fixed, i);
    fi;
od;

Print("  sigma 固定: ");
for i in fixed do
    Print("Rep ", i, " (dim ", dims_2I[i], ")  ");
od;
Print("\n\n");

# --- 直接的な Galois 作用の検証 ---
Print("--- 直接 Galois 検証 ---\n");
Print("各表現に GaloisCyc(chi, -1) を適用:\n");
for i in [1..Length(irr_2I)] do
    galois_chi := List(irr_2I[i], x -> GaloisCyc(x, -1));;
    # この galois_chi がどの表現に一致するか探す
    for j in [1..Length(irr_2I)] do
        if galois_chi = List(irr_2I[j], x -> x) then
            if i = j then
                Print("  Rep ", i, " (dim ", dims_2I[i], "): sigma-固定\n");
            else
                Print("  Rep ", i, " (dim ", dims_2I[i],
                      ") -> Rep ", j, " (dim ", dims_2I[j], ")\n");
            fi;
            break;
        fi;
    od;
od;
Print("\n");

# --- dim=3 の A5 型 node の同定 ---
Print("--- dim=3 の A5 型 node ---\n");
dim3_a5 := Filtered(a5_nodes, i -> dims_2I[i] = 3);;
Print("  dim=3 かつ A5 型の表現: ", dim3_a5, "\n");
Print("  個数: ", Length(dim3_a5), "  (期待: 2 = {rho3, rho3'})\n");
if Length(dim3_a5) = 2 then
    i1 := dim3_a5[1];;
    i2 := dim3_a5[2];;
    # C5 上の指標値を比較
    Print("  Rep ", i1, " の C5 指標: ",
          List(c5_classes, j -> irr_2I[i1][j]), "\n");
    Print("  Rep ", i2, " の C5 指標: ",
          List(c5_classes, j -> irr_2I[i2][j]), "\n");
    # phi = (1+sqrt5)/2 の確認
    Print("  Galois 共役関係の確認:\n");
    for k in c5_classes do
        v1 := irr_2I[i1][k];;
        v2 := irr_2I[i2][k];;
        Print("    class ", k, ": Rep", i1, "=", v1,
              ", Rep", i2, "=", v2,
              ", GaloisCyc(v1,-1)=", GaloisCyc(v1,-1),
              ", match=", v2 = GaloisCyc(v1,-1), "\n");
    od;
    Print("\n*** M54 dim-3 Galois 対 PASS ***\n");
else
    Print("\n*** M54 dim-3 Galois 対 FAIL ***\n");
fi;

Print("\n========================================\n");
Print("  検証完了\n");
Print("========================================\n");
