import Mathlib
import FluidTuringLean.M50_TubeInvariant

/-!
# Module 55 — GPAC σ 構造 Brick G4e：無限帶橋（`Turing.ListBlank`）⟹ 去掉 `bothNonempty`

**承 M46-M50（玩具 σ = `sigmaRL` + 有限 List 帶 + N 步精確、但條件於兩堆疊恆非空 `hne`）**。
M50 `sigmaRL_iterate_exact` 的**誠實缺口** = `bothNonempty`（有限 List 左端 `L=[]` 無頭可讀 ⟹ 落
fallback、模擬中斷）。G4e = 把有限 `List ℕ` 半帶換成 mathlib **`Turing.ListBlank ℕ`**（eventually-blank
無限半帶、blank = `default:ℕ = 0`），使**每個半帶恆有可讀頭**（blank 讀作 0）⟹ `bothNonempty`
**整條消失**、`gStepRLB` 變**全函數**（無 `| c => c` fallback）、N 步精確模擬**無條件**（只剩良編碼初始 +
轉移表良性 + headroom base）。

## 交付（全顯式、字面相等、零 sorry、標準三公理）

- **`encInf`（★核心★）**：`encTape` 經 `ListBlank.liftOn` 昇到 `ListBlank ℕ → ℝ`；良定義義務 =
  blank-append 不變 `encTape K (a ++ replicate n 0) = encTape K a`
  （`encTape_append` + `encTape_replicate_zero`）。
  純代數、**零實分析**（eventually-blank = 有限和）。橋 `encInf_mk`(=encTape、rfl)/`encInf_default`(=0)/
  `encInf_cons`/**`encInf_head_tail`（★無條件 head/tail 分解★）**。
- **`read_plateau_B`（★去邊界核心★）**：**無條件**（任何 `l`、含 all-blank）頭可讀 + 尾入 `[0,w]`
  （blank 頭 = 0 亦然）——有限版 `read_plateau_of_headroom` 的 `bothNonempty`-free 版。
- 配置層 `GCfgB`（`q:ℕ, L R : ListBlank ℕ`）/ `gEncB` / **`gStepRLB`（全函數、無 fallback）** /
  `wfCfgB` / `digitsLtB` / `gStepRLB_wf`（保良編碼）。
- **`sigmaRL_exact_of_wfB`（★CRUX★）**：`σ(gEncB c) = gEncB(gStepRLB c)` **字面相等、無 plateau 假設、
  無 `bothNonempty`**（`cases move`、`smoothSelect` 挑臂、`encInf_cons`/pop 純代數、與 M49 同結構但 head/tail）。
- **`sigmaRL_iterate_exactB`（★HEADLINE★）**：`σ^[n](gEncB c) = gEncB(gStepRLB^[n] c)` **N 步字面相等、
  無 `hne`**——M50 headline 去掉兩堆疊非空假設。**左端邊界（List 內稟缺陷）消失。**

## ★誠實範圍（禁 overclaim）★

- **仍是玩具、仍非通用機**：`gStepRLB` 是 module-local 玩具步（兩堆疊 = 兩 `ListBlank`、頭固定在 0）；
  **未接** mathlib `Turing.TM0/TM1/TM2` 或主線 M18-33 BitTM，**未**證 undecidability。G4e 去掉的是**帶邊界
  假設**（`bothNonempty`），**非**加上通用性。真通用機 = 另一結構橋（BitTM↔兩堆疊、≈M25+M26+M27 級、
  後續 G6 splice）。
- **倖存假設**：良編碼初始 `wfCfgB`（沿軌道保持、`gStepRLB_iterate_wf`）、轉移表良性 `hQ/hW`
  （`δq<Q, δw<k` = 機器性質、非邊界）、headroom base `(k−1)/(K−1) ≤ w`（如 `K=4k`）、數值 `hk/hkK/hK`。
  **消失**：`bothNonempty`/`hne`。
- **邊際價值**：條件式仍**弱於且冗餘於**主線 M33 無條件不可判定；本磚 = 清償 GPAC 線的一條誠實 caveat、
  非新不可判定結果。**C^∞ 非 analytic**（承 M46-M50）。**G5 全檔 tube = 已證 WALL**（讀方向增益 `K>1`、
  無加權範數收縮、分數暫存器整格 latch 無法清、見 `docs/GPAC_ROADMAP.md`）——本磚**不**碰連續流 robustness。
-/

namespace FluidTuring

open Turing

/-! ## `encTape` blank-append 不變（`encInf` 良定義義務） -/

/-- 全 blank 尾編碼為 0（`encTape K (replicate n 0) = 0`）。 -/
theorem encTape_replicate_zero (K n : ℕ) : encTape K (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ]; simp only [encTape]; rw [ih]; simp

/-- Horner 編碼對 append 拆分（尾巴縮 `K^{|a|}`）。 -/
theorem encTape_append (K : ℕ) (a b : List ℕ) :
    encTape K (a ++ b) = encTape K a + encTape K b / (K : ℝ) ^ a.length := by
  induction a with
  | nil => simp [encTape]
  | cons d ds ih =>
    simp only [List.cons_append, encTape, ih, List.length_cons]; field_simp; ring

/-- **blank-append 不變**（`liftOn` 的良定義義務）：`BlankExtends a b ⟹ encTape K a = encTape K b`。 -/
theorem encTape_blankExtends (K : ℕ) {a b : List ℕ} (h : BlankExtends a b) :
    encTape K a = encTape K b := by
  obtain ⟨n, rfl⟩ := h
  rw [encTape_append, show (default : ℕ) = 0 from rfl, encTape_replicate_zero]; simp

/-! ## `encInf`：無限半帶編碼 -/

/-- **無限半帶（eventually-blank）base-`K` 編碼**：`encTape` 經 `ListBlank.liftOn` 昇（有限和、零實分析）。 -/
noncomputable def encInf (K : ℕ) (l : ListBlank ℕ) : ℝ :=
  l.liftOn (encTape K) (fun _ _ h => encTape_blankExtends K h)

/-- 橋：代表元上 = `encTape`（rfl）。 -/
theorem encInf_mk (K : ℕ) (L : List ℕ) : encInf K (ListBlank.mk L) = encTape K L := rfl

/-- 全 blank 帶編碼為 0。 -/
theorem encInf_default (K : ℕ) : encInf K (default : ListBlank ℕ) = 0 := rfl

/-- Horner cons 遞迴（存活於商）。 -/
theorem encInf_cons (K : ℕ) (d : ℕ) (l : ListBlank ℕ) :
    encInf K (l.cons d) = ((d : ℝ) + encInf K l) / (K : ℝ) := by
  refine l.induction_on fun L => ?_
  rw [ListBlank.cons_mk, encInf_mk, encInf_mk]; rfl

/-- **★無條件 head/tail 分解★**：`encInf K l = (l.head + encInf K l.tail)/K`——**任何** `l`（含 all-blank，
`head = 0`）皆有可讀頭。這是 `bothNonempty` 消失的根源（List 版 `L=[]` 無頭；`ListBlank` 版 blank 頭 = 0）。 -/
theorem encInf_head_tail (K : ℕ) (l : ListBlank ℕ) :
    encInf K l = ((l.head : ℝ) + encInf K l.tail) / (K : ℝ) := by
  conv_lhs => rw [← ListBlank.cons_head_tail l]
  rw [encInf_cons]

/-- 編碼非負。 -/
theorem encInf_nonneg (K : ℕ) (l : ListBlank ℕ) : 0 ≤ encInf K l := by
  refine l.induction_on fun L => ?_; rw [encInf_mk]; exact encTape_nonneg K L

/-! ## 良編碼謂詞 + headroom（無限帶版） -/

/-- 良 digits（無限帶）：每個 index 的符號 `< k`。 -/
def digitsLtB (k : ℕ) (l : ListBlank ℕ) : Prop := ∀ i, l.nth i < k

/-- 代表元橋：`digitsLtB k (mk a) ⟹ digitsLt k a`。 -/
theorem digitsLtB_mk {k : ℕ} {a : List ℕ} (h : digitsLtB k (ListBlank.mk a)) : digitsLt k a := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have := h i
  rwa [ListBlank.nth_mk, List.getI_eq_getElem a hi] at this

/-- headroom（無限帶版）：良 digits ⟹ `encInf K l ≤ (k−1)/(K−1)`（經代表元 + M50 有限版）。 -/
theorem encInf_le_headroom (k K : ℕ) (hk : 1 ≤ k) (hK : 1 < K) (l : ListBlank ℕ)
    (hl : digitsLtB k l) : encInf K l ≤ ((k : ℝ) - 1) / ((K : ℝ) - 1) := by
  revert hl
  refine l.induction_on fun L => ?_
  intro hL
  rw [encInf_mk]
  exact encTape_le_headroom k K hk hK L (digitsLtB_mk hL)

/-- **★去邊界核心：無條件 plateau 讀★**：良 digits 尾 + headroom ⟹ 頭可讀（`head ≤ K·encInf ≤ head+w`）——
**任何** `l`（含 all-blank，`head = 0`），無 `bothNonempty`。 -/
theorem read_plateau_B (k K : ℕ) (hk : 1 ≤ k) (hK : 1 < K) (l : ListBlank ℕ)
    (htail : digitsLtB k l.tail) {w : ℝ} (hw : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w) :
    (l.head : ℝ) ≤ (K : ℝ) * encInf K l ∧ (K : ℝ) * encInf K l ≤ (l.head : ℝ) + w := by
  have hKr : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have key : (K : ℝ) * encInf K l = (l.head : ℝ) + encInf K l.tail := by
    rw [encInf_head_tail]; field_simp
  refine ⟨by rw [key]; linarith [encInf_nonneg K l.tail], ?_⟩
  rw [key]; linarith [encInf_le_headroom k K hk hK l.tail htail, hw]

/-! ## 配置層：全函數玩具步 + 編碼 + 良編碼保持 -/

/-- 無限帶玩具組態：狀態 + 兩 `ListBlank` 半帶（頭固定在 0，`R.head` = 當前讀符）。 -/
structure GCfgB where
  q : ℕ
  L : ListBlank ℕ
  R : ListBlank ℕ

/-- **全函數玩具雙向步（無 fallback）**：讀 `R.head`（blank = 0 亦可）、`q → δq`、寫 `δw`、依 move 平移。
`move=true→右移`（寫入 L 頂、R pop）、`false→左移`（L pop、寫入 R、L.head 回填）。 -/
def gStepRLB (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) (c : GCfgB) : GCfgB :=
  if move c.q c.R.head
  then ⟨δq c.q c.R.head, c.L.cons (δw c.q c.R.head), c.R.tail⟩
  else ⟨δq c.q c.R.head, c.L.tail, (c.R.tail.cons (δw c.q c.R.head)).cons c.L.head⟩

/-- 無限帶組態編碼 `ℝ³`。 -/
noncomputable def gEncB (K : ℕ) (c : GCfgB) : ℝ × ℝ × ℝ :=
  ((c.q : ℝ), encInf K c.L, encInf K c.R)

/-- 良組態（無限帶）：狀態 `< Q`、兩半帶 digits `< k`。 -/
def wfCfgB (Q k : ℕ) (c : GCfgB) : Prop := c.q < Q ∧ digitsLtB k c.L ∧ digitsLtB k c.R

/-- **單步保良編碼**（無限帶）：轉移表良性 `hQ/hW` ⟹ `gStepRLB` 保 `wfCfgB`。 -/
theorem gStepRLB_wf (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k)
    (c : GCfgB) (hc : wfCfgB Q k c) : wfCfgB Q k (gStepRLB δq δw move c) := by
  obtain ⟨hq, hL, hR⟩ := hc
  have hs : c.R.head < k := by have h := hR 0; rwa [ListBlank.nth_zero] at h
  have hl : c.L.head < k := by have h := hL 0; rwa [ListBlank.nth_zero] at h
  have hRt : digitsLtB k c.R.tail :=
    fun i => by have := hR (i + 1); rwa [ListBlank.nth_succ] at this
  have hLt : digitsLtB k c.L.tail :=
    fun i => by have := hL (i + 1); rwa [ListBlank.nth_succ] at this
  unfold gStepRLB
  split
  · -- 右移：⟨δq q s, L.cons (δw q s), R.tail⟩
    refine ⟨hQ c.q c.R.head hq hs, ?_, hRt⟩
    intro i
    cases i with
    | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hW c.q c.R.head hq hs
    | succ j => rw [ListBlank.nth_succ, ListBlank.tail_cons]; exact hL j
  · -- 左移：⟨δq q s, L.tail, (R.tail.cons (δw q s)).cons L.head⟩
    refine ⟨hQ c.q c.R.head hq hs, hLt, ?_⟩
    intro i
    cases i with
    | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hl
    | succ j =>
      rw [ListBlank.nth_succ, ListBlank.tail_cons]
      cases j with
      | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hW c.q c.R.head hq hs
      | succ i2 => rw [ListBlank.nth_succ, ListBlank.tail_cons]; exact hRt i2

/-- **N 步保良編碼**（無限帶）。 -/
theorem gStepRLB_iterate_wf (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k)
    (c : GCfgB) (hc : wfCfgB Q k c) :
    ∀ n : ℕ, wfCfgB Q k ((gStepRLB δq δw move)^[n] c) := by
  intro n
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact gStepRLB_wf δq δw move Q k hQ hW _ ih

/-! ## ★CRUX + HEADLINE：無限帶單步 / N 步精確模擬（無 `bothNonempty`） -/

/-- **★CRUX：無限帶單步 σ 格點字面相等、無 `bothNonempty`★**：`σ(gEncB c) = gEncB(gStepRLB c)`。
`cases move`、`smoothSelect` 挑臂、`encInf_cons`/pop 純代數——與 M49 `sigmaRL_exact` 同結構，唯 head/tail
取代 List cons pattern，故**任何** `c`（含空堆疊 = all-blank）皆成立。plateau 假設由 `read_plateau_B` discharge。 -/
theorem sigmaRL_exact_of_wfB (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (c : GCfgB) (hwf : wfCfgB Q k c) :
    sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w (gEncB K c)
      = gEncB K (gStepRLB δqN δwN moveB c) := by
  obtain ⟨hq, hLwf, hRwf⟩ := hwf
  have hs : c.R.head < k := by have h := hRwf 0; rwa [ListBlank.nth_zero] at h
  have hl : c.L.head < k := by have h := hLwf 0; rwa [ListBlank.nth_zero] at h
  have hRt : digitsLtB k c.R.tail :=
    fun i => by have := hRwf (i + 1); rwa [ListBlank.nth_succ] at this
  have hLt : digitsLtB k c.L.tail :=
    fun i => by have := hLwf (i + 1); rwa [ListBlank.nth_succ] at this
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    linarith
  obtain ⟨hloR, hhiR⟩ := read_plateau_B k K hk hK c.R hRt hwhead
  obtain ⟨hloL, hhiL⟩ := read_plateau_B k K hk hK c.L hLt hwhead
  have hMove : tbl2D (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w (c.q : ℝ) (encInf K c.R)
      = if moveB c.q c.R.head then (1 : ℝ) else 0 :=
    tbl2D_exact _ Q K hw0 hw1 c.q hq c.R.head (lt_of_lt_of_le hs hkK) hloR hhiR
  have hDq : tbl2D (fun a b => (δqN a b : ℝ)) Q K w (c.q : ℝ) (encInf K c.R)
      = (δqN c.q c.R.head : ℝ) :=
    tbl2D_exact _ Q K hw0 hw1 c.q hq c.R.head (lt_of_lt_of_le hs hkK) hloR hhiR
  have hDw : tbl2D (fun a b => (δwN a b : ℝ)) Q K w (c.q : ℝ) (encInf K c.R)
      = (δwN c.q c.R.head : ℝ) :=
    tbl2D_exact _ Q K hw0 hw1 c.q hq c.R.head (lt_of_lt_of_le hs hkK) hloR hhiR
  have hReadR : sfloor K w ((K : ℝ) * encInf K c.R) = (c.R.head : ℝ) :=
    sfloor_exact_on_plateau K hw0 hw1 c.R.head (lt_of_lt_of_le hs hkK) hloR hhiR
  have hReadL : sfloor K w ((K : ℝ) * encInf K c.L) = (c.L.head : ℝ) :=
    sfloor_exact_on_plateau K hw0 hw1 c.L.head (lt_of_lt_of_le hl hkK) hloL hhiL
  have hpopR : (K : ℝ) * encInf K c.R - (c.R.head : ℝ) = encInf K c.R.tail := by
    rw [encInf_head_tail K c.R]; field_simp; ring
  have hpopL : (K : ℝ) * encInf K c.L - (c.L.head : ℝ) = encInf K c.L.tail := by
    rw [encInf_head_tail K c.L]; field_simp; ring
  simp only [sigmaRL, gEncB, gStepRLB]
  rw [hMove, hDq, hDw, hReadR, hReadL]
  cases hmv : moveB c.q c.R.head
  · simp only [Bool.false_eq_true, if_false]
    rw [smoothSelect_left (le_refl (0 : ℝ)), smoothSelect_left (le_refl (0 : ℝ))]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact hpopL
    · rw [encInf_cons, encInf_cons, hpopR]
  · simp only [if_true]
    rw [smoothSelect_right (le_refl (1 : ℝ)), smoothSelect_right (le_refl (1 : ℝ))]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · rw [encInf_cons]
    · exact hpopR

/-- **★HEADLINE：無限帶 N 步精確模擬、無 `hne`★**：`σ^[n](gEncB c) = gEncB(gStepRLB^[n] c)`
**字面相等**——M50 `sigmaRL_iterate_exact` 去掉兩堆疊非空假設（`bothNonempty` 消失）。良編碼初始 +
轉移表良性 + headroom base 即得，對**任意** N。**左端邊界（有限 List 內稟缺陷）永久消失。** -/
theorem sigmaRL_iterate_exactB (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    (hQ : ∀ q s, q < Q → s < k → δqN q s < Q)
    (hW : ∀ q s, q < Q → s < k → δwN q s < k)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (c : GCfgB) (hwf : wfCfgB Q k c) (n : ℕ) :
    (sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w)^[n] (gEncB K c)
      = gEncB K ((gStepRLB δqN δwN moveB)^[n] c) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact sigmaRL_exact_of_wfB δqN δwN moveB Q k K hk hkK hK hw0 hw1 hwhead _
      (gStepRLB_iterate_wf δqN δwN moveB Q k hQ hW c hwf m)

end FluidTuring
