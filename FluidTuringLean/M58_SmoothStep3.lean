import Mathlib
import FluidTuringLean.M57_BitTMBridge

/-!
# Module 58 — G6 續：σ-level 光滑提升（3 態 `sigmaRL3` = 顯式 C^∞ 映射模擬 3 態玩具步）

**承 M57（`gStepRL3` = `GCfgB` 的 3 態離散步、`Dir`-based、已證 = `BitTM` 一步）+ M49/M55（2 態
光滑 σ、格點精確、無 `bothNonempty`）**。M57 只給**離散** step 對應；本磚把它提升成**顯式 C^∞
映射** `sigmaRL3 : ℝ³ → ℝ³`，證其在編碼 `gEncB` 下與 M57 的 `gStepRL3` 逐步字面相等——即
**一個光滑映射逐步模擬 3 態玩具 TM**（含 stay 臂，BitTM 用得到）。

## 一句話

M55 的 2 態 `sigmaRL` → 3 態 `sigmaRL3`：`smoothSelect` → `smoothSelect3`（巢狀兩層、grid 精確），
每個帶分量多一條 **stay 臂**（`encInf_cons` 直給、零新代數）。`sigmaRL3_exact_of_wfB` 對接 M57 的
`gStepRL3`（`Dir`-based），使 M57↔M58 鏈**接得起來**。

## 交付（全顯式、字面相等、C^∞、零 sorry、標準三公理）

- **`smoothSelect3 s a b c := smoothSelect (s−1) (smoothSelect s a b) c`**（3 態光滑選、巢狀）+
  `smoothSelect3_zero/_one/_ge_two`（grid `s=0/1/≥2` 精確挑臂）+ `smoothSelect3_contDiff`（joint C^∞）。
- **`dirNat : Dir → ℕ`**（left↦0、stay↦1、right↦2）——把 M57 的 `Dir` 移動編成 σ 讀得到的實數碼。
- **`sigmaRL3`（★3 態光滑 σ★）**：`GCfgB` 的每帶分量 = `smoothSelect3 (讀 move) (左臂) (stay 臂) (右臂)`
  （stay_L = 恆等 `p.2.1`、stay_R = `(δw + pop R)/K` = `encInf(R.tail.cons δw)`）。
- **`sigmaRL3_exact_of_wfB`（★CRUX★）**：`sigmaRL3 (…)(dirNat∘moveD) (gEncB c)`
  `= gEncB(gStepRL3 δq δw moveD c)` **字面相等、無 `bothNonempty`**
  （`cases moveD`、`smoothSelect3` grid 挑臂、`encInf_cons`/pop 純代數）。
- `sigmaRL3_contDiff`（3 態 σ C^∞，`ContDiff.prodMk` + `smoothSelect3_contDiff`）。
- `gStepRL3_wf`/`gStepRL3_iterate_wf`（M57 的 `Dir`-based step 保良編碼；M57 只給模擬定理、未給 wf）。
- **`sigmaRL3_iterate_exactB`（★HEADLINE★）**：`σ3^[n](gEncB c) = gEncB(gStepRL3^[n] c)` **N 步字面相等、
  無 `hne`**——M55 headline 的 3 態版。

## ★誠實範圍（禁 overclaim）★

- **仍未接 undecidability**：本磚交付「光滑映射 = 3 態玩具步」；**未**把 `sigmaRL3` 經 `bitEnc`（M57）+
  `Mtr_halts_iff`（M28）合成 `¬ComputablePred` 結論。那是 G6 最後一步（下個模組：把
  `sigmaRL3_iterate_exactB` 沿 M57 的 `gStepRL3_simulates_BitTM` 拉到 `BitTM.step^[n]`、再接
  `Mtr_halts_iff` 到通用碼停機）。本磚只是把 M57 的離散橋抬到 σ 層。
- **是離散映射、非連續流**：目標仍是「顯式 C^∞ **映射** 的軌道可達性不可判定」，**非**連續 ODE 流
  （連續流升級 = 已證死牆 `M56_G5Wall.lean`、`K>1` 讀增益）。`sigmaRL3` 是裸 ℝ³ 自映射 +
  `Function.iterate`——不需緊空間/懸浮流機器，比 M29/M33 路線簡單。
- **倖存假設**：良編碼初始 `wfCfgB`、轉移表良性 `hQ/hW`、headroom base、數值 `hk/hkK/hK`；**無**
  `bothNonempty`。**C^∞ 非 analytic**（承 M46-M55）。玩具編碼（`Dir` 碼 0/1/2、`K≥3` 由 headroom 保證）。
- **邊際價值**：G6 完工後的 headline 與主線 M33（連續流、無條件）是**不同數學物件**（光滑映射 vs 流），
  皆源自同一 `Mtr_halts_iff` 機器層，不冗餘。
-/

namespace FluidTuring

open Real Turing

/-! ## 3 態光滑選擇 `smoothSelect3`（巢狀兩層 2 態選） -/

/-- **3 態光滑選**：`s≈0→a`、`s≈1→b`、`s≥2→c`（巢狀兩層 `smoothSelect`）。 -/
noncomputable def smoothSelect3 (s a b c : ℝ) : ℝ := smoothSelect (s - 1) (smoothSelect s a b) c

/-- grid `s=0` 精確挑左臂 `a`。 -/
theorem smoothSelect3_zero (a b c : ℝ) : smoothSelect3 0 a b c = a := by
  rw [smoothSelect3, smoothSelect_left (by norm_num), smoothSelect_left (le_refl 0)]

/-- grid `s=1` 精確挑 stay 臂 `b`。 -/
theorem smoothSelect3_one (a b c : ℝ) : smoothSelect3 1 a b c = b := by
  rw [smoothSelect3, smoothSelect_left (by norm_num), smoothSelect_right (le_refl 1)]

/-- grid `s≥2` 精確挑右臂 `c`（比 `s=2` 更泛用）。 -/
theorem smoothSelect3_ge_two {s : ℝ} (h : 2 ≤ s) (a b c : ℝ) : smoothSelect3 s a b c = c := by
  rw [smoothSelect3, smoothSelect_right (by linarith)]

/-- **joint C^∞**：selector + 三臂皆 C^∞ ⟹ `smoothSelect3` C^∞。 -/
theorem smoothSelect3_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {sel a b c : X → ℝ}
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sel)
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => smoothSelect3 (sel x) (a x) (b x) (c x)) := by
  unfold smoothSelect3
  exact smoothSelect_contDiff (hs.sub contDiff_const) (smoothSelect_contDiff hs ha hb) hc

/-! ## `Dir` → 實數碼 + 3 態光滑 σ -/

/-- `Dir` 移動編成 σ 讀得到的實數碼：left↦0、stay↦1、right↦2（對上 `smoothSelect3` 臂序）。 -/
def dirNat : Dir → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

/-- **★3 態光滑 σ:ℝ³→ℝ³★**：每帶分量 = `smoothSelect3 (讀 move) (左臂) (stay 臂) (右臂)`。
L 臂序 = [pop L, 恆等, push]；R 臂序 = [nested, write, pop R]（與 M57 `gStepRL3` 的 left/stay/right 對齊）。 -/
noncomputable def sigmaRL3 (δq δw moveN : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun p =>
    ( tbl2D δq Q K w p.1 p.2.2,
      smoothSelect3 (tbl2D moveN Q K w p.1 p.2.2)
        ((K : ℝ) * p.2.1 - sfloor K w ((K : ℝ) * p.2.1))
        (p.2.1)
        ((tbl2D δw Q K w p.1 p.2.2 + p.2.1) / (K : ℝ)),
      smoothSelect3 (tbl2D moveN Q K w p.1 p.2.2)
        (((sfloor K w ((K : ℝ) * p.2.1))
            + (tbl2D δw Q K w p.1 p.2.2
                + ((K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2))) / (K : ℝ)) / (K : ℝ))
        ((tbl2D δw Q K w p.1 p.2.2
            + ((K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2))) / (K : ℝ))
        ((K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2)) )

/-- **★CRUX：3 態光滑 σ 格點字面相等、無 `bothNonempty`★**：對接 M57 的 `Dir`-based `gStepRL3`
（`moveN := dirNat ∘ moveD`）。`cases moveD`、`smoothSelect3` grid 挑臂、各臂 `encInf_cons`/pop 純代數。 -/
theorem sigmaRL3_exact_of_wfB (δqN δwN : ℕ → ℕ → ℕ) (moveD : ℕ → ℕ → Dir) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (c : GCfgB) (hwf : wfCfgB Q k c) :
    sigmaRL3 (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => (dirNat (moveD a b) : ℝ)) Q K w (gEncB K c)
      = gEncB K (gStepRL3 δqN δwN moveD c) := by
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
  have hMove : tbl2D (fun a b => (dirNat (moveD a b) : ℝ)) Q K w (c.q : ℝ) (encInf K c.R)
      = (dirNat (moveD c.q c.R.head) : ℝ) :=
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
  simp only [sigmaRL3, gEncB, gStepRL3]
  rw [hMove, hDq, hDw, hReadR, hReadL]
  cases hmv : moveD c.q c.R.head with
  | left =>
    simp only [dirNat, Nat.cast_zero]
    rw [smoothSelect3_zero, smoothSelect3_zero]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact hpopL
    · rw [encInf_cons, encInf_cons, hpopR]
  | stay =>
    simp only [dirNat, Nat.cast_one]
    rw [smoothSelect3_one, smoothSelect3_one]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    rw [encInf_cons, hpopR]
  | right =>
    simp only [dirNat, Nat.cast_ofNat]
    rw [smoothSelect3_ge_two (le_refl (2 : ℝ)), smoothSelect3_ge_two (le_refl (2 : ℝ))]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · rw [encInf_cons]
    · exact hpopR

/-- **3 態 σ C^∞**（`ContDiff.prodMk` + `smoothSelect3_contDiff`）。 -/
theorem sigmaRL3_contDiff (δq δw moveN : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaRL3 δq δw moveN Q K w) := by
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D δq Q K w p.1 p.2.2) :=
    (tbl2D_contDiff δq Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hw' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D δw Q K w p.1 p.2.2) :=
    (tbl2D_contDiff δw Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D moveN Q K w p.1 p.2.2) :=
    (tbl2D_contDiff moveN Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hsfL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => sfloor K w ((K : ℝ) * p.2.1)) :=
    (sfloor_contDiff K w).comp (contDiff_const.mul contDiff_snd.fst)
  have hRpop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => (K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2)) :=
    (contDiff_const.mul contDiff_snd.snd).sub
      ((sfloor_contDiff K w).comp (contDiff_const.mul contDiff_snd.snd))
  refine ContDiff.prodMk hq (ContDiff.prodMk ?_ ?_)
  · exact smoothSelect3_contDiff hM
      ((contDiff_const.mul contDiff_snd.fst).sub hsfL)
      contDiff_snd.fst
      ((hw'.add contDiff_snd.fst).div_const K)
  · exact smoothSelect3_contDiff hM
      ((hsfL.add ((hw'.add hRpop).div_const K)).div_const K)
      ((hw'.add hRpop).div_const K)
      hRpop

/-! ## `gStepRL3` 保良編碼（M57 的 `Dir`-based step；M57 只給模擬定理、未給 wf） -/

/-- **單步保良編碼**（3 態 `Dir`）：轉移表良性 `hQ/hW` ⟹ `gStepRL3` 保 `wfCfgB`。 -/
theorem gStepRL3_wf (δq δw : ℕ → ℕ → ℕ) (moveD : ℕ → ℕ → Dir) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k)
    (c : GCfgB) (hc : wfCfgB Q k c) : wfCfgB Q k (gStepRL3 δq δw moveD c) := by
  obtain ⟨hq, hL, hR⟩ := hc
  have hs : c.R.head < k := by have h := hR 0; rwa [ListBlank.nth_zero] at h
  have hl : c.L.head < k := by have h := hL 0; rwa [ListBlank.nth_zero] at h
  have hRt : digitsLtB k c.R.tail :=
    fun i => by have := hR (i + 1); rwa [ListBlank.nth_succ] at this
  have hLt : digitsLtB k c.L.tail :=
    fun i => by have := hL (i + 1); rwa [ListBlank.nth_succ] at this
  have hQ' := hQ c.q c.R.head hq hs
  have hW' := hW c.q c.R.head hq hs
  cases hm : moveD c.q c.R.head with
  | left =>
    simp only [gStepRL3, hm]
    refine ⟨hQ', hLt, ?_⟩
    intro i
    cases i with
    | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hl
    | succ j =>
      rw [ListBlank.nth_succ, ListBlank.tail_cons]
      cases j with
      | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hW'
      | succ i2 => rw [ListBlank.nth_succ, ListBlank.tail_cons]; exact hRt i2
  | stay =>
    simp only [gStepRL3, hm]
    refine ⟨hQ', hL, ?_⟩
    intro i
    cases i with
    | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hW'
    | succ j => rw [ListBlank.nth_succ, ListBlank.tail_cons]; exact hRt j
  | right =>
    simp only [gStepRL3, hm]
    refine ⟨hQ', ?_, hRt⟩
    intro i
    cases i with
    | zero => rw [ListBlank.nth_zero, ListBlank.head_cons]; exact hW'
    | succ j => rw [ListBlank.nth_succ, ListBlank.tail_cons]; exact hL j

/-- **N 步保良編碼**（3 態）。 -/
theorem gStepRL3_iterate_wf (δq δw : ℕ → ℕ → ℕ) (moveD : ℕ → ℕ → Dir) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k)
    (c : GCfgB) (hc : wfCfgB Q k c) :
    ∀ n : ℕ, wfCfgB Q k ((gStepRL3 δq δw moveD)^[n] c) := by
  intro n
  induction n with
  | zero => simpa
  | succ m ih => rw [Function.iterate_succ_apply']; exact gStepRL3_wf δq δw moveD Q k hQ hW _ ih

/-- **★HEADLINE：3 態光滑 σ 的 N 步精確模擬、無 `hne`★**：`σ3^[n](gEncB c) = gEncB(gStepRL3^[n] c)`
**字面相等**——M55 headline 的 3 態版，接 M57 的 `Dir`-based step。 -/
theorem sigmaRL3_iterate_exactB (δqN δwN : ℕ → ℕ → ℕ) (moveD : ℕ → ℕ → Dir) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    (hQ : ∀ q s, q < Q → s < k → δqN q s < Q)
    (hW : ∀ q s, q < Q → s < k → δwN q s < k)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (c : GCfgB) (hwf : wfCfgB Q k c) (n : ℕ) :
    (sigmaRL3 (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => (dirNat (moveD a b) : ℝ)) Q K w)^[n] (gEncB K c)
      = gEncB K ((gStepRL3 δqN δwN moveD)^[n] c) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact sigmaRL3_exact_of_wfB δqN δwN moveD Q k K hk hkK hK hw0 hw1 hwhead _
      (gStepRL3_iterate_wf δqN δwN moveD Q k hQ hW c hwf m)

end FluidTuring
