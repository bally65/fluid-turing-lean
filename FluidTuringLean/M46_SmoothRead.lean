import Mathlib
import FluidTuringLean.M44_SmoothSelect

/-!
# Module 46 — GPAC σ 構造 Brick G2：smooth 讀符號（exact-on-plateau 階梯）

**方向三 GPAC 線**（unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。G2 = **讀符號原語**：光滑 `sfloor`，
於 gap 編碼的格點 plateau 上**字面精確**等於符號（`⌊k·y⌋`），且處處 C^∞。

## ★診斷更正：G2 不是「smooth floor」（那才真不可能）★

不需要 smooth floor（不連續、不可能）。需要的是 **gap 編碼格點上精確的光滑階梯**：符號 `j₀` 編在
**plateau** `[j₀, j₀+w]`（寬 `w`），相鄰 plateau 間留 **gap** 讓 `smoothTransition` 光滑爬升。用 M41/M44
已反覆用的 exact-plateau 兩引理（`smoothTransition.zero_of_nonpos` / `one_of_one_le`）疊出——工作量 ≈ M41 等級。

## 構造（延續 M39-45「顯式函數 + HasDerivAt」紀律）

- 單階 `sstep c g u := smoothTransition((u−c)/g)`（跨 gap `[c, c+g]` 由 0 升到 1）；
- 階梯 `sfloor k w u := ∑_{j<k−1} sstep(j+w, 1−w, u)`；plateau `j = [j, j+w]`、gap `j = [j+w, j+1]`。
- **`sfloor_exact_on_plateau`（★CRUX★）**：`u ∈ [j₀, j₀+w] ⟹ sfloor = j₀` **字面相等**（非 ε）——
  plateau 上每項 `sstep = (j<j₀ ? 1 : 0)`（精確），和 `= |{j<j₀}| = j₀`。這正是 G4 需要的 exact-on-lattice 讀。
- `sfloor_contDiff`（有限和 of C^∞）+ `sfloor_hasDerivAt`（ODE 場可用的顯式導數）。

## ★誠實範圍（禁 overclaim）★

- **C^∞、非 analytic**：`smoothTransition = expNegInvGlue` 是 **C^∞ 但非解析**（`ContDiff ℝ ⊤` 現指
  analytic ω，`smoothTransition` 對它為假；只 `ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)` = C^∞）。**本線目標 =
  C^∞ 光滑流**（同 M13 起全線）；**若** Brick 6 真目標是**嚴格 GPAC（analytic 向量場）**，則本 exact-on-lattice
  是**不可能定理**（analytic 區間常值 ⟹ 全域常值 ⟹ 無法區分符號），整個 M40-46 scaffold 離題。此語意分歧
  是 Brick 6 之上的**真決策點**，非 G2 缺陷。
- `sfloor` **只是** σ 的 read sub-brick——**不** decode 全組態、**不**判定 halting、**不**建 tube 不變式。
  **禁**從 G2 宣稱線三 undecidability（守 M44/M45 紀律）。
- **真牆在下游、與 G2 正交**（不因 G2 打通而移動）：φ 自治化（M41 已標、多月）、真不連續 σ 的全域
  tube 不變式（Wall A/B，`BRICK6_DECISION` §2）、GPAC 嚴格 analytic 語意（上）、邊際價值（條件式仍弱於
  且冗餘於主線 M33 無條件、`BRICK6_DECISION` §3C）。**左緣 margin** 脆弱（base `2m` 單側；`tail≈0` 時
  符號坐 plateau 左界、負向誤差誤讀）= 編碼設計精修（base `4m` 或置中編碼），下游 G4/G5 須顧。
-/

namespace FluidTuring

open Real

/-- **單階原子**：`sstep c g u = smoothTransition((u−c)/g)`，跨 gap `[c, c+g]` 由 0 升到 1。 -/
noncomputable def sstep (c g u : ℝ) : ℝ := Real.smoothTransition ((u - c) / g)

/-- gap 前恰 0（`u ≤ c`）。 -/
theorem sstep_zero {c g u : ℝ} (hg : 0 < g) (h : u ≤ c) : sstep c g u = 0 := by
  rw [sstep]
  apply Real.smoothTransition.zero_of_nonpos
  rw [div_le_iff₀ hg]; linarith

/-- gap 後恰 1（`c + g ≤ u`）。 -/
theorem sstep_one {c g u : ℝ} (hg : 0 < g) (h : c + g ≤ u) : sstep c g u = 1 := by
  rw [sstep]
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hg]; linarith

/-- 單階 C^∞（`smoothTransition` ∘ 仿射）。 -/
theorem sstep_contDiff (c g : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sstep c g) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

/-- 單階顯式導數。 -/
theorem sstep_hasDerivAt (c g u : ℝ) (_hg : g ≠ 0) :
    HasDerivAt (sstep c g)
      (deriv Real.smoothTransition ((u - c) / g) * (1 / g)) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u - c) / g) (1 / g) u := by
    simpa using ((hasDerivAt_id u).sub_const c).div_const g
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((u - c) / g)) ((u - c) / g) :=
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by norm_num)).hasDerivAt
  exact h2.comp u h1

/-- **smooth 讀符號階梯**：符號 `j₀` 編在 plateau `[j₀, j₀+w]`；相鄰間留 gap。 -/
noncomputable def sfloor (k : ℕ) (w u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k - 1), sstep ((j : ℝ) + w) (1 - w) u

/-- **★CRUX：exact-on-plateau★**：`u ∈ [j₀, j₀+w]`（`j₀ < k`、`0<w<1`）⟹ `sfloor = j₀` **字面相等**。
= G4 需要的格點精確讀。plateau 上每項恰 `(j<j₀ ? 1 : 0)`，和 `= |{j<j₀}| = j₀`。 -/
theorem sfloor_exact_on_plateau (k : ℕ) {w : ℝ} (_hw0 : 0 < w) (hw1 : w < 1) (j₀ : ℕ)
    (hj₀ : j₀ < k) {u : ℝ} (hlo : (j₀ : ℝ) ≤ u) (hhi : u ≤ (j₀ : ℝ) + w) :
    sfloor k w u = (j₀ : ℝ) := by
  rw [sfloor]
  have hg : (0 : ℝ) < 1 - w := by linarith
  have hterm : ∀ j ∈ Finset.range (k - 1),
      sstep ((j : ℝ) + w) (1 - w) u = if j < j₀ then (1 : ℝ) else 0 := by
    intro j _
    by_cases hj : j < j₀
    · rw [if_pos hj]
      apply sstep_one hg
      have hjj : (j : ℝ) + 1 ≤ (j₀ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
      linarith
    · rw [if_neg hj]
      apply sstep_zero hg
      have hjj : (j₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.le_of_not_lt hj
      linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  have hfilter : (Finset.range (k - 1)).filter (· < j₀) = Finset.range j₀ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  rw [hfilter, Finset.card_range]

/-- 讀階梯 C^∞（有限和 of C^∞）。 -/
theorem sfloor_contDiff (k : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sfloor k w) := by
  apply ContDiff.sum
  intro j _
  exact sstep_contDiff _ _

/-- 讀階梯顯式導數（ODE 場可用）。 -/
theorem sfloor_hasDerivAt (k : ℕ) {w : ℝ} (hw1 : w < 1) (u : ℝ) :
    HasDerivAt (sfloor k w)
      (∑ j ∈ Finset.range (k - 1),
        deriv Real.smoothTransition ((u - ((j : ℝ) + w)) / (1 - w)) * (1 / (1 - w))) u := by
  have hg : (1 : ℝ) - w ≠ 0 := (show (0 : ℝ) < 1 - w by linarith).ne'
  have hfun : sfloor k w = ∑ j ∈ Finset.range (k - 1), sstep ((j : ℝ) + w) (1 - w) := by
    funext u; simp only [sfloor, Finset.sum_apply]
  rw [hfun]
  apply HasDerivAt.sum
  intro j _
  exact sstep_hasDerivAt ((j : ℝ) + w) (1 - w) u hg

end FluidTuring
