import Mathlib
import FluidTuringLean.M45_SmoothReround
import FluidTuringLean.M46_SmoothRead

/-!
# Module 60 — analytic GPAC 線（L4）：exact-on-lattice 讀符對 analytic 不可能（certified 負結果）

**方向三 GPAC 線的 analytic 語意分歧**（見 `docs/GPAC_ROADMAP.md`、多次標為「若嚴格 GPAC 要求
analytic 向量場，則 exact-on-lattice scaffold 離題」）。本磚把這個非正式 caveat **機器化**成一個
certified 不可能性定理，與 `M56_G5Wall.lean`（連續流 robustness 死牆）平行。

## 一句話

我們整套「精確讀符」`sfloor`（M46，在 plateau 上**字面常值**等於符號）用 `smoothTransition`
（C^∞ 但**非** analytic）。而 analytic 函數有**恆等定理**：在一段開區間上常值 ⟹ 全域常值。故
**任何 analytic 函數都不可能是「精確 plateau 讀符器」**（它讀不出兩個不同符號）——`sfloor`
**必然非 analytic**（只 C^∞）。這是定理、不是工程限制。

## 交付（全顯式、零 sorry、標準三公理）

- **`analytic_const_on_interval_imp_const`**：`f` 於 ℝ 上 analytic + 在某開區間上恆 `c` ⟹ 全域恆 `c`
  （mathlib 恆等定理 `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` + `isPreconnected_univ`）。
- **`no_analytic_two_plateau_reader`（★analytic 讀符牆★）**：`f` analytic 且在兩個開區間上分別恆
  `u`、`v` ⟹ `u = v`。**沒有 analytic 函數能在不同 plateau 取不同常值** = 讀不出兩個符號。
- **`sfloor_not_analytic`（★具體後果★）**：`sfloor k w`（`k≥2`）**不是** `AnalyticOnNhd ℝ · univ`
  ——因它在 plateau 0 恆 0、在 plateau 1 恆 1（`sfloor_exact_on_plateau`），與上一條矛盾。
- **`sround_analytic`（★誠實對比★）**：`sround`（M45、`sin` 基的 re-rounding 原語）**是** analytic。
  故 analytic 障礙**精確定位在「精確讀符」**，非整個 scaffold——error-correction 原語本身 analytic 可得。

## ★誠實範圍（禁 overclaim）★

- **本磚證的是「exact-plateau 技術對 analytic 不可能」，不是「analytic 動力系統計算不可能」。**
  相反，Bournez–Graça–Pouly（JACM 2017）**紙上已證** analytic 多項式 ODE **可**模擬圖靈機——用的是
  **近似 + error-correction**（非 exact-on-lattice），是**另一套架構**。`sround_analytic` 正好指出
  error-corrector 本身 analytic 可得；真正 analytic GPAC 的正面路線 = 近似讀 + `sround` 校正的組合，
  = paper-level、mathlib 未形式化、**本磚不做**。
- 所以本磚的價值 = **certify「我們的具體架構（exact-on-lattice）內稟只能 C^∞」**、把 roadmap 的
  「analytic 語意分歧」從口頭 caveat 升為機器背書的不可能性；並誠實標出正面 analytic 路線在別處。
- 不影響 M33/M59 兩座封頂（皆 C^∞，本就不宣稱 analytic）。
-/

namespace FluidTuring

open Real Set

/-! ## analytic 恆等定理（區間常值 ⟹ 全域常值） -/

/-- **analytic + 開區間常值 ⟹ 全域常值**：`f` 於 ℝ 上處處 analytic 且在 `Ioo a b`（`a<b`）恆 `c`
⟹ `∀ x, f x = c`（mathlib 恆等定理 + ℝ 連通）。 -/
theorem analytic_const_on_interval_imp_const (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f Set.univ) {a b : ℝ} (hab : a < b) {c : ℝ}
    (hconst : ∀ x ∈ Set.Ioo a b, f x = c) : ∀ x, f x = c := by
  have hg : AnalyticOnNhd ℝ (fun _ : ℝ => c) Set.univ := analyticOnNhd_const
  have hz : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hev : f =ᶠ[nhds ((a + b) / 2)] (fun _ : ℝ => c) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx using hconst x hx
  have hEq := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (Set.mem_univ _) hev
  intro x
  exact hEq (Set.mem_univ x)

/-! ## ★analytic 讀符牆★ -/

/-- **★沒有 analytic 兩符號精確讀符器★**：`f` analytic、在 `Ioo a b` 恆 `u`、在 `Ioo c d` 恆 `v`
⟹ `u = v`。一個在某開區間常值的 analytic 函數全域常值，故無法在另一區間取不同值。 -/
theorem no_analytic_two_plateau_reader (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f Set.univ) {a b c d u v : ℝ} (hab : a < b) (hcd : c < d)
    (h1 : ∀ x ∈ Set.Ioo a b, f x = u) (h2 : ∀ x ∈ Set.Ioo c d, f x = v) : u = v := by
  have hall := analytic_const_on_interval_imp_const f hf hab h1
  have hv : f ((c + d) / 2) = v := h2 _ ⟨by linarith, by linarith⟩
  rw [hall ((c + d) / 2)] at hv
  exact hv

/-! ## ★具體後果：`sfloor` 讀符原語必然非 analytic★ -/

/-- **★`sfloor` 非 analytic★**：`k ≥ 2`、`0<w<1` ⟹ `sfloor k w` **不是** ℝ 上處處 analytic。
理由：它在 plateau `[0,w]` 恆 0、在 `[1,1+w]` 恆 1（`sfloor_exact_on_plateau`），若 analytic 則
由 `no_analytic_two_plateau_reader` 得 `0 = 1`，矛盾。⟹ 整個 exact-plateau scaffold 只能 C^∞。 -/
theorem sfloor_not_analytic (k : ℕ) (hk : 2 ≤ k) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    ¬ AnalyticOnNhd ℝ (sfloor k w) Set.univ := by
  intro hana
  have h0 : ∀ x ∈ Set.Ioo (0 : ℝ) w, sfloor k w x = (0 : ℝ) := by
    intro x hx
    have := sfloor_exact_on_plateau k hw0 hw1 0 (by omega) (u := x)
      (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
    simpa using this
  have h1 : ∀ x ∈ Set.Ioo (1 : ℝ) (1 + w), sfloor k w x = (1 : ℝ) := by
    intro x hx
    have := sfloor_exact_on_plateau k hw0 hw1 1 (by omega) (u := x)
      (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
    simpa using this
  have hcontra := no_analytic_two_plateau_reader (sfloor k w) hana hw0
    (by linarith : (1 : ℝ) < 1 + w) h0 h1
  norm_num at hcontra

/-! ## ★誠實對比：re-rounding 原語 `sround` 本身 analytic★ -/

/-- **★`sround` 是 analytic★**：`sround x = x − sin(2πx)/(2π)`（`sin` entire）⟹ analytic。
故 analytic 障礙**精確定位在「精確讀符」`sfloor`**、非整個 GPAC scaffold——error-correction 原語
（G3）在 analytic 下乾淨可得（呼應 Branicky/Bournez–Graça–Pouly 的近似+校正正面路線）。 -/
theorem sround_analytic : AnalyticOnNhd ℝ sround Set.univ := by
  intro x _
  have h1 : AnalyticAt ℝ (fun y : ℝ => 2 * π * y) x := analyticAt_const.mul analyticAt_id
  have h2 : AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * π * y)) x := Real.analyticAt_sin.comp h1
  unfold sround
  exact analyticAt_id.sub h2.div_const

end FluidTuring
