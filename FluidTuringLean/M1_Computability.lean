import Mathlib

/-!
# Module 1 — TTE 可計算分析基礎

Type-Two Effectivity (TTE) 風格的基礎層：

* `eml x y = exp x - log y` 原語：連續性、單調性、`y → 0⁺` 奇異點。
* 快速收斂柯西表示 `Represents`：每個實數都有 `2⁻ⁿ` 精度的有理數列表示。

本檔零 sorry。
-/

namespace FluidTuring

/-- 翻譯鏈的解析原語 `eml x y = exp x - log y`。
`Real.log` 在 `y ≤ 0` 取 junk 值 `0`，故 `eml` 是全函數；
有意義的定義域是 `y > 0`，見下方連續性與奇異點引理。 -/
noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

@[simp]
theorem eml_def (x y : ℝ) : eml x y = Real.exp x - Real.log y := rfl

/-- `eml` 在 `{p | p.2 ≠ 0}` 上連續（`log` 唯一的不連續點是 `0`）。 -/
theorem continuousOn_eml :
    ContinuousOn (fun p : ℝ × ℝ ↦ eml p.1 p.2) {p : ℝ × ℝ | p.2 ≠ 0} := by
  apply ContinuousOn.sub
  · exact (Real.continuous_exp.comp continuous_fst).continuousOn
  · exact Real.continuousOn_log.comp continuous_snd.continuousOn fun p hp ↦ hp

/-- 固定 `y`，`eml` 對 `x` 嚴格遞增。 -/
theorem strictMono_eml_left (y : ℝ) : StrictMono fun x ↦ eml x y := by
  intro a b hab
  simpa [eml, sub_lt_sub_iff_right] using Real.exp_lt_exp.2 hab

/-- 固定 `x`，`eml` 對 `y` 在 `(0, ∞)` 上嚴格遞減。 -/
theorem strictAntiOn_eml_right (x : ℝ) : StrictAntiOn (eml x) (Set.Ioi 0) := by
  intro a ha b hb hab
  exact sub_lt_sub_left (Real.strictMonoOn_log ha hb hab) _

/-- 奇異點：`y → 0⁺` 時 `eml x y → +∞`。 -/
theorem tendsto_eml_atTop (x : ℝ) :
    Filter.Tendsto (eml x) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hlog : Filter.Tendsto Real.log (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hneg : Filter.Tendsto (fun y ↦ -Real.log y)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog
  have h : Filter.Tendsto (fun y ↦ Real.exp x + -Real.log y)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ hneg
  change Filter.Tendsto (fun y ↦ Real.exp x - Real.log y)
    (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop
  simpa [sub_eq_add_neg] using h

/-! ## TTE 表示：快速收斂柯西數列 -/

/-- TTE 名字系統：有理數列 `f` 以 `2⁻ⁿ` 收斂速率表示實數 `x`。 -/
def Represents (f : ℕ → ℚ) (x : ℝ) : Prop :=
  ∀ n : ℕ, |(f n : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ n

/-- 表示的存在性：每個實數都有 TTE 名字。（用 `Classical.choice` 選出逼近列。） -/
theorem exists_represents (x : ℝ) : ∃ f : ℕ → ℚ, Represents f x := by
  have h : ∀ n : ℕ, ∃ q : ℚ, |x - (q : ℝ)| < (2 : ℝ)⁻¹ ^ n := fun n ↦
    exists_rat_near x (by positivity)
  choose f hf using h
  exact ⟨f, fun n ↦ by rw [abs_sub_comm]; exact (hf n).le⟩

/-- 表示的唯一性方向：名字收斂到唯一實數。 -/
theorem represents_unique {f : ℕ → ℚ} {x y : ℝ}
    (hx : Represents f x) (hy : Represents f y) : x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hpos) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hx' := hx n
  have hy' := hy n
  have : |x - y| ≤ (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n := by
    calc |x - y| = |(x - (f n : ℝ)) + ((f n : ℝ) - y)| := by
          congr 1; ring
    _ ≤ |x - (f n : ℝ)| + |(f n : ℝ) - y| := abs_add_le _ _
    _ ≤ (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n := by
        rw [abs_sub_comm x (f n : ℝ)]
        exact add_le_add hx' hy'
  have hcontra : |x - y| < |x - y| := by
    calc |x - y| ≤ (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n := this
    _ < |x - y| / 2 + |x - y| / 2 := add_lt_add hn hn
    _ = |x - y| := add_halves _
  exact absurd hcontra (lt_irrefl _)

end FluidTuring
