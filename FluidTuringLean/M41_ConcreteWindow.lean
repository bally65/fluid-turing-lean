import FluidTuringLean.M40_GatedTargeting
import FluidTuringLean.M13_SmoothSwitch

/-!
# Module 41 — Analog-computation 流：Brick 3（具體非退化窗，消 Brick 2 缺口）

**方向三 Brick 3**（承接 M40 Brick 2 gated targeting）。Brick 2 把「具體 bump 窗 `Φ=∫φ`」誤標為
需 MeasureTheory FTC 的 paper-blocked，且其唯一具體 `Φ` 見證退化（`Φ=id` 恆開不 HOLD、`Φ=const`
恆凍不 target）。**本磚破解**：mathlib `Real.smoothTransition`（`expNegInvGlue` 型，M13 已用）
**本身就是** bump 的**閉式**原函數——`x≤0` 恰 0、`x≥1` 恰 1、`[0,1]` 光滑單調升——**無需區間積分**。

用它造**具體非退化窗** `windowΦ k := smoothTransition(· - k)`，把 Brick 2 的抽象 `Φ` **實例化**：
- **兩側精確 HOLD**（不同於 `Φ=id`）：`t≤k` 恰凍結、`k+1≤t` 恰凍結（`zero_of_nonpos`/`one_of_one_le`
  + M40 `_hold`）；
- **窗內真 target 移動**（不同於 `Φ=const`）：`windowedTargetingSol_moves` 值層見證前後值不等。

⟹ **單一具體 `Φ` 同時逃離兩種退化 = 消 Brick 2 審查缺口**。全部走 M40 已證引理 + `smoothTransition`
閉式事實，**零新 ODE 論證、無抽象 ODE 存在性、無 FTC、無 round**。

**誠實範圍（明寫、不 overclaim）**：
- **單窗只有有限收縮** `e^{-C}`（`y₀ ↦ b+(y₀-b)e^{-C}`、閉合缺口比例 `1-e^{-C}`），**非**精確到 `b`；
  精確收斂需無限窗質量 `Φ→∞`（Brick 2 `_tendsto` 抽象涵蓋、具體階梯 = 後續磚）。**切勿**對單窗套 `_tendsto`。
- **窗仍非自治**（`φ = smoothTransition'(t-k)` 依賴時間 `t`/窗位 `k`、非系統**狀態**）——自治化（把 `φ`
  拉回成停機鄰域指示沿軌道的 pullback）= GPAC 核心、多月 mathlib-from-zero、M13 同標 paper-blocked。
- round/decode（TM 態 ↔ 實數、不連續）、`σ`（一步 TM 更新作目標 `b`）、leapfrog 兩暫存器排程、
  undecidability 轉移 = **仍 paper-blocked**。本磚**只**交付具體非退化單窗 gated steer + 兩側 HOLD。
-/

namespace FluidTuring

open Real Filter Topology

/-! ## 具體窗 `windowΦ`（`smoothTransition` 平移，閉式平坦→升→平坦） -/

/-- **具體窗活化**：`windowΦ k t = smoothTransition (t - k)`。`t≤k` 恰 0、`k+1≤t` 恰 1、中間光滑升；
其導數 = 支撐 `[k,k+1]` 的閉式 bump（= 閘 `φ`）。 -/
noncomputable def windowΦ (k : ℝ) : ℝ → ℝ := fun t ↦ Real.smoothTransition (t - k)

/-- 窗前恰 0（精確平坦，非近似）。 -/
theorem windowΦ_zero_before {k t : ℝ} (h : t ≤ k) : windowΦ k t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- 窗後恰 1（精確飽和）。 -/
theorem windowΦ_one_after {k t : ℝ} (h : k + 1 ≤ t) : windowΦ k t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- 窗單調（`φ ≥ 0`：閘控流永遠收縮或凍結、絕不擴張）。 -/
theorem windowΦ_monotone (k : ℝ) : Monotone (windowΦ k) := by
  intro a b hab
  simp only [windowΦ]
  exact Real.smoothTransition.monotone (sub_le_sub_right hab k)

/-- **窗導數存在**（餵 Brick 2 抽象 `Φ` 假設）：`HasDerivAt (windowΦ k) (deriv smoothTransition (t-k)) t`。
= M13 `smoothSwitchSol_hasDerivAt` 同法（`contDiffAt`→`differentiableAt`→`comp_sub_const`）。 -/
theorem windowΦ_hasDerivAt (k t : ℝ) :
    HasDerivAt (windowΦ k) (deriv Real.smoothTransition (t - k)) t := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (t - k) :=
    (Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by norm_num)
  exact HasDerivAt.comp_sub_const t k hdiff.hasDerivAt

/-- **窗前 HOLD（導數層）**：`t < k` ⟹ `windowΦ` 局部恆 0 ⟹ 導數 0。 -/
theorem windowΦ_hold_before {k t : ℝ} (h : t < k) : HasDerivAt (windowΦ k) 0 t := by
  have hev : windowΦ k =ᶠ[nhds t] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    simp only [windowΦ]
    rw [Set.mem_Iio] at hs
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev

/-- **窗後 HOLD（導數層）**：`k+1 < t` ⟹ `windowΦ` 局部恆 1 ⟹ 導數 0。 -/
theorem windowΦ_hold_after {k t : ℝ} (h : k + 1 < t) : HasDerivAt (windowΦ k) 0 t := by
  have hev : windowΦ k =ᶠ[nhds t] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp only [windowΦ]
    rw [Set.mem_Ioi] at hs
    exact Real.smoothTransition.one_of_one_le (by linarith)
  exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hev

/-! ## 具體窗 gated targeting（= Brick 2 def 實例化） -/

/-- **具體單窗 gated targeting 解** = Brick 2 `targetingGatedSol` 餵具體窗 `windowΦ k`：
`= b + (y₀-b)·exp(-(C·smoothTransition(t-k)))`。 -/
noncomputable def windowedTargetingSol (y₀ b C k : ℝ) : ℝ → ℝ :=
  targetingGatedSol y₀ b C (windowΦ k)

/-- **★具體 gated ODE★**：真滿足 `y' = -C·φ·(y-b)`，`φ = smoothTransition'(t-k)` **閉式**（非抽象）。 -/
theorem windowedTargetingSol_hasDerivAt (y₀ b C k t : ℝ) :
    HasDerivAt (windowedTargetingSol y₀ b C k)
      (-C * deriv Real.smoothTransition (t - k) * (windowedTargetingSol y₀ b C k t - b)) t :=
  targetingGatedSol_hasDerivAt y₀ b C (windowΦ k) (deriv Real.smoothTransition (t - k)) t
    (windowΦ_hasDerivAt k t)

/-- **窗前精確凍結（值層）**：`t≤k` ⟹ 解**恰** `y₀`（未動）。 -/
theorem windowedTargetingSol_frozen_before (y₀ b C k t : ℝ) (h : t ≤ k) :
    windowedTargetingSol y₀ b C k t = y₀ := by
  simp only [windowedTargetingSol, targetingGatedSol, windowΦ_zero_before h,
    mul_zero, neg_zero, Real.exp_zero, mul_one]
  ring

/-- **窗後精確凍結（值層）**：`k+1≤t` ⟹ 解**恰** `b+(y₀-b)e^{-C}`（一窗淨映射；此後不再動）。 -/
theorem windowedTargetingSol_frozen_after (y₀ b C k t : ℝ) (h : k + 1 ≤ t) :
    windowedTargetingSol y₀ b C k t = b + (y₀ - b) * Real.exp (-C) := by
  simp only [windowedTargetingSol, targetingGatedSol, windowΦ_one_after h, mul_one]

/-- **窗前 HOLD（導數層）**：`t<k` ⟹ 解導數 0（凍結）= M40 `_hold` 餵具體窗。 -/
theorem windowedTargetingSol_hold_before (y₀ b C k : ℝ) {t : ℝ} (h : t < k) :
    HasDerivAt (windowedTargetingSol y₀ b C k) 0 t :=
  targetingGatedSol_hold y₀ b C (windowΦ k) t (windowΦ_hold_before h)

/-- **窗後 HOLD（導數層）**：`k+1<t` ⟹ 解導數 0（凍結）。 -/
theorem windowedTargetingSol_hold_after (y₀ b C k : ℝ) {t : ℝ} (h : k + 1 < t) :
    HasDerivAt (windowedTargetingSol y₀ b C k) 0 t :=
  targetingGatedSol_hold y₀ b C (windowΦ k) t (windowΦ_hold_after h)

/-- **★非退化見證（消 Brick 2 缺口）★**：`C>0`、`y₀≠b` ⟹ 窗前值 `y₀` **≠** 窗後值
`b+(y₀-b)e^{-C}`——這個具體窗**真的移動了** `y`（不同於 `Φ=const` 恆凍），且它兩側 HOLD
（不同於 `Φ=id` 恆開）。單一具體 `Φ` 同時逃離兩種退化。 -/
theorem windowedTargetingSol_moves (y₀ b C : ℝ) (hC : 0 < C) (hy : y₀ ≠ b) :
    y₀ ≠ b + (y₀ - b) * Real.exp (-C) := by
  have hlt : Real.exp (-C) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  intro heq
  have hz : (y₀ - b) * (1 - Real.exp (-C)) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp hz with h | h
  · exact hy (by linarith)
  · linarith

/-- **有限收縮（誠實 ε 界線）**：一窗後 `|y - b| = |y₀ - b|·e^{-C}`——閉合缺口比例 `1-e^{-C}`，
**非**精確到 `b`。`C→∞` 才任意接近；精確收斂需無限窗質量（後續磚）。 -/
theorem windowedTargetingSol_contracts (y₀ b C k t : ℝ) (h : k + 1 ≤ t) :
    |windowedTargetingSol y₀ b C k t - b| = |y₀ - b| * Real.exp (-C) := by
  have hcancel : b + (y₀ - b) * Real.exp (-C) - b = (y₀ - b) * Real.exp (-C) := by ring
  rw [windowedTargetingSol_frozen_after y₀ b C k t h, hcancel, abs_mul,
    abs_of_pos (Real.exp_pos (-C))]

end FluidTuring
