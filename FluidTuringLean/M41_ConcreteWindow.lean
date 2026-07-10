import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import FluidTuringLean.M40_GatedTargeting

/-!
# Module 41 — Analog-computation 流：Brick 3（具體非退化窗 + 兩側精確 HOLD）

**方向三 Brick 3**（承接 M40 Brick 2 gated/HOLD、M13 smoothTransition 料）。Brick 2 誠實記債：
唯一「具體」的窗活化 `Φ` 只有**退化**兩種——`Φ = id`（`φ≡1`、恆開、從不 HOLD）或 `Φ = const`
（從不 targeting）；真正**非退化**（先平坦→上升→再平坦）的具體 `Φ` 以為需 paper-blocked 的
bump FTC 反導數。

**★關鍵洞見（本磚兌現）★**：mathlib 的 `Real.smoothTransition`（`expNegInvGlue` 型光滑轉場）
**本身**就是一個閉式「平坦 0 → 光滑上升 → 平坦 1」窗：`x ≤ 0` 恰 0、`x ≥ 1` 恰 1、`[0,1]` 上
單調光滑。故 `windowΦ k t := smoothTransition (t - k)` 是**單一具體 `Φ`**，同時逃離兩種退化：
- 不像 `Φ = id`：**兩側**最終常值 ⟹ 兩側**精確 HOLD**（`t ≤ k` 與 `k+1 ≤ t` 上導數恰 0、值凍結）；
- 不像 `Φ = const`：**非常值**（`Φ k = 0 ≠ Φ(k+1) = 1`）⟹ **真 targeting**（值層見證 `moves`）。
全部閉式，**零 MeasureTheory、零 FTC、零區間積分、零新 axiom、零 sorry**。

**新能力（Brick 2 沒有的）**：
1. **兩側精確 HOLD**（整條半線值凍結，非僅逐點 `y'=0`）——leapfrog 時鐘（Brick 4）承重原語；
2. **值層永不擴張** `dist_antitone`：`|y(t)-b|` 對 `t` 單調不增（收縮或凍結、絕不擴張），
   純由 `smoothTransition.monotone` + `exp` 單調得，**不需** `deriv≥0`；
3. **量化窗質量** `windowΦ_mass = 1` ⟹ 一窗恰施加因子 `e^{-C}`（staircase/leapfrog 的組裝原子）。

**★誠實範圍（Brick 3 之上仍 paper-blocked，明寫，禁 overclaim）★**：
- **有限收縮，非精確收斂**：**單一** `smoothTransition` 窗在 `1` **飽和**（不 `→∞`），累積質量恰 `1`。
  故 `y` 只走到 `b + (y₀-b)e^{-C}`，關閉缺口比例 `(1 - e^{-C})`——是 **ε-近似**（靠拉大 `C`），
  **不是** `Φ→∞` 的精確 `y→b`。**切勿**對單窗套用 M40 `targetingGatedSol_tendsto`（它要
  `Tendsto Φ atTop atTop`）。精確 `y→b` 需**無限窗階梯**（Brick 3.5，選配，非本磚）。本磚
  `eps_target` 形式化的正是 Brick 2 自承「有限窗 ε 版未形式化」那塊。
- **非自治**（承 M13）：`φ = deriv smoothTransition (t-k)` 顯式依賴時間 `t` 與窗位 `k`，**非**狀態的
  函數。把 `φ` 自治化為狀態函數（沿軌道回拉停機鄰域指示）= GPAC 核心，多月、mathlib 從零。
- **round/decode / σ 落地 / leapfrog 排程 / undecidability 轉移**：不變、出本磚範圍。TM 態 ↔ 實數
  編碼與取整本質不連續；正確性需整套 Graça 誤差分析（每步 ε-收縮 + σ 把 ε-鄰域映進 ε-鄰域）。
  本磚**只**交付「具體非退化單窗 gated steer + 兩側精確 HOLD」，**不**宣稱模擬了機器。
  `σ`（TM 一步 map）在此層**保持抽象**：本磚是排程 + steering 動力學，與目標 `b` 是否 `=σ(舊態)` 無關。
-/

namespace FluidTuring

open Real Filter Topology

/-! ## 具體窗 `windowΦ` 與其活化解 `windowedTargetingSol` -/

/-- **具體非退化窗活化**：`windowΦ k t = smoothTransition (t - k)`。閉式「平坦 0 → 上升 → 平坦 1」，
其導數 `deriv smoothTransition (t-k)` 就是支撐在 `[k,k+1]` 的 bump 閘 `φ`（**無需**區間積分反導數）。 -/
noncomputable def windowΦ (k : ℝ) : ℝ → ℝ := fun t ↦ Real.smoothTransition (t - k)

/-- **窗活化的 targeting 解** = Brick 2 `targetingGatedSol` 以具體 `Φ := windowΦ k` 實例化。
展開後 `= b + (y₀-b)·exp(-(C·smoothTransition (t-k)))`。 -/
noncomputable def windowedTargetingSol (y₀ b C k : ℝ) : ℝ → ℝ :=
  targetingGatedSol y₀ b C (windowΦ k)

/-! ## 窗層引理（閉式 smoothTransition 事實） -/

/-- **窗導數 = 具體閉式 bump 閘**（餵 Brick 2 抽象 `Φ` 的具體見證）。用 M13 `smoothSwitchSol_hasDerivAt`
的 `HasDerivAt.comp_sub_const` 手法（避開 ℝ→ℝ `.comp` 的 InnerProductSpace instance-diamond）。 -/
theorem windowΦ_hasDerivAt (k t : ℝ) :
    HasDerivAt (windowΦ k) (deriv Real.smoothTransition (t - k)) t := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (t - k) :=
    (Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by norm_num)
  exact HasDerivAt.comp_sub_const t k hdiff.hasDerivAt

/-- **前側平坦（值）**：`t ≤ k ⟹ windowΦ k t = 0`（`smoothTransition.zero_of_nonpos`）。 -/
theorem windowΦ_zero_before {k t : ℝ} (h : t ≤ k) : windowΦ k t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- **後側飽和（值）**：`k + 1 ≤ t ⟹ windowΦ k t = 1`（`smoothTransition.one_of_one_le`）。 -/
theorem windowΦ_one_after {k t : ℝ} (h : k + 1 ≤ t) : windowΦ k t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- **前側 HOLD（導數層）**：`t < k ⟹ HasDerivAt (windowΦ k) 0 t`。窗前 `φ = 0`（局部恆 0）。
自足證（`eventuallyEq`-const），比重用 M13 `smoothTransition_deriv_zero_of_neg` 更直接。 -/
theorem windowΦ_hold_before {k t : ℝ} (h : t < k) : HasDerivAt (windowΦ k) 0 t := by
  have hev : windowΦ k =ᶠ[nhds t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact windowΦ_zero_before (le_of_lt hs)
  exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev

/-- **後側 HOLD（導數層）**：`k + 1 < t ⟹ HasDerivAt (windowΦ k) 0 t`。窗後 `φ = 0`（飽和恆 1）。
`windowΦ_hold_before` 的鏡像（`one_of_one_le` on `Ioi`）——研究標記為需自造的 mirror 引理。 -/
theorem windowΦ_hold_after {k t : ℝ} (h : k + 1 < t) : HasDerivAt (windowΦ k) 0 t := by
  have hev : windowΦ k =ᶠ[nhds t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact windowΦ_one_after (le_of_lt hs)
  exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hev

/-- **窗單調**：`Monotone (windowΦ k)`（`smoothTransition.monotone` 沿平移）。`dist_antitone` 承重。 -/
theorem windowΦ_monotone (k : ℝ) : Monotone (windowΦ k) := by
  intro a b hab
  exact Real.smoothTransition.monotone (by simpa using sub_le_sub_right hab k)

/-- **量化窗質量 = 1**：累積活化恰爬 `0 → 1`。故一窗恰施加因子 `e^{-C·1} = e^{-C}`——staircase/
leapfrog 的組裝原子。 -/
theorem windowΦ_mass (k : ℝ) : windowΦ k (k + 1) - windowΦ k k = 1 := by
  rw [windowΦ_one_after (le_refl _), windowΦ_zero_before (le_refl _)]; ring

/-! ## 解層引理（實例化 M40 到具體窗） -/

/-- **★具體閘控 ODE★**：解真滿足 `y' = -C·φ(t)·(y-b)`，`φ = deriv smoothTransition (t-k)` 閉式閘。
= M40 `targetingGatedSol_hasDerivAt` 餵具體 `windowΦ_hasDerivAt`（本磚零新 ODE 推理，純實例化）。 -/
theorem windowedTargetingSol_hasDerivAt (y₀ b C k t : ℝ) :
    HasDerivAt (windowedTargetingSol y₀ b C k)
      (-C * deriv Real.smoothTransition (t - k) *
        (windowedTargetingSol y₀ b C k t - b)) t :=
  targetingGatedSol_hasDerivAt y₀ b C (windowΦ k)
    (deriv Real.smoothTransition (t - k)) t (windowΦ_hasDerivAt k t)

/-- **前側 HOLD（解，導數層）**：`t < k ⟹` 解導數恰 0（M40 `_hold` + `windowΦ_hold_before`）。 -/
theorem windowedTargetingSol_hold_before {y₀ b C k t : ℝ} (h : t < k) :
    HasDerivAt (windowedTargetingSol y₀ b C k) 0 t :=
  targetingGatedSol_hold y₀ b C (windowΦ k) t (windowΦ_hold_before h)

/-- **後側 HOLD（解，導數層）**：`k + 1 < t ⟹` 解導數恰 0（M40 `_hold` + `windowΦ_hold_after`）。 -/
theorem windowedTargetingSol_hold_after {y₀ b C k t : ℝ} (h : k + 1 < t) :
    HasDerivAt (windowedTargetingSol y₀ b C k) 0 t :=
  targetingGatedSol_hold y₀ b C (windowΦ k) t (windowΦ_hold_after h)

/-- **前側凍結（值）**：`t ≤ k ⟹` 解恰 `= y₀`（窗前 `Φ=0`、`exp 0 = 1`）。 -/
theorem windowedTargetingSol_frozen_before {y₀ b C k t : ℝ} (h : t ≤ k) :
    windowedTargetingSol y₀ b C k t = y₀ := by
  simp [windowedTargetingSol, targetingGatedSol, windowΦ_zero_before h]

/-- **後側凍結（值）**：`k + 1 ≤ t ⟹` 解恰 `= b + (y₀-b)·e^{-C}`（窗後 `Φ=1` 飽和常值）。
整條 `[k+1,∞)` 嚴格常值亦可經 M40 `targetingGatedSol_const_of_Φ_eq` + `windowΦ_one_after`。 -/
theorem windowedTargetingSol_frozen_after {y₀ b C k t : ℝ} (h : k + 1 ≤ t) :
    windowedTargetingSol y₀ b C k t = b + (y₀ - b) * Real.exp (-C) := by
  simp [windowedTargetingSol, targetingGatedSol, windowΦ_one_after h]

/-! ## ★缺口清償★：非退化（同時逃 `Φ=id` 與 `Φ=const`） + ε-target + 永不擴張 -/

/-- **★缺口清償（非退化見證，值層）★**：`C>0 ∧ y₀≠b ⟹` 窗前值 `≠` 窗後值。反駁 Brick 2「具體 `Φ`
只有退化」：本窗**真的 targeting**（值層移動），非 `Φ=const` 恆不動的退化。 -/
theorem windowedTargetingSol_moves (y₀ b C k : ℝ) (hC : 0 < C) (hy : y₀ ≠ b) :
    windowedTargetingSol y₀ b C k k ≠ windowedTargetingSol y₀ b C k (k + 1) := by
  rw [windowedTargetingSol_frozen_before (le_refl k),
      windowedTargetingSol_frozen_after (le_refl (k + 1))]
  have hlt : Real.exp (-C) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  intro hcontra
  have hz : (y₀ - b) * (1 - Real.exp (-C)) = 0 := by ring_nf; nlinarith [hcontra]
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact hy (by linarith [sub_eq_zero.mp h1])
  · linarith

/-- **★值層永不擴張（收縮或凍結、絕不擴張）★**：`0 ≤ C ⟹ |y(t)-b|` 對 `t` **反單調**。純由
`windowΦ_monotone` + `exp` 單調（`gcongr`），**不需** `deriv≥0`（那才需 bump 顯式公式）。 -/
theorem windowedTargetingSol_dist_antitone (y₀ b C k : ℝ) (hC : 0 ≤ C) {s t : ℝ}
    (hst : s ≤ t) :
    |windowedTargetingSol y₀ b C k t - b| ≤ |windowedTargetingSol y₀ b C k s - b| := by
  have hmono : windowΦ k s ≤ windowΦ k t := windowΦ_monotone k hst
  simp only [windowedTargetingSol, targetingGatedSol, add_sub_cancel_left, abs_mul]
  gcongr

/-- **★ε-target（有限窗、誠實 ε-近似）★**：`∀ ε>0, ∃ C>0`，窗後（`k+1 ≤ t`）解落 `b` 的 ε-內。
**誠實界線**：此為 **ε-近似**（靠拉大 `C`），**非** `Φ→∞` 的精確 `y→b`——單窗質量有限（`=1`）。
取 `C := |y₀-b|/ε`，用 `e^{-C} ≤ C⁻¹`（`add_one_le_exp` + `inv_anti₀`）得 `|y₀-b|·e^{-C} ≤ ε`。 -/
theorem windowedTargetingSol_eps_target (y₀ b k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 < C ∧ ∀ t, k + 1 ≤ t → |windowedTargetingSol y₀ b C k t - b| ≤ ε := by
  rcases eq_or_ne y₀ b with hyb | hyb
  · refine ⟨1, one_pos, fun t ht ↦ ?_⟩
    rw [windowedTargetingSol_frozen_after ht, hyb]
    simp only [sub_self, zero_mul, add_zero, abs_zero]
    exact hε.le
  · have hMpos : 0 < |y₀ - b| := abs_pos.mpr (sub_ne_zero.mpr hyb)
    refine ⟨|y₀ - b| / ε, div_pos hMpos hε, fun t ht ↦ ?_⟩
    rw [windowedTargetingSol_frozen_after ht]
    have hC : (0 : ℝ) < |y₀ - b| / ε := div_pos hMpos hε
    have h1 : Real.exp (-(|y₀ - b| / ε)) ≤ (|y₀ - b| / ε)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hC (by have := Real.add_one_le_exp (|y₀ - b| / ε); linarith)
    have key : |y₀ - b| * Real.exp (-(|y₀ - b| / ε)) ≤ ε := by
      calc |y₀ - b| * Real.exp (-(|y₀ - b| / ε))
          ≤ |y₀ - b| * (|y₀ - b| / ε)⁻¹ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = ε := by field_simp
    have heq : b + (y₀ - b) * Real.exp (-(|y₀ - b| / ε)) - b
        = (y₀ - b) * Real.exp (-(|y₀ - b| / ε)) := by ring
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact key

/-- **有限收縮因子（精確）**：`k+1 ≤ t ⟹ |y(t)-b| = |y₀-b|·e^{-C}`——一窗淨收縮**恰**因子 `e^{-C}`
（`dist_antitone` 的窗後精確值；staircase 疊 `k` 窗 ⟹ `e^{-Ck}`）。 -/
theorem windowedTargetingSol_contracts (y₀ b C k : ℝ) {t : ℝ} (h : k + 1 ≤ t) :
    |windowedTargetingSol y₀ b C k t - b| = |y₀ - b| * Real.exp (-C) := by
  have hcancel : b + (y₀ - b) * Real.exp (-C) - b = (y₀ - b) * Real.exp (-C) := by ring
  rw [windowedTargetingSol_frozen_after h, hcancel, abs_mul, abs_of_pos (Real.exp_pos (-C))]

/-- **★HEADLINE：單一具體 `Φ` 同時「兩側 HOLD」+「真 move」——字面殺死 Brick 2 缺口★**。
本窗 `windowΦ k`（= `smoothTransition (·-k)`）逃離 Brick 2 的雙退化：
前後兩側**精確凍結**（值 + 導數層），且窗跨**真的移動**（`C>0, y₀≠b`），並處處滿足具體閘控 ODE。 -/
theorem windowedTargetingSol_escapes_degeneracy (y₀ b C k : ℝ) (hC : 0 < C) (hy : y₀ ≠ b) :
    (∀ t, t ≤ k → windowedTargetingSol y₀ b C k t = y₀) ∧
    (∀ t, k + 1 ≤ t → windowedTargetingSol y₀ b C k t = b + (y₀ - b) * Real.exp (-C)) ∧
    (windowedTargetingSol y₀ b C k k ≠ windowedTargetingSol y₀ b C k (k + 1)) ∧
    (∀ t, t < k → HasDerivAt (windowedTargetingSol y₀ b C k) 0 t) ∧
    (∀ t, k + 1 < t → HasDerivAt (windowedTargetingSol y₀ b C k) 0 t) ∧
    (∀ t, HasDerivAt (windowedTargetingSol y₀ b C k)
      (-C * deriv Real.smoothTransition (t - k) *
        (windowedTargetingSol y₀ b C k t - b)) t) :=
  ⟨fun _ ht ↦ windowedTargetingSol_frozen_before ht,
   fun _ ht ↦ windowedTargetingSol_frozen_after ht,
   windowedTargetingSol_moves y₀ b C k hC hy,
   fun _ ht ↦ windowedTargetingSol_hold_before ht,
   fun _ ht ↦ windowedTargetingSol_hold_after ht,
   fun t ↦ windowedTargetingSol_hasDerivAt y₀ b C k t⟩

end FluidTuring
