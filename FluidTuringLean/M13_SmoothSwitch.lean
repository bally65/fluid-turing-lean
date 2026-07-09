import FluidTuringLean.M12_HaltBlowupBridge
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Module 13 — 光滑化開關（(A2)：消掉 M12 的混成切換點）

M12 的 `switchSol` 在切換點 `t₀` 只有 C⁰（左導數 0、右導數 1 的 kink）——「混成系統」
誠實界線 (i)。本模組用 mathlib 的 **`Real.smoothTransition`**（`expNegInvGlue` 型光滑
過渡：`x ≤ 0` **恰為** 0、`x ≥ 1` **恰為** 1、C^∞）把開關光滑化：

`smoothSwitchSol t₀ t = (1 - smoothTransition (t - t₀))⁻¹`

- 停機前（`t ≤ t₀`）**恰為** `1`（`expNegInvGlue` 的平坦性——不是近似、是精確）；
- 在整個存在區間 `(-∞, t₀+1)` 上是**單一 C^∞ 函數**（無切換點、混成 caveat 消除）；
- 滿足**光滑 Riccati** `z' = h(t)·z²`，其中 `h(t) = (smoothTransition)'(t - t₀)` 是
  **光滑係數**、且停機前 `h ≡ 0`（機器證明 `smoothTransition_deriv_zero_of_neg`）；
- `t → (t₀+1)⁻` 時**有限時間爆破**。

**誠實界線（剩餘）**：`h` 仍是**非自治**（顯式依賴時間與觸發時刻 `t₀`）。把觸發
自治化——`h` 改為模擬**狀態**的函數（流形上停機區的鄰域指示、沿軌道回拉）——是
(A) 剩餘的 GPAC 核心（多月）。本塊消掉的是「切換不光滑」這一層。
-/

namespace FluidTuring

/-- **光滑開關耦合解**：`(1 - smoothTransition (t - t₀))⁻¹`。 -/
noncomputable def smoothSwitchSol (t₀ : ℝ) : ℝ → ℝ :=
  fun t ↦ (1 - Real.smoothTransition (t - t₀))⁻¹

/-- 停機前**恰為** `1`（`expNegInvGlue` 平坦性：`smoothTransition` 於非正輸入恰 0）。 -/
theorem smoothSwitchSol_eq_one (t₀ t : ℝ) (h : t ≤ t₀) : smoothSwitchSol t₀ t = 1 := by
  simp [smoothSwitchSol, Real.smoothTransition.zero_of_nonpos (by linarith : t - t₀ ≤ 0)]

/-- 分母正性：爆破時刻前 `1 - smoothTransition (t - t₀) > 0`（`lt_one_of_lt_one`）。 -/
theorem smoothSwitch_denom_pos (t₀ t : ℝ) (h : t < t₀ + 1) :
    0 < 1 - Real.smoothTransition (t - t₀) :=
  sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by linarith : t - t₀ < 1))

/-- **單一 C^∞ 軌跡**：`smoothSwitchSol` 在整個存在區間 `(-∞, t₀+1)` 上任意階可微
——M12 的混成切換點消除。 -/
theorem smoothSwitchSol_contDiffOn (t₀ : ℝ) (n : ℕ∞) :
    ContDiffOn ℝ n (smoothSwitchSol t₀) (Set.Iio (t₀ + 1)) := by
  have hs : ContDiff ℝ n fun t : ℝ ↦ 1 - Real.smoothTransition (t - t₀) :=
    contDiff_const.sub
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
  intro t ht
  exact ((hs.contDiffAt.inv (ne_of_gt (smoothSwitch_denom_pos t₀ t ht))).contDiffWithinAt)

/-- 停機前光滑係數為零：`smoothTransition` 於負點的導數 = 0（局部恆 0）。 -/
theorem smoothTransition_deriv_zero_of_neg {x : ℝ} (h : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[nhds x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [heq.deriv_eq]
  exact deriv_const x 0

/-- **光滑 Riccati**：`z' = h(t) · z²`，`h(t) = (smoothTransition)'(t - t₀)` 光滑係數。 -/
theorem smoothSwitchSol_hasDerivAt (t₀ t : ℝ) (h : t < t₀ + 1) :
    HasDerivAt (smoothSwitchSol t₀)
      (deriv Real.smoothTransition (t - t₀) * smoothSwitchSol t₀ t ^ 2) t := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (t - t₀) :=
    (Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by norm_num)
  have hinner : HasDerivAt (fun u : ℝ ↦ Real.smoothTransition (u - t₀))
      (deriv Real.smoothTransition (t - t₀)) t :=
    HasDerivAt.comp_sub_const t t₀ hdiff.hasDerivAt
  have hden : HasDerivAt (fun u : ℝ ↦ 1 - Real.smoothTransition (u - t₀))
      (-(deriv Real.smoothTransition (t - t₀))) t := hinner.const_sub 1
  have hne : 1 - Real.smoothTransition (t - t₀) ≠ 0 :=
    ne_of_gt (smoothSwitch_denom_pos t₀ t h)
  have h2 := hden.inv hne
  have heq : -(-(deriv Real.smoothTransition (t - t₀))) /
        (1 - Real.smoothTransition (t - t₀)) ^ 2
      = deriv Real.smoothTransition (t - t₀) * smoothSwitchSol t₀ t ^ 2 := by
    simp only [neg_neg, smoothSwitchSol, inv_pow, div_eq_mul_inv]
  rwa [heq] at h2

/-- **有限時間爆破**：`t → (t₀+1)⁻` 時光滑開關解爆到 `+∞`。 -/
theorem smoothSwitchSol_tendsto_atTop (t₀ : ℝ) :
    Filter.Tendsto (smoothSwitchSol t₀) (nhdsWithin (t₀ + 1) (Set.Iio (t₀ + 1)))
      Filter.atTop := by
  have hden : Filter.Tendsto (fun t ↦ 1 - Real.smoothTransition (t - t₀))
      (nhdsWithin (t₀ + 1) (Set.Iio (t₀ + 1))) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Filter.Tendsto (fun t ↦ 1 - Real.smoothTransition (t - t₀)) (nhds (t₀ + 1))
          (nhds (1 - Real.smoothTransition (t₀ + 1 - t₀))) :=
        (continuous_const.sub (Real.smoothTransition.continuous.comp
          (continuous_id.sub continuous_const))).tendsto (t₀ + 1)
      have hval : 1 - Real.smoothTransition (t₀ + 1 - t₀) = 0 := by
        norm_num [Real.smoothTransition.one_of_one_le]
      rw [hval] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact smoothSwitch_denom_pos t₀ t ht
  have := hden.inv_tendsto_nhdsGT_zero
  simp only [Pi.inv_def] at this
  exact this

/-- **★停機 ⟹ 光滑軌跡有限時間爆破★（(A2) 完成、混成 caveat 消除）**：停機時，耦合
座標是**單一 C^∞ 函數**——停機前恰 `1`、滿足光滑 Riccati `z' = h(t)z²`（`h` 光滑、
停機前恆 0）、於有限時間 `t₀+1` 爆破。剩餘誠實界線：`h` 非自治（依賴 `t₀`），
自治化 = (A) 的 GPAC 核心。 -/
theorem halts_imp_smooth_blowup {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M} (h : Simulates F step enc)
    (c : Γ) (H : Set Γ) (n : ℕ) (hn : step^[n + 1] c ∈ H) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ F.φ t₀ (enc c) ∈ enc '' H ∧
      (∀ t ≤ t₀, smoothSwitchSol t₀ t = 1) ∧
      (∀ m : ℕ∞, ContDiffOn ℝ m (smoothSwitchSol t₀) (Set.Iio (t₀ + 1))) ∧
      (∀ t, t < t₀ + 1 → HasDerivAt (smoothSwitchSol t₀)
        (deriv Real.smoothTransition (t - t₀) * smoothSwitchSol t₀ t ^ 2) t) ∧
      Filter.Tendsto (smoothSwitchSol t₀) (nhdsWithin (t₀ + 1) (Set.Iio (t₀ + 1)))
        Filter.atTop := by
  obtain ⟨t₀, ht₀, hmem⟩ := halts_imp_orbitReaches h c H n hn
  exact ⟨t₀, ht₀, hmem, fun t ht ↦ smoothSwitchSol_eq_one t₀ t ht,
    fun m ↦ smoothSwitchSol_contDiffOn t₀ m,
    fun t ht ↦ smoothSwitchSol_hasDerivAt t₀ t ht, smoothSwitchSol_tendsto_atTop t₀⟩

end FluidTuring
