import FluidTuringLean.M9_Undecidability
import FluidTuringLean.M11_BlowupODE

/-!
# Module 12 — 停機觸發爆破橋（(A) 的第一塊：trigger 架構）

**(A) TM → 光滑 ODE 模擬**的路徑分解出的第一個可達塊。關鍵觀察：本專案的懸掛流住在
**緊空間**——緊空間**不可能 blowup**（爆破 = 逃逸到無窮、需要無界相空間）。所以
Graça–Buescu–Campagnolo 2009 不可判定 blowup 證明的真架構是**兩層**：

1. **模擬層**（有界、永不爆）：TM 動力學——我們已有（M6 懸掛流 `Simulates`）。
2. **觸發層**：一條耦合座標 `z`，計算未停機時恆定（`z' = 0`）、軌道進入停機區的
   時刻 `t₀` 後切換到 Riccati 爆破機制（`z' = z²`，M11 原子）→ `z` 於**有限時間
   `t₀ + 1`** 爆掉。

於是「**停機 ⟺ 耦合系統有限時間爆破**」。本模組把觸發層 + 「停機 ⟹ 爆破」方向
機器化（組 M9 `halts_imp_orbitReaches` × M11 `blowupSol`）。

**誠實界線**：(i) 這裡的開關是**混成（hybrid/switched）**系統——`z' = h(t)·z²` 的
`h` = 停機指示（分段常數、切換點不可微），把它實現成**單一光滑自治向量場**（含
用光滑 bump/clock 消掉切換）正是 (A) 剩餘的多月硬核（GPAC/analog computation）。
(ii) 逆向「不停機 ⟹ 不爆」需要「軌道不誤入編碼停機區」的忠實性——`Simulates`
只給前向實現、不禁止巧合穿越；該忠實性是模擬層的額外不變量（未建、誠實標示）。
本塊價值 = 把不可判定 blowup 證明的 **trigger 架構**（reach → blowup 的轉換器）
機器驗證，M9（積分側）與 M11（微分側）由此第一次真正**耦合**。
-/

namespace FluidTuring

/-- **開關耦合解**：停機前恆 `1`、停機時刻 `t₀` 後切入 Riccati 爆破
（M11 原子平移到爆破時刻 `T = t₀ + 1`；在 `t = t₀` 兩支皆值 `1`、連續銜接）。 -/
noncomputable def switchSol (t₀ : ℝ) : ℝ → ℝ :=
  fun t ↦ if t ≤ t₀ then 1 else blowupSol (t₀ + 1) t

/-- 計算未完成（`t ≤ t₀`）：耦合座標恆定 `1`——模擬期間不爆。 -/
theorem switchSol_eq_one (t₀ t : ℝ) (h : t ≤ t₀) : switchSol t₀ t = 1 := if_pos h

/-- 停機前（`t < t₀`）：`z' = 0`（觸發未開、無動力）。 -/
theorem switchSol_hasDerivAt_pre (t₀ t : ℝ) (h : t < t₀) :
    HasDerivAt (switchSol t₀) 0 t := by
  have heq : switchSol t₀ =ᶠ[nhds t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact if_pos (le_of_lt hs)
  exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq

/-- 停機後（`t₀ < t < t₀ + 1`）：**`z' = z²`**（Riccati 爆破機制、M11 原子接手）。 -/
theorem switchSol_hasDerivAt_post (t₀ t : ℝ) (h1 : t₀ < t) (h2 : t < t₀ + 1) :
    HasDerivAt (switchSol t₀) (switchSol t₀ t ^ 2) t := by
  have heq : switchSol t₀ =ᶠ[nhds t] blowupSol (t₀ + 1) := by
    filter_upwards [Ioi_mem_nhds h1] with s hs
    exact if_neg (not_le.mpr hs)
  have hval : switchSol t₀ t = blowupSol (t₀ + 1) t := if_neg (not_le.mpr h1)
  rw [hval]
  exact (blowupSol_hasDerivAt (t₀ + 1) t h2).congr_of_eventuallyEq heq

/-- **有限時間爆破**：`t → (t₀+1)⁻` 時耦合座標爆到 `+∞`——停機觸發後恰一單位時間爆掉。 -/
theorem switchSol_tendsto_atTop (t₀ : ℝ) :
    Filter.Tendsto (switchSol t₀) (nhdsWithin (t₀ + 1) (Set.Iio (t₀ + 1)))
      Filter.atTop := by
  refine Filter.Tendsto.congr' ?_ (blowupSol_tendsto_atTop (t₀ + 1))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith : t₀ < t₀ + 1))]
    with s hs
  exact (if_neg (not_le.mpr hs)).symm

/-- **★停機 ⟹ 混成系統有限時間爆破★（(A) 第一塊，M9 × M11 耦合）**：若離散計算從
`c` 於 `n+1` 步進入停機區 `H`，則存在觸發時刻 `t₀ > 0`（M9 的軌道抵達時間），使耦合
座標 `switchSol t₀`：計算期間恆 `1`（不爆）、`t₀` 後滿足 `z' = z²`、於**有限時間
`t₀ + 1` 爆掉**。= 把「停機」轉換成「有限時間 blowup」的機器驗證 trigger。

逆向（不停機 ⟹ 全域存在）由 `z ≡ 1`（`z' = 0` 的全域解）承載，但需模擬層的
軌道忠實性不變量（見模組 docstring、誠實未建）。 -/
theorem halts_imp_hybrid_blowup {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M} (h : Simulates F step enc)
    (c : Γ) (H : Set Γ) (n : ℕ) (hn : step^[n + 1] c ∈ H) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ F.φ t₀ (enc c) ∈ enc '' H ∧
      (∀ t ≤ t₀, switchSol t₀ t = 1) ∧
      (∀ t, t₀ < t → t < t₀ + 1 → HasDerivAt (switchSol t₀) (switchSol t₀ t ^ 2) t) ∧
      Filter.Tendsto (switchSol t₀) (nhdsWithin (t₀ + 1) (Set.Iio (t₀ + 1)))
        Filter.atTop := by
  obtain ⟨t₀, ht₀, hmem⟩ := halts_imp_orbitReaches h c H n hn
  exact ⟨t₀, ht₀, hmem, fun t ht ↦ switchSol_eq_one t₀ t ht,
    fun t h1 h2 ↦ switchSol_hasDerivAt_post t₀ t h1 h2, switchSol_tendsto_atTop t₀⟩

end FluidTuring
