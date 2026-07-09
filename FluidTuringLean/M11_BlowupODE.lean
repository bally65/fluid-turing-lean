import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.Order.Field

/-!
# Module 11 — 顯式有限時間 blowup ODE 原子（M10 的微分側接地）

M10 把「blowup 偵測不可判定」的**還原邏輯**機器化，`blowsUp` 是抽象謂詞。本模組給
**一個真 ODE 的顯式有限時間 blowup**，把那個抽象謂詞接到真微積分物件：

`y(t) = 1/(T - t)` 在 `[0, T)` 上滿足 **`y' = y²`**（Riccati/爆破原型），且 `t → T⁻` 時
`y → +∞`——**有限時間 blowup 的顯式見證**。這是 M10→真 ODE 路徑上「微分側原子」(B)
的落地；剩「(A) TM → 光滑向量場模擬（analog computation/GPAC）」是 mathlib 尚無的多月硬核。

（mathlib 有 `PicardLindelof` 局部存在、`Gronwall` 唯一性，但無顯式 blowup 範例。）
-/

namespace FluidTuring

/-- 爆破解 `y(t) = (T - t)⁻¹`。 -/
noncomputable def blowupSol (T : ℝ) : ℝ → ℝ := fun t ↦ (T - t)⁻¹

/-- **`y' = y²`**：爆破解在 `t < T` 滿足 Riccati 型方程（爆破的微分機制）。 -/
theorem blowupSol_hasDerivAt (T t : ℝ) (h : t < T) :
    HasDerivAt (blowupSol T) (blowupSol T t ^ 2) t := by
  have hne : T - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  have h1 : HasDerivAt (fun s ↦ T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have h2 := h1.inv hne
  have heq : -(-1) / (T - t) ^ 2 = blowupSol T t ^ 2 := by
    simp only [blowupSol, inv_pow, neg_neg]
    norm_num
  rwa [heq] at h2

/-- **有限時間 blowup**：`t → T⁻` 時解爆到 `+∞`（極大存在區間有界、非全域）。 -/
theorem blowupSol_tendsto_atTop (T : ℝ) :
    Filter.Tendsto (blowupSol T) (nhdsWithin T (Set.Iio T)) Filter.atTop := by
  have hsub : Filter.Tendsto (fun t ↦ T - t) (nhdsWithin T (Set.Iio T))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Filter.Tendsto (fun t ↦ T - t) (nhds T) (nhds (T - T)) :=
        tendsto_const_nhds.sub Filter.tendsto_id
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi]
      simp only [Set.mem_Iio] at ht
      linarith
  have := hsub.inv_tendsto_nhdsGT_zero
  simp only [Pi.inv_def] at this
  exact this

end FluidTuring
