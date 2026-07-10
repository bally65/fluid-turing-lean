import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Module 39 — Analog-computation 流：Brick 1（Branicky「steer-to-target」ODE 原子）

**方向三（真·open research、多 session/多月、mathlib 從零）**：Graça/Huynh 路線——TM 組態編碼成
實數、造一個**光滑**（甚至解析/多項式）ODE 使其解軌道**逐步模擬** TM，且 blowup/到達不可判定。
關鍵是「動力學本身計算」（非 M38 障礙的靜態連續讀出），繞過 clopen 障礙。

**mathlib 現況**：有 ODE 存在性（Picard–Lindelöf）、光滑函數、`Real.exp`；**無**整套 TM→向量場
analog 模擬（Branicky/Graça 的迭代編碼、round 函數、targeting 系統皆需從零）。故整條線 paper-blocked。

**Brick 1（本模組、可現做）= Branicky 的「steer-to-target」原子**：analog computation 用「每單位
時間把狀態 `y` 導向目標 `b = σ(舊態)`（σ = 一步 TM 更新）」實現離散迭代。最基本 gadget = 線性
ODE `y' = -C (y - b)`（`C>0`），顯式解 `y(t) = b + (y₀-b) e^{-Ct}` **單調趨近 `b`**——即「一步
targeting」。本模組顯式構造 + 證 `HasDerivAt`（真滿足 ODE）+ `→ b`（targeting 成功）。

這是方向三的**第一塊真磚**（M11/M35 的顯式解手法）；上層（round 編碼、逐步排程、undecidability
轉移）仍是 paper-blocked 的多月工程，明寫於 `docs/UNDECIDABILITY_LINE.md`。
-/

namespace FluidTuring

open Real Filter Topology

/-- **Branicky targeting 解**：`y(t) = b + (y₀ - b) e^{-C t}`——線性 targeting ODE
`y' = -C(y-b)` 的顯式解（把 `y` 從 `y₀` 導向目標 `b`）。 -/
noncomputable def targetingSol (y₀ b C t : ℝ) : ℝ := b + (y₀ - b) * Real.exp (-(C * t))

/-- **★targeting ODE★**：顯式解真滿足 `y' = -C (y - b)`（steer-to-target 動力學）。 -/
theorem targetingSol_hasDerivAt (y₀ b C t : ℝ) :
    HasDerivAt (targetingSol y₀ b C) (-C * (targetingSol y₀ b C t - b)) t := by
  have hlin : HasDerivAt (fun t : ℝ ↦ -(C * t)) (-C) t := by
    simpa using (hasDerivAt_id t).const_mul (-C)
  have hexp : HasDerivAt (fun t : ℝ ↦ Real.exp (-(C * t))) (Real.exp (-(C * t)) * -C) t :=
    hlin.exp
  have hy : HasDerivAt (targetingSol y₀ b C)
      (0 + (y₀ - b) * (Real.exp (-(C * t)) * -C)) t :=
    (hasDerivAt_const t b).add (hexp.const_mul (y₀ - b))
  convert hy using 1
  simp only [targetingSol]
  ring

/-- **★targeting 成功★**：`C > 0` ⟹ 解**趨近目標** `b`（`t → ∞`）。即一步 analog targeting
把狀態導到 `σ(舊態)`——離散迭代的連續實現核心。 -/
theorem targetingSol_tendsto (y₀ b C : ℝ) (hC : 0 < C) :
    Tendsto (targetingSol y₀ b C) atTop (𝓝 b) := by
  have hCt : Tendsto (fun t : ℝ ↦ C * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC tendsto_id
  have harg : Tendsto (fun t : ℝ ↦ -(C * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hCt
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-(C * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmul : Tendsto (fun t : ℝ ↦ (y₀ - b) * Real.exp (-(C * t))) atTop (𝓝 ((y₀ - b) * 0)) :=
    hexp.const_mul (y₀ - b)
  have hadd : Tendsto (targetingSol y₀ b C) atTop (𝓝 (b + (y₀ - b) * 0)) :=
    tendsto_const_nhds.add hmul
  simpa using hadd

end FluidTuring
