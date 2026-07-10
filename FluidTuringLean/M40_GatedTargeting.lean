import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import FluidTuringLean.M39_AnalogTargeting

/-!
# Module 40 — Analog-computation 流：Brick 2（gated/windowed targeting + HOLD 凍結原語）

**方向三 Brick 2**（承接 M39 Brick 1 steer-to-target）。Branicky 迭代機制的**排程原子**：把
Brick 1「永遠開著」的收縮（`y' = -C(y-b)`，係數常數）換成**閘控**收縮 `y' = -C·φ(t)·(y-b)`，
`φ` = 窗函數（集中在計算窗 `[k,k+1]`）。得**新能力**（Brick 1 沒有的）：

- **HOLD / 凍結**：空窗 `φ(t)=0 ⟹ y'(t)=0` ⟹ 狀態**精確不動**。這是 leapfrog 時鐘（Brick 3）
  「兩變數輪流更新、另一個持值」所需的原子。
- **窗內 targeting**：累積窗質量 `Φ = ∫φ → ∞` ⟹ `y → b`（把 `y` 推到任意接近 `σ(舊態)`）。

**作法（同 M35/M39 紀律）**：顯式解 `y(t) = b + (y₀-b) e^{-C·Φ(t)}`（`Φ' = φ`），證 `HasDerivAt`
（真滿足閘控 ODE）——**不碰 mathlib 抽象 ODE 存在性**。`Φ` 保持**抽象假設**（`HasDerivAt Φ φ t`
/ `Tendsto Φ atTop atTop`），把「窗選擇、`σ` 編碼、leapfrog 組裝」外包給上層（誠實範圍）。
`targetingGatedSol_id`（`Φ = id ⟹` 回 Brick 1）**機器背書**承接——見證框架可實例化到真解（非弱
空洞）。**誠實補注**：`Φ = id`（`φ≡1`）是**恆開窗、從不 gate** 的退化實例；真正**非退化**的閘控
`Φ`（先平坦後上升）需 paper-blocked 的 bump FTC 反導數，只能經抽象 `Φ` 觸及（同 M35 抽象原函數之限）。

**Brick 2 之上仍 paper-blocked**（明寫）：具體 bump 的 FTC 反導數（`Φ = ∫₀ᵗφ`，需整層
MeasureTheory）、round/decode（TM 態 ↔ 實數，不連續）、leapfrog 排程、undecidability 轉移。
本磚**只**交付「給定常數目標 `b` 的一步 gated steer + HOLD 凍結原語」，**不**宣稱模擬了機器。
-/

namespace FluidTuring

open Real Filter Topology

/-- **Gated（windowed）targeting 解**：`y(t) = b + (y₀-b)·exp(-(C·Φ t))`，`Φ` = 窗函數 `φ` 的
累積活化 / 原函數（`Φ' = φ`）。係數 `C·φ` 把 Brick 1 恆開的收縮（`φ≡1`）變成閘控（`φ≥0` ⟹
流永遠「收縮或凍結、絕不擴張」）。Brick 1 = `Φ = id`（`φ≡1`）特例（見 `targetingGatedSol_id`）。 -/
noncomputable def targetingGatedSol (y₀ b C : ℝ) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  b + (y₀ - b) * Real.exp (-(C * Φ t))

/-- **★gated ODE★**：給 `HasDerivAt Φ φ t`，顯式解真滿足閘控 steer `y' = -C·φ·(y-b)`。 -/
theorem targetingGatedSol_hasDerivAt (y₀ b C : ℝ) (Φ : ℝ → ℝ) (φ t : ℝ)
    (hΦ : HasDerivAt Φ φ t) :
    HasDerivAt (targetingGatedSol y₀ b C Φ)
      (-C * φ * (targetingGatedSol y₀ b C Φ t - b)) t := by
  have hlin : HasDerivAt (fun t ↦ -(C * Φ t)) (-(C * φ)) t := (hΦ.const_mul C).neg
  have hexp : HasDerivAt (fun t ↦ Real.exp (-(C * Φ t)))
      (Real.exp (-(C * Φ t)) * -(C * φ)) t := hlin.exp
  have hy : HasDerivAt (targetingGatedSol y₀ b C Φ)
      (0 + (y₀ - b) * (Real.exp (-(C * Φ t)) * -(C * φ))) t :=
    (hasDerivAt_const t b).add (hexp.const_mul (y₀ - b))
  convert hy using 1
  simp only [targetingGatedSol]
  ring

/-- **★HOLD（導數層）★**：窗關（`HasDerivAt Φ 0 t`，即 `φ t = 0`）⟹ `y'(t) = 0` ⟹ 狀態凍結。
leapfrog 另一變數在空窗持值的關鍵原語。 -/
theorem targetingGatedSol_hold (y₀ b C : ℝ) (Φ : ℝ → ℝ) (t : ℝ)
    (hΦ : HasDerivAt Φ 0 t) :
    HasDerivAt (targetingGatedSol y₀ b C Φ) 0 t := by
  have h := targetingGatedSol_hasDerivAt y₀ b C Φ 0 t hΦ
  simpa using h

/-- **★HOLD（值層）★**：`Φ s = Φ t`（空窗期 `Φ` 平坦）⟹ 解值相等。純代數（防「逐點 `y'=0`
不等於區間常值」的誤解：要整條 OFF 區間嚴格常值用本引理）。 -/
theorem targetingGatedSol_const_of_Φ_eq (y₀ b C : ℝ) (Φ : ℝ → ℝ) (s t : ℝ)
    (h : Φ s = Φ t) :
    targetingGatedSol y₀ b C Φ s = targetingGatedSol y₀ b C Φ t := by
  simp only [targetingGatedSol, h]

/-- **★targeting 成功（窗版）★**：`C > 0` 且累積窗質量 `Φ → +∞`（無限累積質量）⟹ 解**精確
收斂**到目標 `b`。**誠實補注**：本定理證的是 `Φ→∞` 的**精確極限**；實務有限窗只給 `ε`-近似
（把 `y` 推到任意接近 `σ(舊態)`），該有限版**未**在此形式化。 -/
theorem targetingGatedSol_tendsto (y₀ b C : ℝ) (Φ : ℝ → ℝ) (hC : 0 < C)
    (hΦ : Tendsto Φ atTop atTop) :
    Tendsto (targetingGatedSol y₀ b C Φ) atTop (𝓝 b) := by
  have hCΦ : Tendsto (fun t ↦ C * Φ t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC hΦ
  have harg : Tendsto (fun t ↦ -(C * Φ t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hCΦ
  have hexp : Tendsto (fun t ↦ Real.exp (-(C * Φ t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmul : Tendsto (fun t ↦ (y₀ - b) * Real.exp (-(C * Φ t))) atTop (𝓝 ((y₀ - b) * 0)) :=
    hexp.const_mul (y₀ - b)
  have hadd : Tendsto (targetingGatedSol y₀ b C Φ) atTop (𝓝 (b + (y₀ - b) * 0)) :=
    tendsto_const_nhds.add hmul
  simpa using hadd

/-- **承接 Brick 1（框架可實例化見證）**：`Φ = id`（`φ≡1`、恆開窗）機器化簡回 M39 的
`targetingSol`。把「承接 Brick 1」從口頭宣稱升為機器證。**注意**：此實例**恆開窗、不 gate**，
只反駁「框架空洞不可實例化」的弱空洞性；真正實現 gated/HOLD 新能力的非退化 `Φ` 需 paper-blocked
bump（見檔頭）。 -/
theorem targetingGatedSol_id (y₀ b C : ℝ) :
    targetingGatedSol y₀ b C (fun t ↦ t) = targetingSol y₀ b C := by
  funext t; rfl

end FluidTuring
