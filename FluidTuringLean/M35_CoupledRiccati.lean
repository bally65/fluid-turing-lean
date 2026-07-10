import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.Order.Field

/-!
# Module 35 — 耦合 Riccati 顯式解（方向一 Brick A：真·自治耦合 blowup 的分析核心）

**目標（審計 #1 的真解法）**：把「字面 blowup」焊成**單一自治耦合向量場**——`z' = a(t) z²`，其中
`a(t) = g(X(t))`（X = 懸掛流、g = 停機區平滑指示）。這樣 blowup 是真 ODE 的解逃逸，非 case-split。

**關鍵（不需 mathlib 抽象 ODE 存在性）**：像 M11/M13 顯式構造解。耦合 Riccati `z' = a(t) z²`
（`z(0)=z₀`）的**顯式解** = `z(t) = z₀ / (1 - z₀ A(t))`，`A(t) = ∫₀ᵗ a`。本塊（Brick A）證這個
顯式 `z` **真滿足** `z' = a(t) z²`（給 `A' = a`，如 FTC 對連續 `a` 供），用 `HasDerivAt.inv` + 鏈式。

爆破時序（`z → +∞` ⟺ `z₀ A(t) → 1`）= Brick B；接懸掛流 `a = g(X)`、`A→∞ ⟺ 到達停機區 ⟺ 停機`
= Brick C；封頂 = Brick D。
-/

namespace FluidTuring

/-- 耦合 Riccati 的**顯式解**：`z(t) = z₀ / (1 - z₀ · A(t))`，`A` = 係數 `a` 的原函數（`∫₀ᵗ a`）。 -/
noncomputable def coupledRiccati (z₀ : ℝ) (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  z₀ / (1 - z₀ * A t)

/-- **★耦合 Riccati 的 ODE★**：給 `A' = a`（如 FTC），顯式解滿足 `z' = a · z²`——即 `z` 是
`z' = a(t) z²`（`a(t) = g(X(t))` 的耦合 Riccati）的**真解**（非 case-split）。 -/
theorem coupledRiccati_hasDerivAt (z₀ : ℝ) (A : ℝ → ℝ) (a t : ℝ)
    (hA : HasDerivAt A a t) (hne : 1 - z₀ * A t ≠ 0) :
    HasDerivAt (coupledRiccati z₀ A) (a * coupledRiccati z₀ A t ^ 2) t := by
  have hD : HasDerivAt (fun s ↦ 1 - z₀ * A s) (0 - z₀ * a) t :=
    HasDerivAt.sub (hasDerivAt_const t (1 : ℝ)) (HasDerivAt.const_mul z₀ hA)
  have hz : HasDerivAt (fun s ↦ z₀ * (1 - z₀ * A s)⁻¹)
      (z₀ * (-(0 - z₀ * a) / (1 - z₀ * A t) ^ 2)) t :=
    HasDerivAt.const_mul z₀ (HasDerivAt.inv hD hne)
  have hfun : coupledRiccati z₀ A = fun s ↦ z₀ * (1 - z₀ * A s)⁻¹ := by
    funext s; rw [coupledRiccati, div_eq_mul_inv]
  rw [hfun]
  convert hz using 1
  field_simp
  ring

open Filter Topology in
/-- **★爆破時序★（Brick B）**：`z₀ > 0`，若分母 `1 - z₀ A(t) → 0⁺`（從正側趨零）當 `t → T⁻`，
則耦合 Riccati 解 `→ +∞`——**字面有限時間 blowup**。（耦合中 `A(t)=∫₀ᵗ g(X)`；`z₀ A → 1` ⟺
X 累積「停機區停留時間」達門檻 ⟺ 到達停機區。） -/
theorem coupledRiccati_tendsto_atTop (z₀ : ℝ) (A : ℝ → ℝ) (T : ℝ) (hz : 0 < z₀)
    (hD : Tendsto (fun t ↦ 1 - z₀ * A t) (𝓝[<] T) (𝓝[>] (0 : ℝ))) :
    Tendsto (coupledRiccati z₀ A) (𝓝[<] T) atTop := by
  have h1 : Tendsto (fun t ↦ (1 - z₀ * A t)⁻¹) (𝓝[<] T) atTop :=
    tendsto_inv_nhdsGT_zero.comp hD
  have h2 : Tendsto (fun t ↦ z₀ * (1 - z₀ * A t)⁻¹) (𝓝[<] T) atTop :=
    Filter.Tendsto.const_mul_atTop hz h1
  have hfun : coupledRiccati z₀ A = fun t ↦ z₀ * (1 - z₀ * A t)⁻¹ := by
    funext t; rw [coupledRiccati, div_eq_mul_inv]
  rw [hfun]; exact h2

end FluidTuring
