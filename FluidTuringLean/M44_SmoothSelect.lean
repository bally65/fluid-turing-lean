import FluidTuringLean.M41_ConcreteWindow

/-!
# Module 44 — GPAC σ 構造 Brick G1：smooth 分支（`smoothSelect`）

**方向三 GPAC 線**（unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。目標 = 造光滑 `σ:ℝ→ℝ` 逐步模擬 TM。
本磚 = **G1：smooth 分支原子**——TM 轉移表的有限 case 分析（「讀頭若為符號 X 則做 A、否則做 B」）
的光滑化基石。用 M41 `Real.smoothTransition`（閉式平坦→升→平坦）造 smooth if-then-else：

`smoothSelect s a b = a + smoothTransition(s)·(b-a)`：`s≤0` **恰** `a`、`s≥1` **恰** `b`、中間光滑。

延續 M39-43 紀律（顯式函數 + `HasDerivAt`、零抽象 ODE 存在性）。n-way 分支（`|Q|×|Γ|` 個 case）=
本 2-way 原子的巢狀/疊加（後續 G-brick）。

**誠實範圍**：本磚**只**交付 smooth 2-way 分支原語。GPAC σ 的真核心（G3 smooth 數位穩健 /
re-rounding、G4 單步組成、G5 tube 不變式）仍是多月 research（見路線圖）；**未**宣稱模擬了 TM。
-/

namespace FluidTuring

open Real

/-- **smooth 分支**：`s≤0 → a`、`s≥1 → b`、中間 `smoothTransition` 光滑插值。GPAC case 分析原子。 -/
noncomputable def smoothSelect (s a b : ℝ) : ℝ := a + Real.smoothTransition s * (b - a)

/-- **左分支精確**：`s ≤ 0 ⟹ smoothSelect s a b = a`（`smoothTransition` 平坦 0）。 -/
theorem smoothSelect_left {s : ℝ} (h : s ≤ 0) (a b : ℝ) : smoothSelect s a b = a := by
  rw [smoothSelect, Real.smoothTransition.zero_of_nonpos h]; ring

/-- **右分支精確**：`1 ≤ s ⟹ smoothSelect s a b = b`（`smoothTransition` 飽和 1）。 -/
theorem smoothSelect_right {s : ℝ} (h : 1 ≤ s) (a b : ℝ) : smoothSelect s a b = b := by
  rw [smoothSelect, Real.smoothTransition.one_of_one_le h]; ring

/-- **★smooth★**：`smoothSelect` 對閾值 `s` 可微，導數 `= smoothTransition'(s)·(b-a)`（case 分析
光滑化 = ODE 場可用）。= M41 `smoothTransition.contDiffAt` + `HasDerivAt.mul_const/.const_add`。 -/
theorem smoothSelect_hasDerivAt (s a b : ℝ) :
    HasDerivAt (fun u => smoothSelect u a b) (deriv Real.smoothTransition s * (b - a)) s := by
  have h1 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by norm_num)).hasDerivAt
  exact (h1.mul_const (b - a)).const_add a

/-- **介於兩分支之間**：`a ≤ b ⟹ a ≤ smoothSelect s a b ≤ b`（`smoothTransition ∈ [0,1]` 凸組合）。
分支值有界 = 後續 tube 幾何（G5）所需。 -/
theorem smoothSelect_mem {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    a ≤ smoothSelect s a b ∧ smoothSelect s a b ≤ b := by
  have h0 := Real.smoothTransition.nonneg s
  have h1 := Real.smoothTransition.le_one s
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  constructor
  · rw [smoothSelect]; nlinarith [mul_nonneg h0 hd]
  · rw [smoothSelect]; nlinarith [mul_le_mul_of_nonneg_right h1 hd]

end FluidTuring
