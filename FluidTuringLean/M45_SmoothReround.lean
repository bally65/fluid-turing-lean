import Mathlib
import FluidTuringLean.M43_LeapfrogOrbit

/-!
# Module 45 — GPAC σ 構造 Brick G3：smooth 數位穩健 / re-rounding（`sround`）

**方向三 GPAC 線**（unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。G3 = **數位穩健原語**：一個光滑
`sround : ℝ→ℝ`，**迭代**它把 `x` 拉向**最近整數**（error-correction），使 leapfrog 每步的 `e^{-C}` 殘差
**不累積**（破 Brick 6 **Wall B**：一般擴張 TM 的誤差發散）。

## ★構造決策（硬）：週期 `sin`，不是 `smoothTransition`★

`sround(x) = x − sin(2πx)/(2π)`（Branicky error-correction，`α = 1/(2π)`）。**整數 = 超吸引不動點**
（`g'(k) = 1 − cos 0 = 0`）、半整數 = 斥點 ⟹ 迭代把點拉向最近整數。導數**閉式** `g'(x) = 1 − cos(2πx)`，
`HasDerivAt` 由 mathlib trig 直給——延續 M39–43「顯式函數 + `HasDerivAt`、零抽象 ODE」紀律
（`sin/cos` 是 GPAC 可生成 `y''=−ω²y`，非作弊）。

**為何不用 `smoothTransition`**（G1/M41 的 gating 工具）：它**單調**（平坦→升→平坦），是週期 re-rounding
的**錯工具**；且 mathlib 對它**零導數界引理**（`deriv Real.smoothTransition` 不透明，M44 已撞此牆），
拿不出量化 `ρ<1`。`sin` 是唯一有 mathlib 全套量化支援的路。誠實記此偏離（不破壞 M41 資產鏈）。

## 交付（8 條，皆顯式 + `HasDerivAt`、零抽象 ODE 存在性）

- `sround_zero` / `sround_add_int`（平移不變 ⟹ 有界格點免費）/ `sround_int`（整數不動點）；
- `sround_hasDerivAt`（`g' = 1 − cos(2πx)` 閉式）；
- **`sround_contract`（★CRUX★）**：basin 收縮 `|sround x − k| ≤ ρ·|x − k|`，顯式 `ρ = 1 − cos(2πδ)`
  （證法 = 導數界 + MVT `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`）；
- `sround_rho_lt_one`（`ρ<1` 於 `δ<1/4`）；`sround_iterate`（`|sround^[n] x − k| ≤ ρⁿ·|x − k|`，幾何收斂）；
- **`bounded_orbit`（★破 Wall B★）**：`e(n+1) ≤ Λ·e n + b`、`Λ<1` ⟹ `e n ≤ b/(1−Λ)`（把 M43 的發散
  `ΣLⁱ` 換成收斂遞迴；代 `Λ:=ρL、b:=ρM·e^{-C}` 得 `n`-無關界）。

## ★誠實範圍（禁 overclaim）★

`sround` **只**是離散誤差校正原語——**不** decode 組態、**不** extract 讀符號、**不**判定 halting。
**禁**從 G3 宣稱線三 undecidability。真心臟已**移到下游**（皆多月 / 部分 paper-blocked）：
G2（smooth 讀符號 `⌊k·y⌋` 於格點**精確**——mathlib **無** smooth floor，且 G4 需 `σ(enc c)=enc(step c)`
**字面相等**非 ε-近似，此為**新 crux、比 G3 難**）、G4（顯式單步 σ 組成 + 格點精確恆等）、G5（tube 不變式
歸納，接 `bounded_orbit` + M43 `tracks_ideal`）、G6（splice 到 M16/M30 停機不可判定）、自治流黏合（GPAC
bump-train 振子，paper-blocked）。**`ρ<1` 只在 `δ<1/4` 嚴格**（半整數是斥不動點、`ρ→1` 於 cell 邊界）
= smooth rounding 內稟，下游必須全程用 `δ`-tube。
-/

namespace FluidTuring

open Real

/-- **smooth re-rounding 原語**：`sround x = x − sin(2πx)/(2π)`。整數 = 超吸引不動點、半整數 = 斥點；
迭代拉向最近整數。導數閉式 `g'(x) = 1 − cos(2πx)`。 -/
noncomputable def sround (x : ℝ) : ℝ := x - Real.sin (2 * π * x) / (2 * π)

theorem sround_zero : sround 0 = 0 := by
  simp [sround]

/-- **平移不變（整數）**：`sround (x + n) = sround x + n`（`n : ℤ`）。有界格點 re-rounding 免費。 -/
theorem sround_add_int (x : ℝ) (n : ℤ) : sround (x + n) = sround x + n := by
  simp only [sround]
  rw [show 2 * π * (x + (n : ℝ)) = 2 * π * x + (n : ℤ) * (2 * π) by ring,
    Real.sin_add_int_mul_two_pi]
  ring

/-- **整數不動點**：`sround k = k`。 -/
theorem sround_int (k : ℤ) : sround (k : ℝ) = (k : ℝ) := by
  have h := sround_add_int 0 k
  rwa [zero_add, sround_zero, zero_add] at h

/-- **★導數閉式★**：`HasDerivAt sround (1 − cos(2πx)) x`（延續顯式 HasDerivAt 紀律；避 instance-diamond）。 -/
theorem sround_hasDerivAt (x : ℝ) :
    HasDerivAt sround (1 - Real.cos (2 * π * x)) x := by
  have hu : HasDerivAt (fun y : ℝ => 2 * π * y) (2 * π) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * π)
  have hsin : HasDerivAt (fun y => Real.sin (2 * π * y))
      (Real.cos (2 * π * x) * (2 * π)) x := (Real.hasDerivAt_sin _).comp x hu
  have hdiv : HasDerivAt (fun y => Real.sin (2 * π * y) / (2 * π))
      (Real.cos (2 * π * x) * (2 * π) / (2 * π)) x := hsin.div_const _
  have hmain : HasDerivAt sround
      (1 - Real.cos (2 * π * x) * (2 * π) / (2 * π)) x :=
    (hasDerivAt_id x).sub hdiv
  have heq : (1 : ℝ) - Real.cos (2 * π * x) * (2 * π) / (2 * π)
      = 1 - Real.cos (2 * π * x) := by
    rw [mul_div_assoc, div_self (by positivity : (2 * π) ≠ 0), mul_one]
  rwa [heq] at hmain

/-- **★CRUX：basin 收縮★**：`|x − k| ≤ δ ≤ 1/4 ⟹ |sround x − k| ≤ (1 − cos(2πδ))·|x − k|`。
證 = 導數界 `|1 − cos(2πy)| ≤ 1 − cos(2πδ)`（cos 週期化 + 單調）+ MVT。 -/
theorem sround_contract (k : ℤ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) {x : ℝ}
    (hx : |x - (k : ℝ)| ≤ δ) :
    |sround x - (k : ℝ)| ≤ (1 - Real.cos (2 * π * δ)) * |x - (k : ℝ)| := by
  have hpi := Real.pi_pos
  set s := Set.Icc ((k : ℝ) - δ) ((k : ℝ) + δ) with hsdef
  have hconv : Convex ℝ s := convex_Icc _ _
  have hbound : ∀ y ∈ s, ‖1 - Real.cos (2 * π * y)‖ ≤ 1 - Real.cos (2 * π * δ) := by
    intro y hy
    rw [hsdef, Set.mem_Icc] at hy
    have hyk : |y - (k : ℝ)| ≤ δ := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have hper : Real.cos (2 * π * y) = Real.cos (2 * π * |y - (k : ℝ)|) := by
      have h1 : 2 * π * y = 2 * π * (y - (k : ℝ)) + (k : ℤ) * (2 * π) := by
        ring
      rw [h1, Real.cos_add_int_mul_two_pi, ← Real.cos_abs (2 * π * (y - (k : ℝ))),
        abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have hcos : Real.cos (2 * π * δ) ≤ Real.cos (2 * π * y) := by
      rw [hper]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.pi_pos]
      · nlinarith [abs_nonneg (y - (k : ℝ)), Real.pi_pos]
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one (2 * π * y)])]
    linarith [hcos]
  have hderiv : ∀ y ∈ s, HasDerivWithinAt sround (1 - Real.cos (2 * π * y)) s y :=
    fun y _ => (sround_hasDerivAt y).hasDerivWithinAt
  have hks : (k : ℝ) ∈ s := by rw [hsdef, Set.mem_Icc]; constructor <;> linarith
  have hxs : x ∈ s := by
    rw [hsdef, Set.mem_Icc]; rw [abs_le] at hx; constructor <;> linarith [hx.1, hx.2]
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hks hxs
  rwa [sround_int k, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt

/-- **`ρ<1` 於 `δ<1/4`**：`1 − cos(2πδ) < 1`（`cos(2πδ) > 0`）。`δ=1/4` 退化（`ρ=1`）。 -/
theorem sround_rho_lt_one {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 4) :
    1 - Real.cos (2 * π * δ) < 1 := by
  have hpi := Real.pi_pos
  have hpos : 0 < Real.cos (2 * π * δ) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    constructor <;> nlinarith [Real.pi_pos]
  linarith

/-- **★G3c 迭代收斂★**：`|x − k| ≤ δ ≤ 1/4 ⟹ |sround^[n] x − k| ≤ ρⁿ·|x − k|`（幾何收斂到格點）。
basin 不變 + 歸納（避 `ContractingWith`：`sround` 非全域收縮）。 -/
theorem sround_iterate (k : ℤ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    ∀ (n : ℕ) (x : ℝ), |x - (k : ℝ)| ≤ δ →
      |sround^[n] x - (k : ℝ)| ≤ (1 - Real.cos (2 * π * δ)) ^ n * |x - (k : ℝ)| := by
  have hpi := Real.pi_pos
  have hρ0 : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    linarith [Real.cos_le_one (2 * π * δ)]
  have hcos_nonneg : 0 ≤ Real.cos (2 * π * δ) := by
    apply Real.cos_nonneg_of_mem_Icc
    rw [Set.mem_Icc]; constructor <;> nlinarith [Real.pi_pos]
  have hρ1 : 1 - Real.cos (2 * π * δ) ≤ 1 := by linarith
  intro n
  induction n with
  | zero => intro x hx; simp
  | succ m ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have hbasin : |sround^[m] x - (k : ℝ)| ≤ δ :=
      le_trans (ih x hx) (by
        calc (1 - Real.cos (2 * π * δ)) ^ m * |x - (k : ℝ)|
            ≤ 1 * δ :=
              mul_le_mul (pow_le_one₀ hρ0 hρ1) hx (abs_nonneg _) zero_le_one
          _ = δ := one_mul δ)
    calc |sround (sround^[m] x) - (k : ℝ)|
        ≤ (1 - Real.cos (2 * π * δ)) * |sround^[m] x - (k : ℝ)| :=
          sround_contract k hδ0 hδ hbasin
      _ ≤ (1 - Real.cos (2 * π * δ)) *
            ((1 - Real.cos (2 * π * δ)) ^ m * |x - (k : ℝ)|) :=
          mul_le_mul_of_nonneg_left (ih x hx) hρ0
      _ = (1 - Real.cos (2 * π * δ)) ^ (m + 1) * |x - (k : ℝ)| := by
          rw [pow_succ]; ring

/-- **★破 Wall B★**：`0≤Λ<1`、`0≤b`、`e 0=0`、`e(n+1) ≤ Λ·e n + b` ⟹ `e n ≤ b/(1−Λ)`（`n`-無關界）。
代 `Λ := ρL`（re-rounded step 的 tube-Lipschitz、選 `δ` 使 `ρL<1`）、`b := ρM·e^{-C}` ⟹ 誤差**收斂**、
tube 不變式對**一般擴張 TM** 成立（M43 `error_accumulation` 的發散 `ΣLⁱ` 被此收斂遞迴取代）。 -/
theorem bounded_orbit {e : ℕ → ℝ} {Λ b : ℝ} (h0 : 0 ≤ Λ) (h1 : Λ < 1) (hb : 0 ≤ b)
    (he0 : e 0 = 0) (hrec : ∀ n, e (n + 1) ≤ Λ * e n + b) :
    ∀ n, e n ≤ b / (1 - Λ) := by
  have hne : (1 : ℝ) - Λ ≠ 0 := by linarith
  intro n
  induction n with
  | zero => rw [he0]; exact div_nonneg hb (by linarith)
  | succ m ih =>
    calc e (m + 1)
        ≤ Λ * e m + b := hrec m
      _ ≤ Λ * (b / (1 - Λ)) + b := by
          have := mul_le_mul_of_nonneg_left ih h0; linarith
      _ = b / (1 - Λ) := by field_simp; ring

end FluidTuring
