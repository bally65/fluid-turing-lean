import Mathlib
import FluidTuringLean.M49_SmoothStepBidir

/-!
# Module 56 — 正式封 G5 全檔 tube robustness：讀方向增益恰 `K`（zero-sorry 死牆證書）

**承 M46-M49（玩具 σ = `sigmaRL`）**。設計 scope workflow（`docs/GPAC_ROADMAP.md` 更新⑩）判 G5
（連續類比流全檔 tube robustness：固定 C^∞ 場穩健模擬**所有** N 步、誤差不累積）**已證 WALL**，
根據 = 一個 agent scratch session 裡驗過的 `pop_gain_K`。**本磚把那個 certified 事實正式收進
repo**——之前只活在 workflow transcript 裡，引用鏈斷了；現在是一個真模組。

## G5 為何是死牆（一句話）

`sigmaRL`（M49）在 plateau-exact tube 上，對編碼小誤差 `ε` 的單步作用，三個分量各不同：

| 分量 | 算子 | 對 `ε` 的增益 |
|---|---|---|
| 狀態 `q'`（`tbl2D` 讀） | plateau 上常值 | **0**（`tbl2D_zero_gain`） |
| 寫入 push（`(δw+y)/K`） | 仿射、係數 `1/K` | **1/K**（`push_gain_inv_K`，收縮） |
| **讀出 pop（`K·y−sfloor(K·y)`）** | **plateau 上仿射、係數 `K`** | **恰 `K`**（`pop_gain_K`，**膨脹**） |

`sfloor` 的 plateau 只殺「符號減法」的增益（讀出的符號本身精確）——**不殺 `K·y` 這個縮放本身**。
读方向的 Jacobian 分量 = `K > 1`。**任何**（含加權）範數下，某方向增益 `> 1` 就不可能是全域收縮
（`pop_not_contractive`：在**整個** plateau 上，pop 是**精確**仿射、係數 `K`，非僅一階近似）。
`M45.bounded_orbit` 要求收縮因子 `Λ < 1` 才能得「誤差不累積」的界——**此路不通**。放大的誤差住在
**分數**帶暫存器（`encTape` 值、合法格點間距 `K^{−ℓ}→0`，隨帶長變細），M54 的整數 latch
（`sround`/`snapExact`）**只認固定的整數格**，清不到這裡。

## 交付（全顯式、零 sorry、標準三公理）

- **`pop_affine_on_plateau`（★核心★）**：在**整個閉 plateau**（非僅局部一階）上，
  `pop(y) − pop(y₀) = K·(y − y₀)` **精確**——讀出算子在 plateau 上就是「乘 `K`」。
- **`pop_not_contractive`（★死牆證書★）**：`K > 1` ⟹ 在 plateau 上任兩相異點，
  `ρ·|y−y₀| < |pop(y)−pop(y₀)|` 對**任意** `ρ < K` 皆成立——**沒有任何** `< K` 的 Lipschitz 常數
  能界住這個算子，遑論 `< 1` 的收縮。
- `tbl2D_zero_gain`（狀態分量、`tbl2D_exact` 的一行推論）+ `push_gain_inv_K`（push 分量、平凡仿射）：
  補齊 `diag(0, 1/K, K)` 的另外兩格，讓「讀方向獨自扛下全部膨脹」這件事有完整對照。

## ★誠實範圍（禁 overclaim）★

- **本磚只封讀方向這一個分量**——不是「整個 G5 在 Lean 裡窮舉過所有可能架構」。真正一般的論證
  （任意加權範數 `‖·‖`、任意有限維線性算子，`ρ(A) ≤ ‖A‖` ⟹ 某方向增益 `>1` 全域無收縮範數）是標準
  線性代數事實，**未**在此重新形式化（那是通用工具、非本專案特定內容，形式化成本與價值不成比例）。
  `pop_not_contractive` 給的是**這個具體算子**在**這個具體座標**的直接、自足證書——**足以**支撐「G5
  正面目標死」的結論，因為 `bounded_orbit` 本就是在**這個座標**（`ŷ_R`）上要收縮。
- **不影響離散模擬**：`sigmaRL_iterate_exact`/`sigmaRL_iterate_exactB`（M50/M55）在 `ε=0` 時
  `K·0=0`，讀方向增益完全不出現——**離散迭代仍然字面精確**。爆炸**只**發生在「連續流插值 +
  非零殘差」的 robustness 語境（M53 的 `e^{−C}` 殘差、若試圖靠單一固定場全域清除）。
- **不影響 G4e/M55**：M55 去的是**帶邊界假設**（`bothNonempty`），與本磚（連續流 robustness）正交，
  兩者互不依賴。
- **邊際價值**：本磚是**負結果**——省下未來投入 G5 正面construction 的時間，非新增能力。
-/

namespace FluidTuring

open Real

/-! ## 讀出（pop）算子：plateau 上精確仿射、係數 `K` -/

/-- **★核心：讀出算子在 plateau 上精確仿射★**：`pop(y) − pop(y₀) = K·(y−y₀)`——非僅一階近似，
在**整個閉 plateau**（`sfloor` 常值區間）上逐點精確（直接用 `sfloor_exact_on_plateau` 消去讀出項）。 -/
theorem pop_affine_on_plateau (K : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (j₀ : ℕ) (hj₀ : j₀ < K) {y y₀ : ℝ}
    (hy : (K : ℝ) * y ∈ Set.Icc (j₀ : ℝ) ((j₀ : ℝ) + w))
    (hy₀ : (K : ℝ) * y₀ ∈ Set.Icc (j₀ : ℝ) ((j₀ : ℝ) + w)) :
    ((K : ℝ) * y - sfloor K w ((K : ℝ) * y))
        - ((K : ℝ) * y₀ - sfloor K w ((K : ℝ) * y₀))
      = (K : ℝ) * (y - y₀) := by
  rw [sfloor_exact_on_plateau K hw0 hw1 j₀ hj₀ hy.1 hy.2,
    sfloor_exact_on_plateau K hw0 hw1 j₀ hj₀ hy₀.1 hy₀.2]
  ring

/-- **★死牆證書★**：`K > 1` ⟹ 在 plateau 上任兩相異點，讀出算子把距離放大**嚴格超過任意** `ρ < K`
（含 `ρ = 1`）——**沒有**任何 Lipschitz 常數 `< K`（遑論 `< 1` 的收縮）能界住這個方向。這是
`bounded_orbit`（M45，要求收縮因子 `Λ < 1`）在讀方向**不可能適用**的直接證據。 -/
theorem pop_not_contractive (K : ℕ) (hK1 : (1 : ℝ) < (K : ℝ)) {w : ℝ}
    (hw0 : 0 < w) (hw1 : w < 1) (j₀ : ℕ) (hj₀ : j₀ < K) {y y₀ : ℝ}
    (hy : (K : ℝ) * y ∈ Set.Icc (j₀ : ℝ) ((j₀ : ℝ) + w))
    (hy₀ : (K : ℝ) * y₀ ∈ Set.Icc (j₀ : ℝ) ((j₀ : ℝ) + w))
    (hne : y ≠ y₀) {ρ : ℝ} (hρ : ρ < (K : ℝ)) :
    ρ * |y - y₀|
      < |((K : ℝ) * y - sfloor K w ((K : ℝ) * y))
          - ((K : ℝ) * y₀ - sfloor K w ((K : ℝ) * y₀))| := by
  rw [pop_affine_on_plateau K hw0 hw1 j₀ hj₀ hy hy₀, abs_mul,
    abs_of_pos (by linarith : (0 : ℝ) < (K : ℝ))]
  exact mul_lt_mul_of_pos_right hρ (abs_pos.mpr (sub_ne_zero.mpr hne))

/-! ## 另外兩分量（補齊 `diag(0, 1/K, K)` 對照） -/

/-- **狀態分量增益 0**：`tbl2D` 在 plateau 上對讀入 `R` 常值（`tbl2D_exact` 的一行推論）——
狀態輸出對編碼誤差完全不敏感。 -/
theorem tbl2D_zero_gain (δ : ℕ → ℕ → ℝ) (Q k : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (q : ℕ) (hq : q < Q) (s : ℕ) (hs : s < k) {R R' : ℝ}
    (hlo : (s : ℝ) ≤ (k : ℝ) * R) (hhi : (k : ℝ) * R ≤ (s : ℝ) + w)
    (hlo' : (s : ℝ) ≤ (k : ℝ) * R') (hhi' : (k : ℝ) * R' ≤ (s : ℝ) + w) :
    tbl2D δ Q k w (q : ℝ) R = tbl2D δ Q k w (q : ℝ) R' := by
  rw [tbl2D_exact δ Q k hw0 hw1 q hq s hs hlo hhi,
    tbl2D_exact δ Q k hw0 hw1 q hq s hs hlo' hhi']

/-- **push 分量增益 `1/K`**：`(d+y)/K` 是仿射、係數 `1/K < 1`——這個方向收縮，非膨脹。 -/
theorem push_gain_inv_K (K : ℕ) (d y₀ : ℝ) :
    HasDerivAt (fun y : ℝ => ((d : ℝ) + y) / (K : ℝ)) (1 / (K : ℝ)) y₀ := by
  simpa using ((hasDerivAt_id y₀).const_add d).div_const (K : ℝ)

end FluidTuring
