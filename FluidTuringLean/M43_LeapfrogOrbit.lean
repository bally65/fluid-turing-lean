import FluidTuringLean.M42_LeapfrogHalfStep

/-!
# Module 43 — Analog-computation 流：Brick 5（N 步 leapfrog 組合）

**方向三 Brick 5**（承接 M42 Brick 4 leapfrog 半步原子）。Brick 4 交付**單半步**：主動暫存器讀被
HOLD 的凍結目標 `σ p`，在自己的窗上滿足 Brick-3 具體閘控 ODE，窗後精確推進到
`σ p + (a₀ - σ p)·e^{-C}`（`activeHalfStep_advance`，M42:102，取 `t = k+1` **等號**）。本磚把 N 個
半步**沿斷點鏈接**，交付兩件承重：

## ★交付（誠實：γ2 = 實質 math；γ1 = 值層橋 + M42 單行實例化）★

- **γ1（精確斷點軌道 + N 窗接力鏈，σ 抽象、零誤差 claim）**：離散軌道
  `xₙ₊₁ = σ(xₙ) + (xₙ - σ(xₙ))·e^{-C}`（`leapfrogOrbit`）**恰**是 Brick-4 窗後推進值的 ℕ-摺疊。
  第 n 個 leapfrog 窗（`leapfrogWindow`）以 `xₙ` 為凍結輸入、目標 `σ xₙ` 為**常數**（非追活尾，
  見下），三件 per-window（carry-in `= xₙ` / gated-ODE / carry-out `= xₙ₊₁`）+ **接力交棒**
  `leapfrog_chain_handoff`（窗 n 在斷點 n+1 的值 = 窗 n+1 的凍結進位值）把 **N 個真解 ODE 的窗證成
  首尾相接的鏈**，斷點軌跡恰 = 離散 `leapfrogOrbit`。**此為精確恆等式，非近似**——因為 map 本身
  已把 `e^{-C}` 殘差包進定義。σ 全抽象、對任意（甚至不連續）σ 成立（同 Brick 3/4 對 σ 的免責）。

- **γ2（條件式誤差界，σ Lipschitz 明寫假設）**：把「類比軌道 `leapfrogOrbit` vs 理想 σ-迭代
  `idealOrbit n = σ^[n] x₀`」的追蹤誤差**條件化**。無條件版為**假**（擴張 σ 令誤差對固定 C 爆破），
  故本磚**絕不**宣稱 `∀σ` 的 N 步模擬。假設 (H1) `σ` 全域 `L`-Lipschitz、(H2) 每步自缺口
  `|xₙ - σ(xₙ)| ≤ M`，得幾何界 `|xₙ - σ^[n] x₀| ≤ M·e^{-C}·∑_{i<n} Lⁱ`
  （`leapfrogOrbit_tracks_ideal`）。非擴張推論（`L ≤ 1`）：`≤ N·M·e^{-C}`
  （`leapfrogOrbit_tracks_ideal_linear`）——把 Brick 4「單半步 ε-近似、殘差 `e^{-C}`」的隱憂變成
  **線性可控的累積**。（擴張 `L>1` 的模擬代價 `C = Θ(N·ln L)` **僅散文推論、未形式化**；已形式化的
  定理只到 `L≤1` 線性版 `leapfrogOrbit_tracks_ideal_linear` 與一般幾何界 `leapfrogOrbit_tracks_ideal`。）

## ★單值 staircase 是斷點抽象（明寫決策，非 thin、非偷改語義）★

`leapfrogWindow` 讀 `σ xₙ`（**xₙ 自身的凍結快照**、常數目標），**不是** `σ(live y)`。故**不落入**
Brick 4 檔頭警告的 degenerate「追活尾」（`y'=-Cφ(y-σ(y))` 目標隨 y 移動、無 Brick-3 常數解）。
單值 staircase 是**兩暫存器 leapfrog 斷點軌跡的正確抽象**：兩暫存器輪替讀寫的「時鐘」機制由
Brick 4（`leapfrog_step`、`leapfrog_halfstep_pair_hasDerivAt`）已交付並證正當；Brick 5 = 疊 N 個
模擬步、追斷點值。逐字 2D pair-orbit 的誤差分析與此單值同構、只增結構複雜度，故此處以單值兌現。

## ★誠實範圍（Brick 5 之上仍 paper-blocked，明寫，禁 overclaim）★

- **γ2 的 Lipschitz 是 round-robust 的『代理假設』、非等同**：真 TM 一步 `σ = decode→step→encode`
  在判定邊界**本質不連續**（round 有跳點），**無全域 Lipschitz 常數**。`leapfrogOrbit_tracks_ideal`
  雖字面為真，卻**無法**用真 σ 實例化。真路徑需把 (H1) 換成 **ε-tube 穩健**（σ 在有效編碼的
  ε-鄰域上 Lipschitz/收縮 ∧ 軌道證明恆停在 tube 內的不變式）= 整套 Graça 誤差分析 = paper-blocked。
  本磚**只命名此缺口**（升為明寫假設 H1/H2）、**不消除它**（同專案方案 A 條件化紀律）。
- **`idealOrbit` 僅實數層 σ-迭代**：`idealOrbit n = σ^[n] x₀` 只是一個實數；本磚定理**從不** decode
  成 TM 組態、**從不**判定任何 halting/reachability。追蹤 `σ^[n](x₀)` ≠ 符號地算出它、更 ≠ 判定其
  性質。無 round、無 halting 謂詞、無化約。
- **undecidability 轉移仍 paper-blocked**（需另交：σ = 真 TM 一步的 Graça 光滑實現、`enc/dec` +
  ε-tube 不變式 `∀n, dec xₙ = configₙ`、reachability/halting 謂詞 + 從 TM 停機化約、時鐘自治化）。
- **γ3（全域 C^∞ 黏合成單一 ℝ→ℝ 軌道）延後**：其斷點值與 γ1 相同、數學內容零增量；非自治分段黏合
  可達（`smoothTransition` 兩端平坦 ⟹ 接縫 C^∞，用 M41 `windowedTargetingSol_hold_before/after`），
  但**自治流**（把窗列 `k=0,1,2,…` 編碼成相位狀態變數的 GPAC bump-train 振子、`ẋ=F(x)`）= mathlib
  從零、多月、**paper-blocked**（同 M42 檔頭）。本磚不交 γ3、不宣稱自治流。

**公理純度**：全走 elementary 實分析 + ℕ-歸納 + `geom_sum_succ`，零 ODE 存在性、零 MeasureTheory；
維持 `#print axioms = [propext, Classical.choice, Quot.sound]`。
-/

namespace FluidTuring

open Real Finset

/-! ## γ1：N 步斷點軌道（純遞迴、σ 抽象、零 paper-block、零誤差 claim） -/

/-- **N 步斷點軌道**（純遞迴、σ 抽象、零 paper-block）。
`xₙ₊₁ = σ(xₙ) + (xₙ - σ(xₙ))·e^{-C}` = Brick 4 `activeHalfStep` 窗後推進值的 ℕ-摺疊。
仿射/EMA 形 `= e^{-C}·xₙ + (1-e^{-C})·σ(xₙ)`：每步是舊值與讀目標的凸組合（因 `0 < e^{-C} < 1`）。 -/
noncomputable def leapfrogOrbit (σ : ℝ → ℝ) (x₀ C : ℝ) : ℕ → ℝ
  | 0     => x₀
  | n + 1 => σ (leapfrogOrbit σ x₀ C n)
              + (leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)) * Real.exp (-C)

theorem leapfrogOrbit_zero (σ : ℝ → ℝ) (x₀ C : ℝ) :
    leapfrogOrbit σ x₀ C 0 = x₀ := rfl

theorem leapfrogOrbit_succ (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) :
    leapfrogOrbit σ x₀ C (n + 1)
      = σ (leapfrogOrbit σ x₀ C n)
        + (leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)) * Real.exp (-C) := rfl

/-- **第 n 個 leapfrog 窗**：輸入 = 被讀凍結快照 = `xₙ`，窗位 `k = n`。目標 `σ xₙ` 為**常數**
（非追活尾——見檔頭）。純顯式、零 ODE 存在性、σ 抽象。 -/
noncomputable def leapfrogWindow (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) : ℝ → ℝ :=
  activeHalfStep σ (leapfrogOrbit σ x₀ C n) (leapfrogOrbit σ x₀ C n) C (n : ℝ)

/-- **carry-in**：`t ≤ n ⟹` 窗 n 凍於進位值 `xₙ`（M42 `activeHalfStep_frozen_before`）。 -/
theorem leapfrogWindow_carry_in (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) {t : ℝ} (h : t ≤ (n : ℝ)) :
    leapfrogWindow σ x₀ C n t = leapfrogOrbit σ x₀ C n :=
  activeHalfStep_frozen_before σ h

/-- **carry-out**：`n+1 ≤ t ⟹` 窗 n 達 `xₙ₊₁`（M42 `activeHalfStep_advance` + `leapfrogOrbit_succ`）。 -/
theorem leapfrogWindow_carry_out (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) {t : ℝ}
    (h : (n : ℝ) + 1 ≤ t) :
    leapfrogWindow σ x₀ C n t = leapfrogOrbit σ x₀ C (n + 1) := by
  rw [leapfrogWindow, activeHalfStep_advance σ h, leapfrogOrbit_succ]

/-- **窗內解真滿足 Brick-3 具體閘控 ODE**（常數目標 `σ xₙ`；M42 `activeHalfStep_hasDerivAt`）。 -/
theorem leapfrogWindow_hasDerivAt (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (leapfrogWindow σ x₀ C n)
      (-C * deriv Real.smoothTransition (t - (n : ℝ)) *
        (leapfrogWindow σ x₀ C n t - σ (leapfrogOrbit σ x₀ C n))) t :=
  activeHalfStep_hasDerivAt σ (leapfrogOrbit σ x₀ C n) (leapfrogOrbit σ x₀ C n) C (n : ℝ) t

/-- **★γ1 值層橋★ 接力交棒**：窗 n 在斷點 `n+1` 的值 = 窗 `(n+1)` 的（凍結）進位值 = `xₙ₊₁`。
N 個 Brick-3/4 ODE 窗首尾相接、斷點值恰走 `leapfrogOrbit`。此即「連續斷點值 = leapfrogOrbit n」
的值層版（不需 γ3 全域 C^∞ 黏合）。**誠實**：本引理**近乎定義性**（兩側皆由 `leapfrogOrbit` 定義經
`carry_out` / `carry_in` 直接 `= xₙ₊₁`）；真實質內容在 γ2 的 `error_accumulation` + `tracks_ideal`。 -/
theorem leapfrog_chain_handoff (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) :
    leapfrogWindow σ x₀ C n ((n : ℝ) + 1) = leapfrogWindow σ x₀ C (n + 1) ((n : ℝ) + 1) := by
  rw [leapfrogWindow_carry_out σ x₀ C n (le_refl _),
      leapfrogWindow_carry_in σ x₀ C (n + 1) (by push_cast; linarith)]

/-- **★γ1 綜合★ leapfrog 軌道實現**：carry-in ∧ carry-out ∧ gated-ODE ∧ 接力交棒 四合一。
N 個真解 ODE 的窗證成首尾相接的鏈，斷點軌跡恰 = 離散 `leapfrogOrbit`。 -/
theorem leapfrog_orbit_realized (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) :
    (∀ t, t ≤ (n : ℝ) → leapfrogWindow σ x₀ C n t = leapfrogOrbit σ x₀ C n) ∧
    (∀ t, (n : ℝ) + 1 ≤ t → leapfrogWindow σ x₀ C n t = leapfrogOrbit σ x₀ C (n + 1)) ∧
    (∀ t, HasDerivAt (leapfrogWindow σ x₀ C n)
        (-C * deriv Real.smoothTransition (t - (n : ℝ)) *
          (leapfrogWindow σ x₀ C n t - σ (leapfrogOrbit σ x₀ C n))) t) ∧
    leapfrogWindow σ x₀ C n ((n : ℝ) + 1) = leapfrogWindow σ x₀ C (n + 1) ((n : ℝ) + 1) :=
  ⟨fun _ ht => leapfrogWindow_carry_in σ x₀ C n ht,
   fun _ ht => leapfrogWindow_carry_out σ x₀ C n ht,
   fun t => leapfrogWindow_hasDerivAt σ x₀ C n t,
   leapfrog_chain_handoff σ x₀ C n⟩

/-! ## γ2：條件式誤差界（σ Lipschitz + 步長有界為**明寫假設**、非偷渡 undecidability） -/

/-- **理想 σ-迭代軌道**（欲模擬的離散動力）`zₙ = σ^[n] x₀`。純實數層物件、無 decode/round/halting。 -/
noncomputable def idealOrbit (σ : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ := fun n => σ^[n] x₀

theorem idealOrbit_zero (σ : ℝ → ℝ) (x₀ : ℝ) : idealOrbit σ x₀ 0 = x₀ := rfl

theorem idealOrbit_succ (σ : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    idealOrbit σ x₀ (n + 1) = σ (idealOrbit σ x₀ n) :=
  Function.iterate_succ_apply' σ n x₀

/-- **每步殘差 = Brick-3 收縮因子**：`|xₙ₊₁ - σ(xₙ)| = |xₙ - σ(xₙ)|·e^{-C}`。純代數 + `abs_mul`
+ `abs_of_pos (exp_pos)`。這是「單半步只 ε-近似 σ(xₙ)、殘差因子 `e^{-C}`」的精確量化。 -/
theorem leapfrogOrbit_residual (σ : ℝ → ℝ) (x₀ C : ℝ) (n : ℕ) :
    |leapfrogOrbit σ x₀ C (n + 1) - σ (leapfrogOrbit σ x₀ C n)|
      = |leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)| * Real.exp (-C) := by
  rw [leapfrogOrbit_succ]
  have h : σ (leapfrogOrbit σ x₀ C n)
        + (leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)) * Real.exp (-C)
        - σ (leapfrogOrbit σ x₀ C n)
      = (leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)) * Real.exp (-C) := by ring
  rw [h, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **★誤差累積（抽象數值引理）★**：`e 0 = 0` ∧ `e(n+1) ≤ L·e n + δ`（`0≤L, 0≤δ`）
⟹ `e n ≤ δ·∑_{i<n} Lⁱ`。純 ℕ-歸納 + `geom_sum_succ`。γ2 的承重骨架、與 σ 無關。 -/
theorem error_accumulation {e : ℕ → ℝ} {L δ : ℝ} (hL : 0 ≤ L) (_hδ : 0 ≤ δ)
    (he0 : e 0 = 0) (hrec : ∀ n, e (n + 1) ≤ L * e n + δ) :
    ∀ n, e n ≤ δ * ∑ i ∈ Finset.range n, L ^ i := by
  intro n
  induction n with
  | zero => simp [he0]
  | succ k ih =>
    calc e (k + 1)
        ≤ L * e k + δ := hrec k
      _ ≤ L * (δ * ∑ i ∈ Finset.range k, L ^ i) + δ := by
            have h := mul_le_mul_of_nonneg_left ih hL
            linarith
      _ = δ * ∑ i ∈ Finset.range (k + 1), L ^ i := by
            rw [geom_sum_succ]; ring

/-- **★HEADLINE（γ2、方案 A 條件化）★**：明寫 (H1) `σ` `L`-Lipschitz、(H2) 每步自缺口 `≤ M`，則
`|xₙ - σ^[n] x₀| ≤ M·e^{-C}·∑_{i<n} Lⁱ`。經 `abs_sub_le` 拆「殘差項 + Lipschitz 項」餵
`error_accumulation`。**誠實**：(H1) 對真 TM σ（不連續）**不可實例化**，真版需 ε-tube 穩健
（paper-blocked，見檔頭）；`idealOrbit` 只是實數、無 decode/halting。 -/
theorem leapfrogOrbit_tracks_ideal (σ : ℝ → ℝ) (x₀ C : ℝ) {L M : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hLip : ∀ x y, |σ x - σ y| ≤ L * |x - y|)
    (hgap : ∀ n, |leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)| ≤ M) :
    ∀ n, |leapfrogOrbit σ x₀ C n - idealOrbit σ x₀ n|
          ≤ (M * Real.exp (-C)) * ∑ i ∈ Finset.range n, L ^ i := by
  refine error_accumulation hL (mul_nonneg hM (Real.exp_pos _).le) ?_ ?_
  · show |leapfrogOrbit σ x₀ C 0 - idealOrbit σ x₀ 0| = 0
    rw [leapfrogOrbit_zero, idealOrbit_zero, sub_self, abs_zero]
  · intro n
    have hres : |leapfrogOrbit σ x₀ C (n + 1) - σ (leapfrogOrbit σ x₀ C n)|
                  ≤ M * Real.exp (-C) := by
      rw [leapfrogOrbit_residual]
      exact mul_le_mul_of_nonneg_right (hgap n) (Real.exp_pos _).le
    have hlip : |σ (leapfrogOrbit σ x₀ C n) - idealOrbit σ x₀ (n + 1)|
                  ≤ L * |leapfrogOrbit σ x₀ C n - idealOrbit σ x₀ n| := by
      rw [idealOrbit_succ]
      exact hLip _ _
    calc |leapfrogOrbit σ x₀ C (n + 1) - idealOrbit σ x₀ (n + 1)|
        ≤ |leapfrogOrbit σ x₀ C (n + 1) - σ (leapfrogOrbit σ x₀ C n)|
            + |σ (leapfrogOrbit σ x₀ C n) - idealOrbit σ x₀ (n + 1)| := abs_sub_le _ _ _
      _ ≤ L * |leapfrogOrbit σ x₀ C n - idealOrbit σ x₀ n| + M * Real.exp (-C) := by
            linarith [add_le_add hres hlip]

/-- **★γ2 非擴張推論★**：`L ≤ 1 ⟹ |x_N - σ^[N] x₀| ≤ N·M·e^{-C}`（線性累積）。
量化交換：欲以容差 `τ>0` 模擬 N 步（`M>0`），取 `C ≥ log(N·M/τ)` 即足——把單半步 ε-近似的殘差
`e^{-C}` 的隱憂化為顯式的模擬代價。`pow_le_one₀ + Finset.sum_le_sum`。 -/
theorem leapfrogOrbit_tracks_ideal_linear (σ : ℝ → ℝ) (x₀ C : ℝ) {L M : ℝ}
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hM : 0 ≤ M)
    (hLip : ∀ x y, |σ x - σ y| ≤ L * |x - y|)
    (hgap : ∀ n, |leapfrogOrbit σ x₀ C n - σ (leapfrogOrbit σ x₀ C n)| ≤ M) (N : ℕ) :
    |leapfrogOrbit σ x₀ C N - idealOrbit σ x₀ N| ≤ (N : ℝ) * (M * Real.exp (-C)) := by
  have hbound := leapfrogOrbit_tracks_ideal σ x₀ C hL0 hM hLip hgap N
  have hsum : ∑ i ∈ Finset.range N, L ^ i ≤ (N : ℝ) := by
    calc ∑ i ∈ Finset.range N, L ^ i
        ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => pow_le_one₀ hL0 hL1)
      _ = (N : ℝ) := by simp
  calc |leapfrogOrbit σ x₀ C N - idealOrbit σ x₀ N|
      ≤ (M * Real.exp (-C)) * ∑ i ∈ Finset.range N, L ^ i := hbound
    _ ≤ (M * Real.exp (-C)) * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hM (Real.exp_pos _).le)
    _ = (N : ℝ) * (M * Real.exp (-C)) := by ring

end FluidTuring
