import Mathlib
import FluidTuringLean.M53_CpuInClock
import FluidTuringLean.M45_SmoothReround

/-!
# Module 54 — Wall B 連續版：每步 re-rounding 清 `e^{−C}` 殘差 ⟹ 精確迭代流

**承 M53（自振盪 CPU 向量場、一個時鐘窗把玩具組態推進一步、但殘差 `e^{−C}`）+ M45（`sround`）+
M46（`sfloor` exact-on-plateau）**。M53 的誠實缺口 = **連續流是 ε-近似**（`cpuWindow_advances` 白紙黑字留
`e^{−C}` 殘差）。本磚**閉合這個缺口**：在每個時鐘邊緣把窗後值**重新量化（re-round）**回精確格點，使誤差
**對所有 N 不累積**——「時鐘 latch」把類比流重新數位化，正如真晶片的 flip-flop 於時鐘邊緣採樣。

## 兩條誠實路線（各有代價）

**路線 A（`sround`、real-analytic、有界不歸零）**：`sround`（M45，`sin` 基、GPAC 可生成、real-analytic）
把窗後值**收縮**向最近整數（`ρ=1−cos2πδ<1`），但**漸近、非字面到達**（`e^{−C}>0` 恆有殘差）。
- `cleanStep`（flow-window + `sround`）+ **`cleanStep_contract`**（一週期誤差 `× ρe^{−C}`、basin 條件是
  **窗後版** `e^{−C}|y−k|≤δ`）；
- **`cleanTrack_bounded`（★A HEADLINE★）**：**移動**整數目標軌道（大 `C` 容 `D≥1` 真跳幅、非退化常數），
  tube 半徑 `r` 自洽（`e^{−C}(r+D)≤δ`、`ρe^{−C}(r+D)≤r`）⟹ `∀ n, |y n − m n| ≤ r`
  （**誤差對所有 N 不累積**——sround 每步清殘差）。

**路線 B（`sfloor` 置中量化、C^∞、literal-exact）**：`sfloor`（M46）於 plateau **字面常值**，故置中量化
`snapExact` 對 plateau 半寬內任何殘差**字面** `= m`（非漸近、真 0 殘差）——代價 = C^∞ 非 analytic。
- `snapExact`（`sfloor` 平移 `w/2` 置中）+ **`snapExact_exact`**（`|y−m|≤w/2 ⟹ =m` 字面）；
- `exactStep`（flow-window + `snapExact`）+ **`exactStep_fix`**（殘差入 plateau 半寬 ⟹ `=m` 字面）；
- **`exactTrack_zero`（★B HEADLINE★）**：起點精確 + 有界跳幅 + `e^{−C}D ≤ w/2` ⟹ `∀ n, y n = m n`
  **字面相等**（誤差**恆等於 0**、對所有 N）= clocked/latched 數位流：ε-模擬流 + 時鐘邊置中量化 latch
  ⟹ **數位態序列字面精確**；
- **`cpuWindow_state_latched`（★接 M53★）**：真的把 M53 窗後**狀態暫存器**（q-分量）用 `snapExact` latch
  = 下個狀態 `q'` **字面**（殘差入半寬時）——「M53 一個時鐘窗 + 邊緣 latch = 精確推進狀態」。

## ★誠實範圍（禁 overclaim）★

- **是 clocked HYBRID、非純自治 ODE**：flow 窗（M53、連續 C^∞）+ 時鐘邊 latch（`snapExact`/`sround` 映射）。
  latch 是「連續→離散再數位化」的所在（正如真 flip-flop 的比較器 plateau/遲滯）。把 latch 本身嵌成**純**
  連續流段會撞「光滑流有限時間**無法**精確到達格點」牆（= 真電路**為何**要時鐘邊）。**迭代（數位態序列）
  字面精確；底層連續流仍 ε-近似。**
- **只清整數暫存器**（狀態 `q` + 讀出符號、`m n : ℕ`）：`sround`/`snapExact` 只量化**整數值**分量。
  帶編碼（分數、非整格）的 re-round 靠**讀**（`sfloor` plateau 解碼符號字面精確、另一機制）；全暫存器檔
  含尾巴放大 `Kⁱ` 的 tube 不變式 = 下游 G5 組裝。但**狀態暫存器正是承載「停機/哪條指令」位元的關鍵暫存器**
  （`cpuWindow_state_latched` 清的就是它）。
- **A（sround）有界不歸零、B（sfloor）字面歸零**：real-analytic 只能有界（漸近）、literal-exact 需 C^∞
  plateau。此 analytic↔exact 取捨是內稟（承 M45/M46）。
- **仍是玩具**：`sigmaRL`/`gEnc`/`gStepRL` module-local；真通用機 = G4e。**禁**宣稱線三 undecidability。
-/

namespace FluidTuring

open Real

/-! ## 路線 A：`sround` re-rounding（real-analytic、有界追蹤） -/

/-- **一個「清洗週期」（sround 版）**：flow-window 把 `y` 拉向整數 `m`（殘差 `e^{−C}`，見 M53
`cpuWindowSol_end`）後施 `sround` 收縮回最近整數。 -/
noncomputable def cleanStep (m y C : ℝ) : ℝ := sround (m + (y - m) * Real.exp (-C))

/-- **★A 單步收縮★**：`sround` basin 只需**窗後**距離入界（`e^{−C}·|y−k| ≤ δ ≤ 1/4`）——故大 `C`
可容納**大跳幅**的 `y`（窗把它先收縮進 basin），這是路線 A 能追**移動**整數目標的關鍵。
⟹ 一個清洗週期把誤差 `× ρe^{−C}`（`ρ=1−cos2πδ`）：`|cleanStep k y C − k| ≤ ρ·e^{−C}·|y−k|`。 -/
theorem cleanStep_contract (k : ℤ) {δ C : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    {y : ℝ} (hy : Real.exp (-C) * |y - (k : ℝ)| ≤ δ) :
    |cleanStep (k : ℝ) y C - (k : ℝ)|
      ≤ (1 - Real.cos (2 * π * δ)) * Real.exp (-C) * |y - (k : ℝ)| := by
  have he0 : (0 : ℝ) ≤ Real.exp (-C) := (Real.exp_pos _).le
  set yf : ℝ := (k : ℝ) + (y - (k : ℝ)) * Real.exp (-C) with hyfdef
  have hyfk : yf - (k : ℝ) = (y - (k : ℝ)) * Real.exp (-C) := by rw [hyfdef]; ring
  have hyfabs : |yf - (k : ℝ)| = Real.exp (-C) * |y - (k : ℝ)| := by
    rw [hyfk, abs_mul, abs_of_nonneg he0, mul_comm]
  have hbasin : |yf - (k : ℝ)| ≤ δ := by rw [hyfabs]; exact hy
  have hc := sround_contract k hδ0 hδ hbasin
  have hcs : cleanStep (k : ℝ) y C = sround yf := by rw [cleanStep, hyfdef]
  rw [hcs]
  calc |sround yf - (k : ℝ)|
      ≤ (1 - Real.cos (2 * π * δ)) * |yf - (k : ℝ)| := hc
    _ = (1 - Real.cos (2 * π * δ)) * (Real.exp (-C) * |y - (k : ℝ)|) := by rw [hyfabs]
    _ = (1 - Real.cos (2 * π * δ)) * Real.exp (-C) * |y - (k : ℝ)| := by ring

/-- **★A HEADLINE：sround 有界追蹤（Wall B 連續版、誤差不累積、可追移動目標）★**：整數目標軌道
`m:ℕ→ℤ`、清洗軌道 `y:ℕ→ℝ`（每步 = flow-window 拉向 `m(n+1)` 後 `sround`）；tube 半徑 `r` 自洽
（跳幅界 `D`、**窗後入 basin** `e^{−C}(r+D)≤δ`、`ρe^{−C}(r+D)≤r`）+ 起點入管 ⟹ **`∀ n, |y n − m n| ≤ r`**
（誤差對所有 N 有界、不累積——`sround` 每步清 `e^{−C}` 殘差）。**basin 條件是窗後版**（`e^{−C}(r+D)≤δ`
非 `r+D≤δ`）故大 `C` 允許 **`D≥1` 的真移動整數目標**（跳幅 ≥1、被窗先收縮進 basin），非退化常數。 -/
theorem cleanTrack_bounded {y : ℕ → ℝ} {m : ℕ → ℤ} {r D δ C : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hD : ∀ n, |(m n : ℝ) - (m (n + 1) : ℝ)| ≤ D)
    (hcons1 : Real.exp (-C) * (r + D) ≤ δ)
    (hcons2 : (1 - Real.cos (2 * π * δ)) * Real.exp (-C) * (r + D) ≤ r)
    (hy0 : |y 0 - (m 0 : ℝ)| ≤ r)
    (hrec : ∀ n, y (n + 1) = cleanStep (m (n + 1) : ℝ) (y n) C) :
    ∀ n, |y n - (m n : ℝ)| ≤ r := by
  have hρ0 : (0 : ℝ) ≤ 1 - Real.cos (2 * π * δ) := by linarith [Real.cos_le_one (2 * π * δ)]
  have hρe0 : (0 : ℝ) ≤ (1 - Real.cos (2 * π * δ)) * Real.exp (-C) :=
    mul_nonneg hρ0 (Real.exp_pos _).le
  intro n
  induction n with
  | zero => exact hy0
  | succ p ih =>
    have hstep : |y p - (m (p + 1) : ℝ)| ≤ r + D :=
      calc |y p - (m (p + 1) : ℝ)|
          ≤ |y p - (m p : ℝ)| + |(m p : ℝ) - (m (p + 1) : ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ r + D := add_le_add ih (hD p)
    have hstep_basin : Real.exp (-C) * |y p - (m (p + 1) : ℝ)| ≤ δ :=
      calc Real.exp (-C) * |y p - (m (p + 1) : ℝ)|
          ≤ Real.exp (-C) * (r + D) := mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
        _ ≤ δ := hcons1
    have hcontr := cleanStep_contract (m (p + 1)) hδ0 hδ hstep_basin
    rw [hrec p]
    calc |cleanStep (m (p + 1) : ℝ) (y p) C - (m (p + 1) : ℝ)|
        ≤ (1 - Real.cos (2 * π * δ)) * Real.exp (-C) * |y p - (m (p + 1) : ℝ)| := hcontr
      _ ≤ (1 - Real.cos (2 * π * δ)) * Real.exp (-C) * (r + D) :=
          mul_le_mul_of_nonneg_left hstep hρe0
      _ ≤ r := hcons2

/-! ## 路線 B：`sfloor` 置中量化 re-rounding（C^∞、literal-exact） -/

/-- **置中精確 latch（C^∞）**：`snapExact K w y := sfloor K w (y + w/2)`。`sfloor` 右 plateau `[m,m+w]`
平移 `w/2` 置中 ⟹ 整數 `m` 的**對稱** plateau `[m−w/2, m+w/2]` 上**字面** `= m`。 -/
noncomputable def snapExact (K : ℕ) (w y : ℝ) : ℝ := sfloor K w (y + w / 2)

/-- 置中 latch C^∞（`sfloor` ∘ 仿射）。 -/
theorem snapExact_contDiff (K : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (snapExact K w) :=
  (sfloor_contDiff K w).comp (contDiff_id.add contDiff_const)

/-- **★literal-exact latch★**：`|y−m| ≤ w/2`（`m<K`、`0<w<1`）⟹ `snapExact K w y = m` **字面相等**
（非 ε、非漸近——plateau 常值）。 -/
theorem snapExact_exact (K : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (m : ℕ) (hm : m < K)
    {y : ℝ} (hy : |y - (m : ℝ)| ≤ w / 2) :
    snapExact K w y = (m : ℝ) := by
  rw [snapExact]
  rw [abs_le] at hy
  exact sfloor_exact_on_plateau K hw0 hw1 m hm (by linarith [hy.1]) (by linarith [hy.2])

/-- **一個「精確清洗週期」（sfloor 版）**：flow-window 拉向整數 `m`（殘差 `e^{−C}`）後置中量化。 -/
noncomputable def exactStep (K : ℕ) (w m y C : ℝ) : ℝ :=
  snapExact K w (m + (y - m) * Real.exp (-C))

/-- **★B literal-exact 單步★**：殘差入 plateau 半寬（`e^{−C}·|y−m| ≤ w/2`、`m<K`）⟹ `exactStep = m`
**字面相等**（clock-edge latch 把 ε-流重新精確數位化、真 0 殘差）。 -/
theorem exactStep_fix (K : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (m : ℕ) (hm : m < K)
    {y C : ℝ} (hres : Real.exp (-C) * |y - (m : ℝ)| ≤ w / 2) :
    exactStep K w (m : ℝ) y C = (m : ℝ) := by
  rw [exactStep]
  apply snapExact_exact K hw0 hw1 m hm
  have hz : ((m : ℝ) + (y - (m : ℝ)) * Real.exp (-C)) - (m : ℝ)
      = (y - (m : ℝ)) * Real.exp (-C) := by ring
  rw [hz, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm]
  exact hres

/-- **★B HEADLINE：literal-exact 迭代流（Wall B 連續版、誤差恆等於 0）★**：整數目標軌道 `m:ℕ→ℕ`
（各 `<K`）、精確清洗軌道 `y:ℕ→ℝ`（每步 = flow-window 拉向 `m(n+1)` 後 `snapExact`）；起點精確
`y 0 = m 0`、有界跳幅 `D`、`e^{−C}·D ≤ w/2`（大 `C` 即得）⟹ **`∀ n, y n = m n`** 字面相等
（誤差**恆等於 0**、對所有 N）= clocked/latched 數位流：ε-模擬流 + 時鐘邊置中量化 latch ⟹ **數位態序列字面精確**。 -/
theorem exactTrack_zero (K : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    {y : ℕ → ℝ} {m : ℕ → ℕ} {C D : ℝ}
    (hmK : ∀ n, m n < K)
    (hD : ∀ n, |(m n : ℝ) - (m (n + 1) : ℝ)| ≤ D)
    (hCw : Real.exp (-C) * D ≤ w / 2)
    (hy0 : y 0 = (m 0 : ℝ))
    (hrec : ∀ n, y (n + 1) = exactStep K w (m (n + 1) : ℝ) (y n) C) :
    ∀ n, y n = (m n : ℝ) := by
  intro n
  induction n with
  | zero => exact hy0
  | succ p ih =>
    rw [hrec p]
    apply exactStep_fix K hw0 hw1 (m (p + 1)) (hmK (p + 1))
    rw [ih]
    calc Real.exp (-C) * |(m p : ℝ) - (m (p + 1) : ℝ)|
        ≤ Real.exp (-C) * D := mul_le_mul_of_nonneg_left (hD p) (Real.exp_pos _).le
      _ ≤ w / 2 := hCw

/-! ## 接 M53：真的把自振盪 CPU 流的狀態暫存器 latch 成精確下個狀態 -/

/-- **★接 M53：時鐘窗 + 邊緣 latch = 精確推進狀態★**：`σstep := sigmaRL`、`r₂ := gEnc c`（良編碼）、
下個狀態 `q' = (gStepRL c).q < K`、窗後狀態暫存器殘差入 plateau 半寬 ⟹ 對 M53 窗後**狀態分量**
（`(cpuWindowSol … 1).1.1`）施 `snapExact` = `q'` **字面相等**——把 M53 的 `e^{−C}` 殘差在時鐘邊清成
精確下個狀態（承 `cpuWindow_advances`）。 -/
theorem cpuWindow_state_latched (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (r1₀ : Cfg3) (C : ℝ) (n : ℤ)
    (q l₀ s : ℕ) (L' R' : List ℕ) (hwf : wfCfg Q k ⟨q, l₀ :: L', s :: R'⟩)
    (hqK : (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩).q < K)
    (hres : Real.exp (-C)
        * |r1₀.1 - ((gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩).q : ℝ)| ≤ w / 2) :
    snapExact K w ((cpuWindowSol r1₀ (gEnc K ⟨q, l₀ :: L', s :: R'⟩)
          (sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
            (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w) C n 1).1.1)
      = ((gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩).q : ℝ) := by
  have hadv := cpuWindow_advances δqN δwN moveB Q k K hk hkK hK hw0 hw1 hwhead
    r1₀ C n q l₀ s L' R' hwf
  -- 取窗後 `.1` 三元組的第一分量（= 狀態暫存器）；`(gEnc K c').1` 定義即 `↑c'.q`，
  -- 故其恰是 `exactStep K w q' r1₀.1 C`，由 `exactStep_fix` latch 成 `q'`（`exact` 走 defeq）。
  rw [hadv]
  exact exactStep_fix K hw0 hw1 _ hqK hres

end FluidTuring
