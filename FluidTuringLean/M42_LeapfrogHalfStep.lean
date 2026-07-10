import Mathlib.Analysis.Calculus.Deriv.Prod
import FluidTuringLean.M41_ConcreteWindow

/-!
# Module 42 — Analog-computation 流：Brick 4（leapfrog 半步化約 + 兩暫存器解耦讀寫）

**方向三 Brick 4**（承接 M41 Brick 3 具體窗 + 兩側精確 HOLD）。Branicky/Graça leapfrog 時鐘的
**排程原子**：兩暫存器 `(active, passive)` **輪流**更新——一個在自己的窗內被 gated steer 到
`σ(另一暫存器的凍結值)`，另一個在該窗內被 HOLD 成常數（carry），下一窗角色互換。本磚把「一個
讀寫、另一個閂鎖」的**兩暫存器構造/資料流**精確化成機器證，並交付 leapfrog **分段耦合場**（**寫法上**
兩座標耦合 `σ(passive)/σ(active)`；**動態上**每窗恰**一分量 live**、讀另一分量的**凍結值**——write-protect
使交叉項在 active 窗乘 0，故**非**同時 live 雙向耦合，此即 leapfrog 讀寫解耦本意）（顯式 pair 對解、
**零 Picard–Lindelöf**）。

## ★方案裁決：α（半步化約），存在性-free★

三方研究一致推薦 **α**（半步化約），非 β（全自治）。關鍵洞見：
- **互補窗 HOLD 讓存在性變得不必要**：`passive` 暫存器排在**下一窗** `k+1`，故在 `active` 窗
  `[k,k+1]` 上它被 M41 兩側 HOLD **凍成常數** `p₀`（值層 `windowedTargetingSol_frozen_before`、
  導數層 `windowedTargetingSol_hold_before`）。於是 `active` 讀取的目標 `σ(passive t) = σ p₀` 是
  **常數**，`active` 分量**恰好**是 Brick 3 的純量閘控 ODE（常數目標），有顯式閉式解，逐點驗
  `HasDerivAt` 即可。**全程零抽象 ODE 存在性**（延續 M35/M39/M40/M41「只寫顯式解 + HasDerivAt」
  紀律）。
- **σ 全程抽象且無需正則性**（最漂亮的誠實點）：解耦只在**單一凍結值** `p₀` 對 `σ` 求值，故
  `σ(passive t) = σ p₀` 對**任意**（甚至不連續）`σ` 成立。這反過來**精確劃出**本磚不碰的邊界——
  模擬正確性（`σ` 把 ε-鄰域映進 ε-鄰域、round）恰是唯一未觸及、且需 σ 具體化的部分。α 因此
  **結構上不可能**偷渡模擬 claim。

## 本磚交付（四個承重件，非 thin）

1. **解耦本體**（`passiveReg_frozen_on_active` 值層 + `passiveReg_holds` 導數層）：被動暫存器在
   主動窗內被 HOLD 成常數 ⟹ 被讀取目標 `σ(passive)` 恆常、乾淨常數來源。
2. **★HEADLINE 化約★**（`leapfrog_halfstep_reduction`）：主動暫存器讀取**真實**被動暫存器
   `passiveReg`（非裸常數）作目標，在主動窗上耦合 read **恰化約**為 Brick-3 定常目標 steer。
3. **★HEADLINE leapfrog 分段耦合場★**（`leapfrog_halfstep_pair_hasDerivAt`）：pair `(active, passive)`
   滿足 leapfrog **分段耦合向量場**（寫法上耦合）
   `(-Cφ₁·(active - σ(passive)), -Cφ₂·(passive - σ(active)))`，被 `HasDerivAt.prodMk` **顯式對解**。
   **★誠實：動態上此場在證明窗 `t<k+1` 退化成解耦乘積★**——第二分量的具體閘
   `φ₂ = deriv smoothTransition(t-(k+1))` 在主動窗上**被證恰 = 0**（`deriv_smoothTransition_zero_before`，
   經 `HasDerivAt.unique` 由 M41 HOLD 導出），故 `σ(active)` 交叉項**乘 0 湮滅**（不承重）、`passive` inert；
   第一分量讀的 `passive` 被凍成 `p₀`、故目標 = **常數** `σ p₀`。所以**無同時 live 雙向耦合被行使**——
   這正是 leapfrog 讀寫解耦本意（每窗恰一分量 live），**非**「造出真雙向耦合流」。**零 Picard–Lindelöf。**
4. **★HEADLINE leapfrog 步 data-flow★**（`leapfrog_step`）：`reg1` 在窗 `k` 讀 `σ(reg2 的凍結輸入)`、
   `reg2` 在窗 `k+1` 讀 `σ(reg1 的推進值)`；兩半步**角色互換**、**來源永遠是被 HOLD 的常數**。本定理
   機器證的是**兩暫存器構造/資料流**（角色互換、來源恆常）。**單暫存器不足**（`y'=-Cφ(y-σ(y))` 目標
   隨 `y` 移動、無 Brick-3 常數解、追移動不動點收斂到 `σ` 的 fixed point ≠ 推進一步 `σ`）= **motivating
   prose、未形式化**（檔內**無**單暫存器 no-go 定理）。

**相對 Brick 3 的實質增量（誠實）**：約 6 條引理（`activeHalfStep_hasDerivAt/_frozen_before/_advance/`
`_eps`、`passiveReg_frozen_before/_holds`）是 M41 的**字面單行實例化**（`b→σ p`、`bp` 更名）。真新增 =
`deriv_smoothTransition_zero_before`（HOLD→`deriv=0` 經 `HasDerivAt.unique`）、`HasDerivAt.prodMk` 2D 打包、
`passiveReg_frozen_on_active` frozen-read 化約、`leapfrog_step` data-flow 打包——為真但薄；headline 勿讀成大於內容。

## ★誠實範圍（Brick 4 之上仍 paper-blocked，明寫，禁 overclaim）★

- **非自治（外源時鐘）**：各暫存器**各自**滿足其向（被 HOLD 的）另一暫存器值的 gated steer，
  場透過 `φ(t)` 窗閘與被 HOLD 的另一值進入——**非**聯合自治向量場 `ẋ=F(x)`。本磚**不**宣稱造出
  自治流。真自治需 (a) **σ 具體化**（σ = TM 一步 map on encoded reals、round/decode 本質不連續、
  需整套 Graça 誤差分析）與 (b) **時鐘自治化**（把窗列變成相位變數的光滑週期 bump-train
  state-function）= GPAC 核心、多月、mathlib 從零。**β 的 block 在此二者，不是（局部）ODE 存在性**
  （**局部**存在性可用互補窗 HOLD + 閉式解避開）——但真自治 GPAC 流仍需**全域**存在 + 無爆破 +
  Graça 誤差 bookkeeping，纏在 blocker (a) 內；mathlib 現貨 Picard–Lindelöf 只給 bounded `Icc` 上**局部**解。
- **模擬未觸及**：`σ` 保持抽象且只在凍結值取值，故「σ 把 ε-鄰域映進 ε-鄰域」的模擬正確性完全
  未觸及。α = leapfrog 排程 + 兩暫存器解耦讀寫的**動力學/定理層核心**，與「目標是否真 =
  σ(編碼舊態)」無關（同 M41 對 σ 的免責）。
- **有限收縮，非精確收斂**：單一 `smoothTransition` 窗在 `1` **飽和**（不 `→∞`），每半步只收縮到
  `σ(w)` 的 **ε-鄰域**（因子 `e^{-C}`），**非**精確 `y→σ(w)`。**切勿**對半步套 M40
  `targetingGatedSol_tendsto`（要 `Φ→∞`）。精確推進需**無限窗階梯 + per-step 誤差 bookkeeping**
  （γ / Brick 5，重回 paper-block）。
- **N 步組合、round/decode、σ 落地、undecidability 轉移**：全部維持 paper-blocked，本磚明寫不碰。
-/

namespace FluidTuring

open Real Filter Topology

/-! ## 具體閘在窗外恰 0（write-protect 的機械見證） -/

/-- **窗前具體閘恰 0**：`t < k ⟹ deriv smoothTransition (t-k) = 0`。由 M41 兩見證經導數唯一性得：
`windowΦ_hasDerivAt` 給導數 `= deriv smoothTransition (t-k)`、`windowΦ_hold_before` 給導數 `= 0`，
`HasDerivAt.unique` 逼相等。這把「被動暫存器在自己 off-窗 inert」從抽象假設升為機械事實。 -/
theorem deriv_smoothTransition_zero_before {k t : ℝ} (h : t < k) :
    deriv Real.smoothTransition (t - k) = 0 :=
  (windowΦ_hasDerivAt k t).unique (windowΦ_hold_before h)

/-! ## 兩暫存器：active（本窗更新）與 passive（排下一窗、本窗被 HOLD） -/

/-- **主動暫存器**（窗 `k`）= Brick 3 解以常數目標 `b := σ p` 實例化（`p` = 被動被讀取的凍結值）。
純顯式、零 ODE 存在性。`σ` 抽象、無連續假設——`σ p` 只是一個實數，直接代入 M41 的 `b`。 -/
noncomputable def activeHalfStep (σ : ℝ → ℝ) (a₀ p C k : ℝ) : ℝ → ℝ :=
  windowedTargetingSol a₀ (σ p) C k

/-- **被動暫存器** = 排在**下一窗** `k+1` 的 `windowedTargetingSol`；故在主動窗 `[k,k+1]` 上被 M41
兩側 HOLD 凍成輸入常數 `p₀`（乾淨常數來源、carry）。 -/
noncomputable def passiveReg (p₀ bp C k : ℝ) : ℝ → ℝ :=
  windowedTargetingSol p₀ bp C (k + 1)

/-! ## 主動暫存器：Brick 3 直接實例化（目標 σ p 透明代入 b） -/

/-- **主動 gated steer**：滿足向 `σ p` 的具體閘控 ODE（= M41 `_hasDerivAt` 代 `b := σ p`）。 -/
theorem activeHalfStep_hasDerivAt (σ : ℝ → ℝ) (a₀ p C k t : ℝ) :
    HasDerivAt (activeHalfStep σ a₀ p C k)
      (-C * deriv Real.smoothTransition (t - k) * (activeHalfStep σ a₀ p C k t - σ p)) t :=
  windowedTargetingSol_hasDerivAt a₀ (σ p) C k t

/-- **窗前凍結**：`t ≤ k ⟹` 主動暫存器恰 `= a₀`（輸入）。 -/
theorem activeHalfStep_frozen_before (σ : ℝ → ℝ) {a₀ p C k t : ℝ} (h : t ≤ k) :
    activeHalfStep σ a₀ p C k t = a₀ :=
  windowedTargetingSol_frozen_before h

/-- **WRITE / 推進值**：`k+1 ≤ t ⟹` 主動暫存器 `= σ p + (a₀-σ p)·e^{-C}`（讀 `σ(舊)`、走一因子
`e^{-C}`）。誠實：這是 ε-近似 σ p（因子 `e^{-C}`），非精確 `= σ p`（見檔頭）。 -/
theorem activeHalfStep_advance (σ : ℝ → ℝ) {a₀ p C k t : ℝ} (h : k + 1 ≤ t) :
    activeHalfStep σ a₀ p C k t = σ p + (a₀ - σ p) * Real.exp (-C) :=
  windowedTargetingSol_frozen_after h

/-- **ε-WRITE 正確性**：`∀ ε>0 ∃ C>0`，窗後主動落 `σ p` 的 ε 內（誠實 ε-近似、靠拉大 `C`）。 -/
theorem activeHalfStep_eps (σ : ℝ → ℝ) (a₀ p k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 < C ∧ ∀ t, k + 1 ≤ t → |activeHalfStep σ a₀ p C k t - σ p| ≤ ε :=
  windowedTargetingSol_eps_target a₀ (σ p) k hε

/-! ## 被動暫存器：本窗被 HOLD（解耦本體） -/

/-- **被動窗前凍結（值）**：`t ≤ k+1 ⟹` 被動暫存器恰 `= p₀`（排在窗 `k+1`、故整個主動窗前凍結）。 -/
theorem passiveReg_frozen_before {p₀ bp C k t : ℝ} (h : t ≤ k + 1) :
    passiveReg p₀ bp C k t = p₀ :=
  windowedTargetingSol_frozen_before h

/-- **被動 HOLD（導數層）**：`t < k+1 ⟹ HasDerivAt (passiveReg ..) 0 t`（值永不漂移、合格 latch）。 -/
theorem passiveReg_holds {p₀ bp C k t : ℝ} (h : t < k + 1) :
    HasDerivAt (passiveReg p₀ bp C k) 0 t :=
  windowedTargetingSol_hold_before h

/-- **★解耦核心（值層）★**：主動窗上 `t ≤ k+1`，被讀取目標 `σ(passive t) = σ p₀` 恆常；與 `σ` 是否
連續**無關**（只在單一凍結值 `p₀` 取值）。這正是「耦合 read 良定義且 = 定常目標」的本體。 -/
theorem passiveReg_frozen_on_active (σ : ℝ → ℝ) {p₀ bp C k t : ℝ} (h : t ≤ k + 1) :
    σ (passiveReg p₀ bp C k t) = σ p₀ := by
  rw [passiveReg_frozen_before h]

/-! ## ★HEADLINE 化約：耦合 read → Brick-3 定常 steer★ -/

/-- **★HEADLINE 化約★**：主動暫存器讀取**真實**被動暫存器 `passiveReg`（非裸常數 `b`）作目標，在
主動窗 `t ≤ k+1` 上耦合系統**恰化約**為 Brick-3 定常目標 steer。這是「兩暫存器解耦讀寫」的定理層
核心（缺此件則退化為 Brick 3 改名）。證：先把 `σ(passive t)` rewrite 成 `σ p₀`（解耦核心），再套
主動 gated steer。 -/
theorem leapfrog_halfstep_reduction (σ : ℝ → ℝ) (a₀ p₀ bp C k t : ℝ) (h : t ≤ k + 1) :
    HasDerivAt (activeHalfStep σ a₀ p₀ C k)
      (-C * deriv Real.smoothTransition (t - k) *
        (activeHalfStep σ a₀ p₀ C k t - σ (passiveReg p₀ bp C k t))) t := by
  rw [passiveReg_frozen_on_active σ h]
  exact activeHalfStep_hasDerivAt σ a₀ p₀ C k t

/-! ## ★HEADLINE 真 2D 耦合向量場（顯式對解、零 Picard–Lindelöf）★ -/

/-- **★HEADLINE leapfrog 分段耦合場★**：pair `(active, passive)` 滿足 leapfrog 分段耦合向量場——第一
分量 steer 向 `σ(passive)`、第二分量 steer 向 `σ(active)`——被 `HasDerivAt.prodMk` **顯式對解**。
**★誠實：這是「寫法耦合、動態解耦」，非同時 live 雙向耦合★**。在證明窗 `t < k+1` 上：(i) `passive`
被凍成 `p₀`，故第一分量目標 `σ(passive t) = σ p₀` 退化為**常數**（`leapfrog_halfstep_reduction`；主動只讀
凍結值、不追 live 軌道）；(ii) 第二分量的具體閘 `deriv smoothTransition(t-(k+1))` **被證恰 = 0**
（`deriv_smoothTransition_zero_before`），故 `σ(active)` 交叉項**乘 0 湮滅、不承重**、`passive` inert
（`passiveReg_holds`）。即此窗 pair 動力學 = **解耦乘積**（Brick-3 定常 ODE × held 常數）；耦合只在**場的
寫法**、非動態行使——**這正是 leapfrog 讀寫解耦**（每窗恰一分量 live）。**全程零 Picard–Lindelöf。**
`#print axioms = [propext, Classical.choice, Quot.sound]`。 -/
theorem leapfrog_halfstep_pair_hasDerivAt (σ : ℝ → ℝ) (a₀ p₀ bp C k t : ℝ) (h : t < k + 1) :
    HasDerivAt (fun s => (activeHalfStep σ a₀ p₀ C k s, passiveReg p₀ bp C k s))
      (-C * deriv Real.smoothTransition (t - k) *
          (activeHalfStep σ a₀ p₀ C k t - σ (passiveReg p₀ bp C k t)),
       -C * deriv Real.smoothTransition (t - (k + 1)) *
          (passiveReg p₀ bp C k t - σ (activeHalfStep σ a₀ p₀ C k t))) t := by
  have hc2 : HasDerivAt (passiveReg p₀ bp C k)
      (-C * deriv Real.smoothTransition (t - (k + 1)) *
        (passiveReg p₀ bp C k t - σ (activeHalfStep σ a₀ p₀ C k t))) t := by
    rw [deriv_smoothTransition_zero_before h]
    simpa using passiveReg_holds h
  exact (leapfrog_halfstep_reduction σ a₀ p₀ bp C k t (le_of_lt h)).prodMk hc2

/-! ## ★HEADLINE 完整 leapfrog 步（角色互換、來源恆常）★ -/

/-- **★HEADLINE 完整 leapfrog 步★**：`reg1 = activeHalfStep σ r1₀ r2₀ C k`（窗 `k`、讀 `σ(r2₀)`）；
`reg2 = activeHalfStep σ r2₀ r1' C (k+1)`（窗 `k+1`、讀 `σ(r1')`），`r1'` = reg1 推進值。斷言三段
（角色互換、來源永遠是被 HOLD 的常數）：
① `∀ t ≤ k+1`：reg1 向 `σ r2₀` gated steer（讀被凍的 reg2 輸入）∧ reg2 `= r2₀`（此窗被 HOLD carry）；
② `∀ k+1 ≤ t`：reg1 `= r1'`（推進完成）；
③ `∀ t`：（`k+1 < t →` reg1 HOLD 導數 0）∧ reg2 向 `σ r1'` gated steer（下一窗讀 reg1 推進值）。
本定理機器證的是**兩暫存器構造/資料流**（角色互換、來源恆常打破讀寫環）。**「單暫存器不足」= motivating
prose、未形式化**（檔內**無**單暫存器 `y'=-Cφ(y-σ(y))` no-go 定理）。`r1'` 以顯式參數 + 定義等式傳入
（避免 let-binding 讓 `HasDerivAt` 目標卡在 let-展開，見 risks）。 -/
theorem leapfrog_step (σ : ℝ → ℝ) (r1₀ r2₀ C k : ℝ)
    (r1' : ℝ) (hr1' : r1' = σ r2₀ + (r1₀ - σ r2₀) * Real.exp (-C)) :
    (∀ t, t ≤ k + 1 →
      HasDerivAt (activeHalfStep σ r1₀ r2₀ C k)
        (-C * deriv Real.smoothTransition (t - k) *
          (activeHalfStep σ r1₀ r2₀ C k t - σ r2₀)) t ∧
      activeHalfStep σ r2₀ r1' C (k + 1) t = r2₀) ∧
    (∀ t, k + 1 ≤ t → activeHalfStep σ r1₀ r2₀ C k t = r1') ∧
    (∀ t, (k + 1 < t → HasDerivAt (activeHalfStep σ r1₀ r2₀ C k) 0 t) ∧
      HasDerivAt (activeHalfStep σ r2₀ r1' C (k + 1))
        (-C * deriv Real.smoothTransition (t - (k + 1)) *
          (activeHalfStep σ r2₀ r1' C (k + 1) t - σ r1')) t) := by
  refine ⟨fun t ht => ⟨activeHalfStep_hasDerivAt σ r1₀ r2₀ C k t, ?_⟩,
          fun t ht => ?_, fun t => ⟨fun ht => ?_, activeHalfStep_hasDerivAt σ r2₀ r1' C (k + 1) t⟩⟩
  · exact activeHalfStep_frozen_before σ ht
  · rw [activeHalfStep_advance σ ht, hr1']
  · exact windowedTargetingSol_hold_after ht

end FluidTuring
