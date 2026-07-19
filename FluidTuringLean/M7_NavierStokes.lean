import FluidTuringLean.M6_EulerTuring

/-!
# Module 7 — Navier–Stokes 定常解層（Proposition 4.1，方案 A 抽象簽名版）

依源頭論文 **Dyhr–González-Prieto–Miranda–Peralta-Salas 2025/2026**
（arXiv:2507.07696；PNAS Nexus 5(5), pgag131）《Turing complete Navier–Stokes
steady states via cosymplectic geometry》**Proposition 4.1**。

**Prop 4.1**：黎曼 3-流形 `(M, g)` 上，調和向量場 `X`（對偶 1-形式 `α = X♭` 滿足
`dα = 0 ∧ d*α = 0`）是不可壓縮 Navier–Stokes 方程的**定常解**，對**任意 `ν ≥ 0`** 成立，
取適當壓力 `p`。

**證明骨架（論文，非自創）**：
1. `dα = d*α = 0` ⟹ Hodge Laplacian `Δ_H α = (dd* + d*d) α = 0` ⟹ `ΔX = 0`。
2. `d*α = 0` ⟹ `div X = 0`（不可壓縮）。
3. 定常 NS：`∇_X X − ν ΔX = −∇p`；因 `ΔX = 0`，**黏滯項對任意 `ν` 直接消失** ⟹ `∇_X X = −∇p`。
4. `dα = 0` ⟹ `∇_X X = ∇(½|X|²)`（Cartan/閉形式恆等式），取 `p = −½|X|² + c`。

**前提 A（釘死，先前出錯根源）**：黏滯項的 `Δ` 是 **Hodge Laplacian `(dd* + d*d)`**，
不是 Bochner/連接拉普拉斯 `∇*∇`。Hodge-調和 ⟹ `ΔX = 0`；若換 Bochner，Weitzenböck
`Δ_H = ∇*∇ + Ric` 會帶出 `Ric` 項、命題就要 Ricci-flat。此**運算元選擇**是「黏滯免疫」
的全部關鍵——M6 前身 docstring 正是誤用 Bochner（並混淆動量黏滯項 `νΔX` 與耗散率
`ν∫|∇u|²`）而判它為假，本模組依源頭論文更正（**這是基於新證據的修正、非壓力反轉**）。

**前提 B（釘死）**：Hodge-admissibility 為**明寫前提**——`M` 容許處處非零的調和向量場
（Tischler：`M` 須纖維化到 `S¹`；比 `H¹ ≠ 0` 強：幾何＋分析條件）。**不對任意流形宣稱免疫**。

**誠實範圍（硬規則 2/3/4）**：mathlib 無微分幾何（Hodge Laplacian / codifferential /
調和形式 / Cartan 恆等式），故本層是**抽象簽名**（同 M5 `VectorCalculus3`）：算子是符號，
骨架步驟 1（Hodge 分解）與步驟 4（Cartan 恆等式）以**簽名法則**承載。`prop_4_1` 機器
證的是**推導結構**——「黏滯項 `νΔX` 為何對任意 `ν` 消失」的邏輯，對所有滿足簽名的詮釋
成立。**抽象層空洞**（下方 `trivialNS` 機器背書：退化詮釋 trivially 滿足）——真物理內容
（Hodge Laplacian 的真定義、Cartan 恆等式）需真微分幾何、mathlib 無、**paper-blocked**。
不冒充證了真流體 NS。同 M5/M6 方案 A 誠實條件化手法。
-/

namespace FluidTuring

/-- **Navier–Stokes 抽象簽名**（擴 `VectorCalculus3`）：在向量微積分簽名上加 NS 定常解
所需的符號算子與法則。詮釋層（真黎曼 3-流形微分算子）待 mathlib 微分幾何；此前，任何
用到此結構的定理都理解為「對所有滿足此簽名的詮釋成立」。 -/
structure NSCalculus3 (M : Type*) [TopologicalSpace M] extends VectorCalculus3 M where
  /-- **前提 A**：黏滯項的拉普拉斯算子 = **Hodge Laplacian `dd* + d*d`**（符號；非 Bochner）。 -/
  hodgeLap : Vec → Vec
  /-- 自對流（self-advection）`∇_X X = (u·∇)u`（符號）。 -/
  conv : Vec → Vec
  /-- 壓力梯度 `∇p`（符號）。 -/
  grad : (M → ℝ) → Vec
  /-- 零向量場。 -/
  zero : Vec
  /-- 向量場減法（符號）。 -/
  sub : Vec → Vec → Vec
  /-- 向量場取負（符號）。 -/
  neg : Vec → Vec
  /-- 法則：`ν • 0 = 0`（純量乘零）。 -/
  smul_zero : ∀ r : ℝ, smul r zero = zero
  /-- 法則：`w − 0 = w`。 -/
  sub_zero : ∀ w : Vec, sub w zero = w
  /-- **骨架步驟 4（Cartan 恆等式，簽名法則）**：調和場（`ΔX = 0`）的自對流是梯度場
  `∇_X X = ∇(½|X|²) = −∇(−½|X|²)`——即存在壓力見證。真幾何內容、此處抽象承載。 -/
  harmonic_conv_isGrad : ∀ u : Vec, hodgeLap u = zero → ∃ p : M → ℝ, conv u = neg (grad p)

namespace NSCalculus3

variable {M : Type*} [TopologicalSpace M] (N : NSCalculus3 M)

/-- **調和向量場**（Hodge-調和）：`Δ_H X = 0`（對偶 1-形式 closed + coclosed 的結果）。 -/
def IsHarmonic (u : N.Vec) : Prop := N.hodgeLap u = N.zero

/-- **Navier–Stokes 定常**動量方程（黏滯係數 `ν`）：存在壓力 `p` 使
`∇_X X − ν ΔX = −∇p`（`ΔX` = **Hodge Laplacian**，前提 A）。

**注意（審計後校正）**：本 `Prop` **只含動量方程**，**不含**不可壓縮條件 `div u = 0`——
後者是**另一個**條件（調和場經 `d*α = 0` ⟹ `div X = 0`，見檔頭 §2）。且整個 M7 是抽象簽名層、
機器確認 trivially 可滿足（`trivialNS_vacuous`），故「不可壓縮 NS」在此為**名義簽名**、非真解。 -/
def IsNSSteady (ν : ℝ) (u : N.Vec) : Prop :=
  ∃ p : M → ℝ, N.sub (N.conv u) (N.smul ν (N.hodgeLap u)) = N.neg (N.grad p)

/-- **★ Proposition 4.1 的動量方程部分（Dyhr et al. 2025/2026）★**：
調和向量場滿足 Navier–Stokes 定常動量方程，**對任意 `ν` 成立**（黏滯項消失）。

證明骨架步驟 3：因 `ΔX = 0`（調和），黏滯項 `ν ΔX = ν • 0 = 0` 對任意 `ν` 消失，
動量方程化為 `∇_X X = −∇p`；步驟 4（`harmonic_conv_isGrad`）供壓力見證。

**機器證的是推導結構**（黏滯項為何對任意 `ν` 消失）；結論 `IsNSSteady`
不含 `div u = 0`，故本定理本身不宣稱不可壓縮性。真幾何內容在簽名法則、抽象空洞
（見 `trivialNS_vacuous`）。 -/
theorem prop_4_1 (u : N.Vec) (h : N.IsHarmonic u) (ν : ℝ) : N.IsNSSteady ν u := by
  obtain ⟨p, hp⟩ := N.harmonic_conv_isGrad u h
  have hz : N.hodgeLap u = N.zero := h
  exact ⟨p, by rw [hz, N.smul_zero, N.sub_zero]; exact hp⟩

end NSCalculus3

/-! ## 誠實整合：抽象 NS 簽名的空洞性（機器背書，保護誠信）

同 M5 `reebBeltramiRealization_trivial`：抽象簽名下 `IsNSSteady` **無條件 trivially 可滿足**，
故 `prop_4_1` 的真內容是**推導結構**、非真流體 NS 物理。真物理需真微分幾何（mathlib 無）。 -/

/-- 退化 NS 詮釋（`Vec = Unit`、所有算子平凡）——見證抽象簽名可滿足。 -/
def trivialNS {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M) : NSCalculus3 M where
  Vec := Unit
  curl := id
  div := fun _ _ ↦ 0
  flowOf := fun _ ↦ F
  smul := fun _ ↦ id
  hodgeLap := id
  conv := id
  grad := fun _ ↦ ()
  zero := ()
  sub := fun _ _ ↦ ()
  neg := id
  smul_zero := fun _ ↦ rfl
  sub_zero := fun _ ↦ rfl
  harmonic_conv_isGrad := fun _ _ ↦ ⟨fun _ ↦ 0, rfl⟩

/-- **抽象 NS 層空洞**（機器背書）：退化詮釋下**每個場對每個 `ν` 都是「NS 定常解」且調和**
——證明 `IsNSSteady` / `IsHarmonic` 在簽名級 trivially 可滿足。故 `prop_4_1` 不建立真實
Navier–Stokes 流的性質；真物理內容（Hodge Laplacian 真定義 + Cartan 恆等式）需真微分幾何、
mathlib 無、paper-blocked。**不誇大**（硬規則 2/3）。 -/
theorem trivialNS_vacuous {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M) :
    ∀ (u : (trivialNS F).Vec) (ν : ℝ), (trivialNS F).IsNSSteady ν u ∧ (trivialNS F).IsHarmonic u :=
  fun _ _ ↦ ⟨⟨fun _ ↦ 0, rfl⟩, rfl⟩

/-! ## Step 3 — 抽象定常動量方程 capstone（條件定理，方案 A）

把 `prop_4_1`（調和 ⟹ NS-steady 對任意 ν）+ **調和場幾何實現假設**
`ReebHarmonicRealization` + 已證離散→連續模擬鏈 `suspension_flow_simulates`，複合成
主定理給出被模擬流、`IsHarmonic` 與對任意 `ν` 的 `IsNSSteady`。這兩個舊謂詞
都不把 `div u = 0` 放進結論；不可壓縮性必須另列為假設與結論，見下游 additive
規格層。

**`ReebHarmonicRealization`（明寫假設，folds 論文 Theorem A + Prop 4.3/Lemma 4.5 的
全部 paper-blocked 幾何）**：任意緊空間連續流可實現為某緊空間上抽象
`NSCalculus3` 的**調和向量場**之流、經單射共軛。正式型別沒有宣稱該空間是
真流形。
這一個假設意圖包住：
- **前提 B**：Hodge-admissible 流形（Tischler：纖維化到 `S¹`）；
- **度量形變 `g_ε`**（Prop 4.3 / Lemma 4.5）：只支撐在嵌入實心環面 `T = D × S¹`、`T` 外
  `g̃ = g`、`T` 內把 `β` 改成 `β̃` 植入模擬 TM 的回歸映射並保 `α = ⋆_g̃ β̃`（`X̃` 仍調和）；
- Reeb 場 = 調和場（餘辛結構）。

**Chern–Hamilton 注意**（arXiv:2505.10379）：某些 `b₁ ≥ 2`、有餘辛結構卻無 critical
compatible metric 的流形上度量形變不可行；故此假設**只對形變可行的流形類成立**，不對
任意 Hodge-admissible 流形無痛宣稱——此限制 folded 進假設的可滿足性（下方 `_trivial`
只證抽象簽名可滿足、非真幾何）。

**誠實範圍**：主定理零 sorry、條件於此一幾何輸入；真內容 = 離散→連續模擬鏈（全證）；
`ReebHarmonicRealization` 抽象可滿足（`reebHarmonicRealization_trivial`）、真幾何 mathlib 無、
paper-blocked。不冒充真流體 NS。 -/

/-- **調和場抽象實現假設**（明寫，方案 A）：
任意緊空間連續流 `F` 可實現為某緊空間上
`NSCalculus3` 結構的 `IsHarmonic` 場 `u` 之流、經單射 `ψ` 共軛。正式結論只有
`hodgeLap u = zero`，不含流形結構或 `div u = 0`；真幾何意圖來自論文 Theorem A +
Prop 4.3/Lemma 4.5（Hodge-admissibility + 度量形變 + Reeb=調和）。 -/
def ReebHarmonicRealization : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [CompactSpace M] (F : ContinuousFlowOn M),
    ∃ (M' : Type) (_ : TopologicalSpace M') (_ : CompactSpace M')
      (N : NSCalculus3.{0, 0} M') (u : N.Vec) (ψ : M → M'),
      Function.Injective ψ ∧ N.IsHarmonic u ∧
        ∀ (t : ℝ) (x : M), (N.flowOf u).φ t (ψ x) = ψ (F.φ t x)

/-- **★ 舊版抽象 NS capstone（方案 A 條件定理）★**：
給定調和場抽象實現假設，任意緊空間自同胚 `e` 被某緊空間上 `NSCalculus3` 場 `u`
的流模擬。結論明列：

- `N.IsHarmonic u`，其正式定義僅為 `N.hodgeLap u = N.zero`；
- `∀ ν, N.IsNSSteady ν u`，即抽象定常**動量方程**；
- `Simulates ...`。

它**不**斷言 `curl u = λ • u`、Beltrami 或 `div u = 0`，因此不可稱為正式的
不可壓縮 Navier–Stokes 解。整層抽象簽名亦可 trivially 滿足
（`trivialNS_vacuous`）。證明只複合
`suspension_flow_simulates`、`hgeo` 與 `prop_4_1`；舊 statement 保留作 API 相容。 -/
theorem navier_stokes_turing_complete (hgeo : ReebHarmonicRealization)
    {X : Type} [TopologicalSpace X] [CompactSpace X] (e : X ≃ₜ X) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (N : NSCalculus3.{0, 0} M) (u : N.Vec) (enc : X → M),
      N.IsHarmonic u ∧ (∀ ν : ℝ, N.IsNSSteady ν u) ∧ Simulates (N.flowOf u) (⇑e) enc := by
  obtain ⟨M, iT, iC, F, enc, hinj, hstep⟩ := suspension_flow_simulates e
  obtain ⟨M', iT', iC', N, u, ψ, hψinj, hharm, hconj⟩ := hgeo M F
  refine ⟨M', iT', iC', N, u, ψ ∘ enc, hharm, fun ν ↦ N.prop_4_1 u hharm ν,
    hψinj.comp hinj, fun c ↦ ?_⟩
  obtain ⟨t, ht, hft⟩ := hstep c
  exact ⟨t, ht, by rw [Function.comp_apply, hconj t (enc c), hft, Function.comp_apply]⟩

/-- 誠實整合：`ReebHarmonicRealization` **抽象可滿足**（退化 `trivialNS` 見證）——故 NS
主定理的真內容在離散→連續鏈、非（抽象空洞的）幾何層。同 `reebBeltramiRealization_trivial`。 -/
theorem reebHarmonicRealization_trivial : ReebHarmonicRealization := by
  intro M _ _ F
  exact ⟨M, ‹_›, ‹_›, trivialNS F, (), id, Function.injective_id, rfl, fun _ _ ↦ rfl⟩

end FluidTuring
