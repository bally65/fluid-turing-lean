import FluidTuringLean.M7_NavierStokes

/-!
# Module 61 — 不可壓縮 NS 的 additive 規格修補（抽象簽名層）

M7 的舊 API 把兩件事分開：`IsHarmonic u` 只表示 `hodgeLap u = zero`，
`IsNSSteady ν u` 只表示定常動量方程。兩者都**沒有**把不可壓縮條件 `div u = 0`
放進型別。本模組不修改舊 declaration，而以 additive predicates 明確記錄：

* `IsDivergenceFree`：抽象散度逐點為零；
* `IsIncompressibleNSSteady`：divergence-free 與舊動量方程的合取；
* `HasHarmonicNSData`：舊 Hodge-Laplacian kernel 資料與 divergence-free 資料的合取；
* `ReebHarmonicRealizationV2` / `navier_stokes_turing_complete_v2`：把該額外資料一路帶到
  capstone 的結論。

## 誠實範圍

這只是**抽象 signature bookkeeping**，不是 Navier–Stokes PDE 的形式化，也不是
Millennium existence/smoothness 問題的推進。`NSCalculus3` 的 `div`、`hodgeLap`、
`conv`、`grad` 仍是未詮釋符號；本模組沒有建立真 `ℝ³`/`T³` 算子、
初值問題、
Sobolev 正則性或能量估計。下方 `reebHarmonicRealizationV2_trivial` 更明確證明：
即使加上 divergence-free 欄位，退化 `trivialNS` 仍可滿足整個 V2 假設。
因此本模組
的價值是修正規格與假設帳本，不是增加物理內容。
-/

namespace FluidTuring

namespace NSCalculus3

variable {M : Type*} [TopologicalSpace M] (N : NSCalculus3 M)

/-- 抽象 divergence-free 條件：`div u` 在每一點皆為零。

這仍只使用 `NSCalculus3.div` 符號，不宣稱它已詮釋為真黎曼散度。 -/
def IsDivergenceFree (u : N.Vec) : Prop :=
  ∀ x, N.div u x = 0

/-- 不可壓縮定常 NS 的**完整抽象規格**：divergence-free 加上 M7 的定常
動量方程。 -/
def IsIncompressibleNSSteady (ν : ℝ) (u : N.Vec) : Prop :=
  N.IsDivergenceFree u ∧ N.IsNSSteady ν u

/-- M7 `prop_4_1` 所需的 Laplacian-kernel 資料，加上不可壓縮性所需的獨立
div-free 資料。特意用合取而非聲稱 `IsHarmonic → IsDivergenceFree`：該蘊含需要
真 Hodge 理論，現有抽象簽名無法證明。 -/
def HasHarmonicNSData (u : N.Vec) : Prop :=
  N.IsHarmonic u ∧ N.IsDivergenceFree u

/-- harmonic 資料加明寫 div-free 假設，對每個非負黏滯係數導出完整抽象
不可壓縮定常規格。

`prop_4_1` 實際對所有 `ν : ℝ` 證出動量方程；`0 ≤ ν` 在此明列，以對齊物理
NS 的參數範圍。 -/
theorem harmonicNSData_isIncompressibleNSSteady {u : N.Vec}
    (h : N.HasHarmonicNSData u) (ν : ℝ) (_hν : 0 ≤ ν) :
    N.IsIncompressibleNSSteady ν u :=
  ⟨h.2, N.prop_4_1 u h.1 ν⟩

end NSCalculus3

/-! ## V2 realization：把 div-free 明列在幾何輸入 -/

/-- M7 `ReebHarmonicRealization` 的 additive V2：除舊 `IsHarmonic` 外，幾何輸入
還必須明確供應 `IsDivergenceFree`。名稱沿用舊 API 以表示相容升級；
正式型別仍只是
抽象緊拓撲空間與 `NSCalculus3`，不宣稱已構造 Reeb 場、流形或真 NS 算子。 -/
def ReebHarmonicRealizationV2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [CompactSpace M] (F : ContinuousFlowOn M),
    ∃ (M' : Type) (_ : TopologicalSpace M') (_ : CompactSpace M')
      (N : NSCalculus3.{0, 0} M') (u : N.Vec) (ψ : M → M'),
      Function.Injective ψ ∧ N.HasHarmonicNSData u ∧
        ∀ (t : ℝ) (x : M), (N.flowOf u).φ t (ψ x) = ψ (F.φ t x)

/-- V2 忘掉獨立 div-free 資料後給出舊 realization；因此新增規格不破壞
舊 API。 -/
theorem reebHarmonicRealizationV2_to_v1
    (hgeo : ReebHarmonicRealizationV2) : ReebHarmonicRealization := by
  intro M _ _ F
  obtain ⟨M', iT', iC', N, u, ψ, hψinj, hdata, hconj⟩ := hgeo M F
  exact ⟨M', iT', iC', N, u, ψ, hψinj, hdata.1, hconj⟩

/-! ## V2 capstone：結論字面包含不可壓縮性 -/

/-- **V2 抽象 capstone**：若 V2 realization 成立，任意緊空間自同胚可由一個
帶完整 `HasHarmonicNSData` 的抽象場模擬，而且對每個 `ν ≥ 0`，結論字面包含
`IsIncompressibleNSSteady ν u`。

這仍是條件於可退化 signature 的 bookkeeping theorem；不建立真 NS PDE 解。 -/
theorem navier_stokes_turing_complete_v2 (hgeo : ReebHarmonicRealizationV2)
    {X : Type} [TopologicalSpace X] [CompactSpace X] (e : X ≃ₜ X) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (N : NSCalculus3.{0, 0} M) (u : N.Vec) (enc : X → M),
      N.HasHarmonicNSData u ∧
        (∀ ν : ℝ, 0 ≤ ν → N.IsIncompressibleNSSteady ν u) ∧
          Simulates (N.flowOf u) (⇑e) enc := by
  obtain ⟨M, iT, iC, F, enc, hinj, hstep⟩ := suspension_flow_simulates e
  obtain ⟨M', iT', iC', N, u, ψ, hψinj, hdata, hconj⟩ := hgeo M F
  refine ⟨M', iT', iC', N, u, ψ ∘ enc, hdata, ?_, hψinj.comp hinj, fun c ↦ ?_⟩
  · intro ν hν
    exact N.harmonicNSData_isIncompressibleNSSteady hdata ν hν
  · obtain ⟨t, ht, hft⟩ := hstep c
    exact ⟨t, ht, by rw [Function.comp_apply, hconj t (enc c), hft, Function.comp_apply]⟩

/-! ## V2 仍然空洞：退化 `trivialNS` 見證 -/

/-- 在退化 `trivialNS` 中，每個場都同時帶 harmonic 與 divergence-free 資料。
這只揭露 signature 的空洞性，非真幾何。 -/
theorem trivialNS_hasHarmonicNSData {M : Type*} [TopologicalSpace M]
    (F : ContinuousFlowOn M) (u : (trivialNS F).Vec) :
    (trivialNS F).HasHarmonicNSData u := by
  cases u
  exact ⟨rfl, fun _ ↦ rfl⟩

/-- **V2 realization 在抽象簽名下仍無條件成立**：取 `M' = M`、`ψ = id`，
並用 `trivialNS F`。因此 V2 修補的是規格缺項，不把抽象層冒充成真不可壓縮
NS。 -/
theorem reebHarmonicRealizationV2_trivial : ReebHarmonicRealizationV2 := by
  intro M _ _ F
  exact ⟨M, ‹_›, ‹_›, trivialNS F, (), id, Function.injective_id,
    trivialNS_hasHarmonicNSData F (), fun _ _ ↦ rfl⟩

end FluidTuring
