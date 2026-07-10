import FluidTuringLean.M6_EulerTuring

/-!
# Module 9 — 不可判定性推論（計算骨幹的記憶點結論）

「流體可模擬圖靈機」最有記憶點的**後果方向**：**停機 ⟹ 流軌道抵達編碼終態**
（`halts_imp_orbitReaches`，由 `Simulates.iterate` + 單射編碼）。

**★誠實範圍（審計後校正 2026-07-10）★**：本檔**只證正向** `停機 ⟹ 可達`。要把「不可判定性」
真正轉移到可達性，需要**逆向** `可達 ⟹ 停機`（否則正向只給「不停機」半可判定，不給還原）。
逆向需**軌道忠實性**（orbit-faithfulness）——它在 **M14** `orbitReaches_iff_halts` 才證出
（配 M14 `suspension_flow_simulates_faithful`，對懸掛流是定理）。故「可達性 ⟺ 停機」的**等價**
與「可達性不可判定」的完整還原**不在本檔**，而在 M14（並最終於 M33 無條件收尾）。本檔的
`halts_imp_orbitReaches` 是該還原的**正向半邊**，語句真確、無誇大。

（文獻脈絡：Cardona–Miranda–Peralta-Salas–Presas / Dyhr 等把不可判定性帶進流體動力學；本專案的
完整無條件不可判定結果在 M33。）
-/

namespace FluidTuring

/-- **軌道可達性**：從 `x` 出發、某正時間的流落在集合 `S`。 -/
def OrbitReaches {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M)
    (x : M) (S : Set M) : Prop :=
  ∃ t : ℝ, 0 < t ∧ F.φ t x ∈ S

/-- **★停機 ⟹ 流可達性（還原）★**：若離散動力系統 `step` 從 `c` 於 `n+1` 步後進入
「終態集」`H`（= 停機），則連續流 `F` 的軌道從編碼 `enc c` 出發**抵達 `H` 的編碼像**
`enc '' H`。直接由 `Simulates.iterate`（軌道以正時間實現任意步數）+ 單射編碼。

**意義**：這是「停機還原到可達性」的**正向半邊**。完整還原（＋逆向 `可達 ⟹ 停機`，需
軌道忠實性）在 M14 `orbitReaches_iff_halts`；由此得的「可達性不可判定」無條件版在 M33。
**本定理只斷言正向**，不單獨蘊含等價或不可判定。 -/
theorem halts_imp_orbitReaches {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M} (h : Simulates F step enc)
    (c : Γ) (H : Set Γ) (n : ℕ) (hn : step^[n + 1] c ∈ H) :
    OrbitReaches F (enc c) (enc '' H) := by
  obtain ⟨t, ht, hft⟩ := h.iterate c n
  exact ⟨t, ht, ⟨step^[n + 1] c, hn, hft.symm⟩⟩

/-- **忠實性（單射保領域）**：不同組態的編碼互異——確保「抵達 `enc '' H`」真對應
「進入 `H`」，還原不失真（`Simulates` 已含 `enc` 單射）。 -/
theorem enc_injective_of_simulates {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M} (h : Simulates F step enc) :
    Function.Injective enc :=
  h.1

end FluidTuring
