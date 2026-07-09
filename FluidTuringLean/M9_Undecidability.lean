import FluidTuringLean.M6_EulerTuring

/-!
# Module 9 — 不可判定性推論（計算骨幹的記憶點結論）

「流體可模擬圖靈機」最有記憶點、最好引用的**後果**：**流的軌道可達性不可判定**
（= 停機問題）。本模組把它形式化為**還原**（reduction）——不去形式化「不可判定」
本身（需完整 `Turing` 框架 + Rice/停機），而是機器證出**停機 ⟹ 流軌道抵達編碼終態**，
這正是「停機問題還原到流可達性」的數學內容。誠實界線：不可判定性由此還原 + Turing
停機問題不可判定（外部經典結果）推得，narrative 層，非本檔形式化斷言。

**一句話結論**：任何被連續流忠實模擬的圖靈計算，其「軌道會不會抵達某區域」等價於
「那台機器會不會停機」——因後者不可判定（Turing 1936），前者亦不可判定。這是
Cardona–Miranda–Peralta-Salas–Presas / Dyhr 等把不可判定性帶進流體動力學的核心。
-/

namespace FluidTuring

/-- **軌道可達性**：從 `x` 出發、某正時間的流落在集合 `S`。 -/
def OrbitReaches {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M)
    (x : M) (S : Set M) : Prop :=
  ∃ t : ℝ, 0 < t ∧ F.φ t x ∈ S

/-- **★停機 ⟹ 流可達性（還原）★**：若離散動力系統 `step` 從 `c` 於 `n+1` 步後進入
「終態集」`H`（= 停機），則連續流 `F` 的軌道從編碼 `enc c` 出發**抵達 `H` 的編碼像**
`enc '' H`。直接由 `Simulates.iterate`（軌道以正時間實現任意步數）+ 單射編碼。

**意義**：把「圖靈機停機？」還原成「流軌道抵達某區域？」。後者若可判定則前者可判定，
與 Turing 停機問題不可判定矛盾 ⟹ **流可達性不可判定**。這是流體圖靈完備性的記憶點推論。 -/
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
