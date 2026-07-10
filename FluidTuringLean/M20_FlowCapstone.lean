import FluidTuringLean.M14_OrbitFaithful
import FluidTuringLean.M3c_Bennett

/-!
# Module 20 — 流 blowup 不可判定的組裝頂石（(ii) B2c：下游全鏈接合）

**本塊發現（重要）**：到「懸掛流的有限時間 blowup 觸發不可判定」的**下游全鏈已證且已接**：
- `suspension_flow_simulates_faithful`（M14）：**任意**緊空間自同胚 `e : X ≃ₜ X` 的懸掛流
  忠實模擬 `⇑e`（Simulates + OrbitFaithful 皆定理）。
- `coupled_blowup_undecidable`（M14）：忠實模擬 + 前向可達不可判定 ⟹ blowup 觸發不可判定
  （複用 M10 `finite_time_blowup_undecidable` + mathlib `halting_problem`）。

本塊把兩者**組裝**成單一頂石 `suspension_blowup_trigger_undecidable`：

> **任意**緊空間自同胚 `e`，配一個 `e`-前向封閉的「停機集」`H` 與通用機器接線 `huniv`
> （`e` 迭代 `k+1` 步打進 `H` ⟺ code 在輸入 `n` 停機）⟹ 其懸掛流的
> 「∃ 正時間打進 `enc '' H`」謂詞**不可計算**。

⟹ **整個流體端不可判定性歸約到唯一一條建構義務**：造一個緊空間自同胚 `e`（= M3c
`bennettHomeo` 之於某位元機 `M_tr`），其前向可達性編碼通用 TM2 停機（M16 已證 TM2 停機
不可判定）。這正是 B2a 子塊 4「M_tr 建構」——**非 paper-blocked**（mathlib 有全部零件）、
是大型多 session 工程。本頂石**誠實外顯**該缺口（同 M7 NS 的方案 A 條件化手法）。

**第二定理** `bitTM_bennett_blowup_undecidable`：把頂石實例化到 `e := bennettHomeo M`，並用
`bennettAut_iterate`（M3c，無時間膨脹）把 `huniv` 從**機器級** `M.step` 停機對應**證出**——
只剩 `bennettAut`-不變停機集封閉性 + `M.step` 級對應兩條 crisp 義務給 M_tr。
-/

namespace FluidTuring

open Nat.Partrec MappingTorus

/-! ## 頂石：緊自同胚 + 前向可達不可判定 ⟹ 懸掛流 blowup 觸發不可判定 -/

/-- **★組裝頂石★**：任意緊空間自同胚 `e : X ≃ₜ X`，若其 `k+1` 步前向可達某 `e`-封閉集 `H`
逐 code 等價於通用機器停機（`huniv`），則**存在**其懸掛流（緊 Hausdorff、忠實模擬 `⇑e`），
使「∃ 正時間打進 `enc '' H`」謂詞**不可計算**。

= `suspension_flow_simulates_faithful`（流構造 + 忠實性）∘ `coupled_blowup_undecidable`
（忠實 + huniv → 不可判定）。把下游全鏈壓成單一「有前向可達不可判定的緊自同胚 ⟹ 流 blowup
不可判定」。 -/
theorem suspension_blowup_trigger_undecidable {X : Type} [TopologicalSpace X] [CompactSpace X]
    (e : X ≃ₜ X) (H : Set X) (init : Code → X)
    (hH : ∀ code : Code, init code ∈ H → e (init code) ∈ H) (n : ℕ)
    (huniv : ∀ code : Code, (∃ k : ℕ, (⇑e)^[k + 1] (init code) ∈ H) ↔ (code.eval n).Dom) :
    ∃ (M : Type) (_ : TopologicalSpace M) (F : ContinuousFlowOn M) (enc : X → M),
      Simulates F (⇑e) enc ∧
      ¬ ComputablePred (fun code : Code =>
          ∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code)) ∈ enc '' H) := by
  obtain ⟨M, tM, cM, F, enc, hsim, hfaith⟩ := suspension_flow_simulates_faithful e
  exact ⟨M, tM, F, enc, hsim,
    coupled_blowup_undecidable hsim hfaith H init hH n huniv⟩

/-! ## bennett 層歸約：把頂石實例化到位元機的可逆化 -/

open BitTM in
/-- **★bennett 層歸約★**：對**任意**位元機 `M`（不必可逆），若其**機器級** `M.step` 迭代
`k+1` 步打進停機集 `Hcfg` 逐 code 等價通用機停機（`hmachine`），且 `Hcfg` 之提升在
`bennettAut` 下前向封閉（`hHclosed`），則 `M` 的 Bennett 可逆化（`bennettHomeo`，緊自同胚）
的懸掛流之 blowup 觸發**不可計算**。

`huniv` 由 `bennettAut_iterate`（M3c，無時間膨脹：`bennettAut^[k] (c, blankHist)` 的工作分量
= `M.step^[k] c`）從 `hmachine` **證出**——把流層可達性精確降到機器層停機。

⟹ **整個流體端不可判定性 = 兩條 crisp 義務**：(1) `hmachine`（`M.step` 模擬通用 TM2 停機，
配 M16 `tm2_halting_undecidable`）(2) `hHclosed`（停機集 bennett-不變）。兩者 = B2a 子塊 4
的 M_tr 建構要交付的東西——**誠實外顯的唯一剩餘缺口**。 -/
theorem bitTM_bennett_blowup_undecidable (M : BitTM)
    (Hcfg : Set M.Cfg) (init : Code → M.Cfg) (n : ℕ)
    (hHclosed : ∀ code : Code, init code ∈ Hcfg → M.step (init code) ∈ Hcfg)
    (hmachine : ∀ code : Code,
        (∃ k : ℕ, M.step^[k + 1] (init code) ∈ Hcfg) ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : (M.Cfg × (ℤ → M.HistRec)) → Mt),
      Simulates F (⇑M.bennettHomeo) enc ∧
      ¬ ComputablePred (fun code : Code =>
          ∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code, M.blankHist))
            ∈ enc '' {p | p.1 ∈ Hcfg}) := by
  -- 工作分量：bennettHomeo 迭代的第一座標 = M.step 迭代（無時間膨脹）
  have hfst : ∀ (c : M.Cfg) (k : ℕ),
      ((⇑M.bennettHomeo)^[k] (c, M.blankHist)).1 = M.step^[k] c := by
    intro c k
    simp only [M.coe_bennettHomeo]
    obtain ⟨η, heq, _⟩ := M.bennettAut_iterate c k
    exact congrArg Prod.fst heq
  -- 前向封閉性（僅需 init 點：init 的歷史空白 ⟹ bennettAut 第一分量 = M.step，無 Feistel 擾動）
  have hH : ∀ code : Code,
      (init code, M.blankHist) ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg} →
      M.bennettHomeo (init code, M.blankHist) ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg} := by
    intro code hmem
    simp only [Set.mem_setOf_eq] at hmem ⊢
    have h1 : (M.bennettHomeo (init code, M.blankHist)).1 = M.step (init code) := by
      simpa using hfst (init code) 1
    rw [h1]
    exact hHclosed code hmem
  -- 通用接線：降到機器層
  have huniv : ∀ code : Code,
      (∃ k : ℕ, (⇑M.bennettHomeo)^[k + 1] (init code, M.blankHist)
        ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg}) ↔ (code.eval n).Dom := by
    intro code
    rw [← hmachine code]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa only [Set.mem_setOf_eq, hfst (init code) (k + 1)] using hk⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only [Set.mem_setOf_eq, hfst (init code) (k + 1)]
      exact hk
  exact suspension_blowup_trigger_undecidable M.bennettHomeo
    {p | p.1 ∈ Hcfg} (fun code ↦ (init code, M.blankHist)) hH n huniv

end FluidTuring
