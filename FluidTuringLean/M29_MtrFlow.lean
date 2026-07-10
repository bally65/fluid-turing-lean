import FluidTuringLean.M28_HaltBridge
import FluidTuringLean.M20_FlowCapstone

/-!
# Module 29 — M_tr 流層組裝（M_tr 本體 4b-5b-A）

把 M_tr 的停機橋（M28 `Mtr_halts_iff`）接到 M20 的 bennett 頂石
（`bitTM_bennett_blowup_undecidable`），得到流層最終定理——歸約到唯一一條**純機器**義務
`hcorr`（reduced TM0-Bool 機器的 `eval` 停機 ⟺ `code.eval` 停機）。

`hcorr` 由化約鏈（M22/23/24 + M16）兌現 = 4b-5b-B（最後的 mathlib 接線）。
-/

namespace FluidTuring

open Nat.Partrec

/-- **★M_tr 流層不可判定★（條件於機器對應 `hcorr`）**：任意 TM0-Bool 機器 `M`（有限支撐 `S`、
init 組態控制皆可達），若其 `eval` 停機逐 code 對應 `code.eval n` 停機（`hcorr`），則
`M` 的 M_tr 之 Bennett 可逆化懸掛流的 blowup 觸發**不可計算**。

= M28 `Mtr_halts_iff`（M_tr 迭代到 `encHalt` ⟺ TM0 `eval` 停機）+ M28 `Mtr_step_fst_halt`
（停機吸收兌現 `hHclosed`）+ M20 `bitTM_bennett_blowup_undecidable`。剩 `hcorr` = 化約鏈（4b-5b-B）。 -/
theorem mtr_flow_blowup_undecidable {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) (hSupp : Turing.TM0.Supports M ↑S)
    (init : Code → Turing.TM0.Cfg Bool Λ) (n : ℕ) (hinit_q : ∀ code, (init code).q ∈ S)
    (hcorr : ∀ code : Code,
        (StateTransition.eval (Turing.TM0.step M) (init code)).Dom ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : ((Mtr M S).Cfg × (ℤ → (Mtr M S).HistRec)) → Mt),
      Simulates F (⇑(Mtr M S).bennettHomeo) enc ∧
      ¬ ComputablePred (fun code : Code =>
          ∃ t : ℝ, 0 < t ∧ F.φ t (enc (encTM0 M S (init code), (Mtr M S).blankHist))
            ∈ enc '' {p | p.1 ∈ {c : (Mtr M S).Cfg | c.1 = encHalt S}}) := by
  refine bitTM_bennett_blowup_undecidable (Mtr M S) {c : (Mtr M S).Cfg | c.1 = encHalt S}
    (fun code ↦ encTM0 M S (init code)) n ?_ ?_
  · -- hHclosed：init 控制 = encHalt ⟹ 一步後仍 encHalt（停機吸收）
    intro code hmem
    exact Mtr_step_fst_halt M S _ hmem
  · -- hmachine：M_tr 迭代到 encHalt ⟺ TM0 eval 停機 ⟺ code.eval 停機
    intro code
    simp only [Set.mem_setOf_eq]
    rw [Mtr_halts_iff M S hSupp (init code) (hinit_q code), hcorr code]

end FluidTuring
