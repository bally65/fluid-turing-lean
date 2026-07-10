import FluidTuringLean.M30_UnivConfig

/-!
# Module 31 — TM2to1 通用組態橋（M_tr 本體 4b-5b-B1）

B1：把 M30 的具體 TM2 組態 `init cu v` 經 `TM2to1` 化約到 TM1 的組態對應 `TrCfg`。

**關鍵洞見**：`init cu v` 堆疊 = `K'.elim (trList v) [] [] []`（main = trList v、其餘空）——與
`TM2.init main (trList v)` 同形。`TrCfg` 的 `L` 條件只依堆疊，故直接建 `L`（trList v 進 main 軌）
並鏡射 mathlib `trCfg_init` 的投影證明（該證只用「S k = trList v（k=main）否則 []」，正合 K'.elim）。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2

/-- init cu v 經 TM2to1 化約後對應的 TM1 組態（main 軌 = trList v）。 -/
noncomputable def univTM1Cfg (cu : Turing.ToPartrec.Code) (v : List ℕ) :
    Turing.TM1.Cfg (Turing.TM2to1.Γ' K' fun _ ↦ Γ')
      (Turing.TM2to1.Λ' K' (fun _ ↦ Γ') Λ' (Option Γ')) (Option Γ') :=
  ⟨(some (trNormal cu Cont'.halt)).map Turing.TM2to1.Λ'.normal, none,
    Turing.Tape.mk' ∅ (Turing.TM2to1.addBottom
      (Turing.ListBlank.mk ((trList v).reverse.map
        fun a ↦ Function.update (default : ∀ _ : K', Option Γ') K'.main (some a))))⟩

/-- **B1：通用組態的 `TrCfg`**（直接建 `L`、鏡射 `trCfg_init` 投影證）。 -/
theorem trCfg_init_univ (cu : Turing.ToPartrec.Code) (v : List ℕ) :
    Turing.TM2to1.TrCfg (init cu v) (univTM1Cfg cu v) := by
  rw [univTM1Cfg]
  refine Turing.TM2to1.TrCfg.mk _ (fun k' ↦ ?_)
  refine Turing.ListBlank.ext fun i ↦ ?_
  rw [Turing.ListBlank.map_mk, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.map_map]
  have hcomp : ((Turing.proj k').f ∘
      fun a ↦ Function.update (default : ∀ _ : K', Option Γ') K'.main (some a))
    = fun a ↦ (Turing.proj k').f
      (Function.update (default : ∀ _ : K', Option Γ') K'.main (some a)) := rfl
  rw [hcomp, List.getElem?_map, Turing.proj, PointedMap.mk_val]
  cases k' with
  | main =>
    simp only [Function.update_self, K'.elim_main]
    rw [Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD, ← List.map_reverse, List.getElem?_map]
  | rev =>
    simp only [Function.update_of_ne (show K'.rev ≠ K'.main by decide), K'.elim_rev,
      List.map_nil, List.reverse_nil, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    cases (trList v).reverse[i]? <;> rfl
  | aux =>
    simp only [Function.update_of_ne (show K'.aux ≠ K'.main by decide), K'.elim_aux,
      List.map_nil, List.reverse_nil, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    cases (trList v).reverse[i]? <;> rfl
  | stack =>
    simp only [Function.update_of_ne (show K'.stack ≠ K'.main by decide), K'.elim_stack,
      List.map_nil, List.reverse_nil, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    cases (trList v).reverse[i]? <;> rfl

/-- **B1 停機橋**：`init cu v` 經 `TM2to1` 化約到 TM1、組態層停機保持
（`tr_respects` ∘ `StateTransition.tr_eval_dom`）。 -/
theorem tm2to1_univ_halts_iff (cu : Turing.ToPartrec.Code) (v : List ℕ) :
    (StateTransition.eval (Turing.TM1.step (Turing.TM2to1.tr tr)) (univTM1Cfg cu v)).Dom ↔
      (StateTransition.eval (Turing.TM2.step tr) (init cu v)).Dom :=
  StateTransition.tr_eval_dom (Turing.TM2to1.tr_respects tr) (trCfg_init_univ cu v)

end FluidTuring
