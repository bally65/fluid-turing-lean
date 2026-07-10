import FluidTuringLean.M31_TM2to1Univ

/-!
# Module 32 — 化約鏈 eval 組合（M_tr 本體 4b-5b-B2/B3）

B2（TM1to1）+ B3（TM1to0）：把 B1 的 TM1 停機橋接續到 TM0-Bool，組態翻譯用 `trCfg`（init 翻譯
= `rfl`）。再接 `PartrecToTM2.tr_eval`，得 reduced TM0-Bool 機器從具體組態的 `eval` 停機 ⟺
`cu.eval v` 停機。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2

/-- reduced TM0-Bool 機器：`TM1to0 ∘ TM1to1 ∘ TM2to1` 套到通用 TM2 機器 `tr`。 -/
noncomputable def Muniv {N : ℕ} (enc : Turing.TM2to1.Γ' K' (fun _ ↦ Γ') → List.Vector Bool N)
    (dec : List.Vector Bool N → Turing.TM2to1.Γ' K' (fun _ ↦ Γ')) :=
  Turing.TM1to0.tr (Turing.TM1to1.tr enc dec (Turing.TM2to1.tr tr))

/-- reduced TM0-Bool 機器從 `init cu v` 化約下來的組態。 -/
noncomputable def univTM0Cfg {N : ℕ} (enc : Turing.TM2to1.Γ' K' (fun _ ↦ Γ') → List.Vector Bool N)
    (dec : List.Vector Bool N → Turing.TM2to1.Γ' K' (fun _ ↦ Γ'))
    (enc0 : enc default = List.Vector.replicate N false)
    (cu : Turing.ToPartrec.Code) (v : List ℕ) :=
  Turing.TM1to0.trCfg (Turing.TM1to1.tr enc dec (Turing.TM2to1.tr tr))
    (Turing.TM1to1.trCfg enc enc0 (univTM1Cfg cu v))

/-- **B2+B3 eval 鏈**：reduced TM0-Bool 機器從 `univTM0Cfg` 的 `eval` 停機 ⟺ `cu.eval v` 停機。
= B1 `tm2to1_univ_halts_iff` + M23 `tm1to1_halts_iff` + M24 `tm1to0_halts_iff`（組態翻譯 rfl）+
`PartrecToTM2.tr_eval`。 -/
theorem univ_eval_chain {N : ℕ} (enc : Turing.TM2to1.Γ' K' (fun _ ↦ Γ') → List.Vector Bool N)
    (dec : List.Vector Bool N → Turing.TM2to1.Γ' K' (fun _ ↦ Γ'))
    (encdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate N false)
    (cu : Turing.ToPartrec.Code) (v : List ℕ) :
    (StateTransition.eval (Turing.TM0.step (Muniv enc dec)) (univTM0Cfg enc dec enc0 cu v)).Dom ↔
      (cu.eval v).Dom := by
  have h3 := tm1to0_halts_iff (Turing.TM1to1.tr enc dec (Turing.TM2to1.tr tr))
    (c₁ := Turing.TM1to1.trCfg enc enc0 (univTM1Cfg cu v)) rfl
  have h2 := tm1to1_halts_iff (Turing.TM2to1.tr tr) enc dec encdec
    (enc0 := enc0) (c₁ := univTM1Cfg cu v) rfl
  have h1 := tm2to1_univ_halts_iff cu v
  have h0 : (StateTransition.eval (Turing.TM2.step tr) (init cu v)).Dom ↔ (cu.eval v).Dom := by
    rw [Turing.PartrecToTM2.tr_eval]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
      obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
      exact Part.dom_iff_mem.mpr ⟨a, ha⟩
    · intro h
      exact Part.dom_iff_mem.mpr ⟨halt ((cu.eval v).get h), Part.mem_map _ (Part.get_mem h)⟩
  exact h3.trans (h2.trans (h1.trans h0))

end FluidTuring
