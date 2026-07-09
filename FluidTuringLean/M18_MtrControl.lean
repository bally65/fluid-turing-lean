import FluidTuringLean.M16_TM2Wiring
import FluidTuringLean.M17_TM2Layout

/-!
# Module 18 — M_tr 控制有限性（(ii) B2a 子塊 1：route A 地基）

M_tr（不可逆掃描解釋器）的**控制狀態**要塞進 `Fin m → Bool`（有限），這是 route A
勝過 route B（`ToPartrec.step` 無界丟失）的關鍵。本塊把 mathlib 已證的
`Turing.PartrecToTM2.tr_supports`（`tr` 的可達 TM2 label 全落在 `codeSupp c Cont'.halt`
這個 **`Finset Λ'`**、forward-closed）抬成 M_tr 可用的地基 + label 的 `Fin` 位元編碼。

即：M_tr 的 label 分量 = `Fin (trLabels c).card`；`c` = M16 `tm2_univ_wiring` 的固定通用碼。
剩（B2c）：把 forward-closure 從 statement 級（`SupportsStmt`）連到 `stepAux` 級的
「一 TM2 步後 label 仍 ∈ trLabels」。
-/

namespace FluidTuring

open Turing Turing.ToPartrec Turing.PartrecToTM2

/-- M_tr 控制的**有限狀態集**：固定碼 `c` 的可達 TM2 label 全落在此 `Finset Λ'`。 -/
def trLabels (c : Code) : Finset Λ' := codeSupp c Cont'.halt

/-- **★控制有限性★**（= mathlib `tr_supports`）：`tr` 於 `trLabels c` 是 `TM2.Supports`
——初始 label ∈、且每個 label 的 statement forward-closed（gotos 全落回 `trLabels c`）。
route A 的地基：M_tr 的 label 分量塞得進固定有限集。 -/
theorem tr_supports_trLabels (c : Code) :
    @TM2.Supports _ _ _ _ ⟨trNormal c Cont'.halt⟩ tr (trLabels c) :=
  tr_supports c Cont'.halt

/-- 初始 label `trNormal c Cont'.halt` ∈ `trLabels c`（`Supports` 的第一半）。 -/
theorem trNormal_mem_trLabels (c : Code) : trNormal c Cont'.halt ∈ trLabels c :=
  (tr_supports_trLabels c).1

/-- statement forward-closure（`Supports` 的第二半）：每個 `q ∈ trLabels c` 的
`tr q` 的所有 goto 目標仍 ∈ `trLabels c`。 -/
theorem trLabels_supportsStmt (c : Code) :
    ∀ q ∈ trLabels c, TM2.SupportsStmt (trLabels c) (tr q) :=
  (tr_supports_trLabels c).2

/-- **label ↔ `Fin (card)`**：M_tr 控制 label 分量的位元編碼（route A 的有限控制）。 -/
noncomputable def trLabelEquivFin (c : Code) : ↥(trLabels c) ≃ Fin (trLabels c).card :=
  (Fintype.equivFin _).trans (finCongr (Fintype.card_coe _))

end FluidTuring
