import FluidTuringLean.M22_MathlibReduction

/-!
# Module 23 — route β 第二段：TM1 字母 → Bool 字母（`TM1to1`）（M_tr 本體 4b-2）

`TM2to1`（M22）把 TM2 化成 TM1，字母 = `Γ' K' Γ = Bool × ∀ k, Option (Γ k)`（有限、非 Bool）。
本塊用 mathlib `Turing.TM1to1` 把它降到 **2 符號（Bool）帶**：每個字母符號編成 `n` 位塊、讀寫
頭走 `n` 格讀一符號（`readAux`），`O(1)` 額外開銷、停機保持。

**mathlib 給的**：`tr_respects`（每步被模擬、停機保持）+ `tr_supports`（有限可達）+
`exists_enc_dec`（**任意 `Finite` 字母免費得 bit 編碼** `enc/dec` + `enc default = 0` + round-trip）。
mathlib **不給** eval/init 助手、也**不預先組合**整條鏈。

**本塊交付（4b-2）**：
- `tm1to1_halts_iff`：組態級停機橋——`TM1to1.tr_respects` 經 `StateTransition.tr_eval_dom` 導出。
  參數化於 init 組態翻譯 `h : trCfg enc enc0 c₁ = c₂`（具體 init 翻譯留待組裝 4b-4/5，誠實）。
- `tm1to1_supports`：有限可達導出（`tr_supports`）。
- `tm1to1_enc`：從 `Finite` 字母取 mathlib `exists_enc_dec` 的編碼（route β 後續要餵的 `enc/dec`）。
-/

namespace FluidTuring

open Turing

open Turing.TM1to1 in
/-- **route β 第二段停機橋**：TM1（字母 `Γ`）→ TM1（Bool 字母）的組態級停機保持。由 mathlib
`TM1to1.tr_respects`（每步被模擬）經 `StateTransition.tr_eval_dom` 導出。參數化於 init 組態翻譯 `h`。 -/
theorem tm1to1_halts_iff {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) {n : ℕ} (enc : Γ → List.Vector Bool n)
    (dec : List.Vector Bool n → Γ) (encdec : ∀ a, dec (enc a) = a)
    {enc0 : enc default = List.Vector.replicate n false}
    {c₁ : TM1.Cfg Γ Λ σ} {c₂ : TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ}
    (h : TM1to1.trCfg enc enc0 c₁ = c₂) :
    (StateTransition.eval (TM1.step (TM1to1.tr enc dec M)) c₂).Dom ↔
      (StateTransition.eval (TM1.step M) c₁).Dom :=
  StateTransition.tr_eval_dom (TM1to1.tr_respects (M := M) (enc := enc) (dec := dec) encdec) h

open scoped Classical in
open Turing.TM1to1 in
/-- **有限可達導出**：輸入機器有限支撐 ⟹ Bool 字母機器有限支撐（`trSupp`）。字母 `Γ` 需
`Fintype`（`trSupp`/`writes` 列舉所有可寫符號）——我們的 `Γ' K' Γ` 由 `instFintypeK'` 供給。 -/
theorem tm1to1_supports {Γ Λ σ : Type*} [Inhabited Γ] [Fintype Γ] [Inhabited Λ]
    (M : Λ → TM1.Stmt Γ Λ σ) {n : ℕ} (enc : Γ → List.Vector Bool n)
    (dec : List.Vector Bool n → Γ) {S : Finset Λ} (ss : TM1.Supports M S) :
    TM1.Supports (TM1to1.tr enc dec M) (TM1to1.trSupp M S) :=
  TM1to1.tr_supports (M := M) (enc := enc) (dec := dec) ss

/-- **編碼取得**：任意 `Finite` `Inhabited` 字母，mathlib `exists_enc_dec` 免費給 bit 編碼
（`enc default = 0` + round-trip）。route β 後續（TM1to1 套用）要餵的 `enc/dec`。 -/
theorem tm1to1_enc (Γ : Type*) [Inhabited Γ] [Finite Γ] :
    ∃ (n : ℕ) (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ),
      enc default = List.Vector.replicate n false ∧ ∀ a, dec (enc a) = a :=
  TM1to1.exists_enc_dec

end FluidTuring
