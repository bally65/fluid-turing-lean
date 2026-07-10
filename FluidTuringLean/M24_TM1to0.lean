import FluidTuringLean.M23_TM1to1Bool

/-!
# Module 24 — route β 第三段：TM1(Bool) → TM0(Bool)（`TM1to0`）（M_tr 本體 4b-3）

`TM1to1`（M23）把 TM1 降到 2 符號 Bool 帶。本塊用 mathlib `Turing.TM1to0` 把 TM1 化成
**TM0**（原子機器：一步 = 讀頭 + 依 `(狀態, 讀符)` 寫**或**移一格），字母不變（Bool）。TM0 的
一步語意最接近我們的 `BitTM`（讀→動作），是接「TM0(Bool) → 我們 BitTM」橋（4b-4）的正確終點。

**mathlib 給的**：`tr_eval`（**eval 等式**，比 TM1to1 的 `Respects` 更強）+ `tr_respects`
（組態級每步模擬）+ `tr_supports`（有限可達，需 `Fintype σ`）。TM0 的狀態型
`Λ' M = Option (TM1.Stmt Γ Λ σ) × σ`（無限型、但有限可達）。

**本塊交付（4b-3）**：
- `tm1to0_halts_iff`：組態級停機橋（`tr_respects` ∘ `StateTransition.tr_eval_dom`，參數化於 init
  翻譯 `h`），與 M22/M23 同介面、供整鏈組合。
- `tm1to0_eval`：**eval 等式**（`tr_eval`，直接給）——`TM0.eval = TM1.eval`。
- `tm1to0_supports`：有限可達導出（`tr_supports`，需 `Fintype σ`）。
-/

namespace FluidTuring

open Turing

open scoped Classical in
open Turing.TM1to0 in
/-- **route β 第三段停機橋**：TM1 → TM0（同字母）的組態級停機保持。由 `TM1to0.tr_respects`
（每步模擬）經 `StateTransition.tr_eval_dom` 導出，參數化於 init 組態翻譯 `h`。 -/
theorem tm1to0_halts_iff {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) {c₁ : TM1.Cfg Γ Λ σ} {c₂ : TM0.Cfg Γ (TM1to0.Λ' M)}
    (h : TM1to0.trCfg M c₁ = c₂) :
    (StateTransition.eval (TM0.step (TM1to0.tr M)) c₂).Dom ↔
      (StateTransition.eval (TM1.step M) c₁).Dom :=
  StateTransition.tr_eval_dom (TM1to0.tr_respects M) h

open Turing.TM1to0 in
/-- **eval 等式**（mathlib `tr_eval` 直接給）：TM0 emulator 的 eval = 原 TM1 的 eval。 -/
theorem tm1to0_eval {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) (l : List Γ) :
    TM0.eval (TM1to0.tr M) l = TM1.eval M l :=
  TM1to0.tr_eval M l

open scoped Classical in
open Turing.TM1to0 in
/-- **有限可達導出**：TM1 有限支撐 ⟹ TM0 emulator 有限支撐（`trStmts`，需 `Fintype σ`）。 -/
theorem tm1to0_supports {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt Γ Λ σ) {S : Finset Λ} (ss : TM1.Supports M S) :
    TM0.Supports (TM1to0.tr M) ↑(TM1to0.trStmts M S) :=
  TM1to0.tr_supports (M := M) ss

end FluidTuring
