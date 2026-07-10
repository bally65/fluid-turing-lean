import FluidTuringLean.M21_MtrConfig

/-!
# Module 22 — route β 起手：接 mathlib TM 化約鏈（M_tr 本體 4b）

**路線決策（見 `docs/UNDECIDABILITY_LINE.md`）**：mathlib `Turing.TM2to1` / `TM1to1` / `TM1to0`
**已證** TM2 → TM1 → TM1(Bool 字母) → TM0(Bool) 的完整化約——含把 4 堆疊交錯到帶、頭走位到
堆疊頂（`addBottom` + `(Tape.move right)^[(S k).length]`），正是 M3e/M17/M19 手刻的走位+編碼。
三段皆保停機（`tr_eval_dom` / `tr_eval`）+ 有限可達（`tr_supports`）。

⟹ 不手刻走位。route β = 複用這條鏈 + 只補「TM0(Bool) → 我們的 `BitTM`」有界橋，兌現 M20
`bitTM_bennett_blowup_undecidable` 的 `hmachine`。

**本塊（4b 第一鑽）**：補鏈需要、mathlib 缺的 instance，並確認第一段（`TM2to1`）在**我們的
機器參數**（`K' / Γ' / Λ' / Option Γ'`）上可套用（停機橋 `tr_eval_dom`）。

- `Fintype K'`：mathlib 只 derive `DecidableEq/Inhabited`，但 `TM1to1` 的 Bool 字母化約需要
  `Fintype (Γ' K' Γ)`（`Γ' = Bool × ∀ k, Option (Γ k)`），而它需要 `Fintype K'`。本塊補上（4 元）。
- `tm2to1_halts_iff`：通用 TM2 機器經 `TM2to1` 化約成 TM1，停機保持——確認鏈在我們的參數上成立。
-/

namespace FluidTuring

open Turing

/-- **`K'` 的 `Fintype`**（mathlib 只 derive `DecidableEq/Inhabited`）：4 個堆疊索引
`main/rev/aux/stack`。route β 的 Bool 字母化約（`TM1to1`）需要 `Fintype (Γ' K' Γ)` ⟸ `Fintype K'`。 -/
instance instFintypeK' : Fintype Turing.PartrecToTM2.K' :=
  ⟨{.main, .rev, .aux, .stack}, fun k ↦ by cases k <;> decide⟩

open Turing.PartrecToTM2 in
/-- **route β 第一段**：任意 TM2 機器 `M` 經 mathlib `TM2to1` 化約成 TM1，**停機保持**
（`TM2to1.tr_eval_dom`）。確認化約鏈在我們的機器參數（`K' / Γ' / Λ' / Option Γ'`）上可套用。 -/
theorem tm2to1_halts_iff (M : Λ' → TM2.Stmt (fun _ : K' ↦ Γ') Λ' (Option Γ'))
    (k : K') (L : List Γ') :
    (TM1.eval (TM2to1.tr M) (TM2to1.trInit k L)).Dom ↔ (TM2.eval M k L).Dom :=
  TM2to1.tr_eval_dom M k L

end FluidTuring
