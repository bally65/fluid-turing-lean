import FluidTuringLean.M1_Computability

/-!
# Module 2 — EML 語法樹與連續解釋器

* `EmlExpr`：`{var, const, add, mul, neg, exp, log}` 語法樹。
* `EmlExpr.eval`：對環境 `ρ : ℕ → ℝ` 的連續語意解釋器。
* `eml` 原語可表達（`exp x - log y` 的語法見證）。
* 連續邏輯閘：布林值嵌入 `{0,1} ⊆ ℝ`，NAND 閘 `1 - x·y` 正確模擬 `Bool.nand`（`nandR_boolean`），
  且該 NAND 閘可由語法樹表達。**注意**：NAND 泛函完備（可組成所有布林函數）是**古典 folklore**、
  **未於本檔形式化**（無電路組合定理）；本檔只證**單一 NAND 閘**的連續模擬正確性 + 語法可表達性。
* log-free 片段的解釋器全域連續（對 `ρ` 的乘積拓撲）。

本檔零 sorry。
-/

namespace FluidTuring

/-- EML 運算式語法樹。 -/
inductive EmlExpr : Type
  | var : ℕ → EmlExpr
  | const : ℚ → EmlExpr
  | add : EmlExpr → EmlExpr → EmlExpr
  | mul : EmlExpr → EmlExpr → EmlExpr
  | neg : EmlExpr → EmlExpr
  | exp : EmlExpr → EmlExpr
  | log : EmlExpr → EmlExpr
  deriving DecidableEq, Repr

namespace EmlExpr

/-- 連續語意：在環境 `ρ`（變數賦值）下求值。
`log` 解釋為 mathlib 的全函數 `Real.log`（`≤ 0` 取 junk 值）。 -/
noncomputable def eval (ρ : ℕ → ℝ) : EmlExpr → ℝ
  | var n => ρ n
  | const q => (q : ℝ)
  | add e₁ e₂ => e₁.eval ρ + e₂.eval ρ
  | mul e₁ e₂ => e₁.eval ρ * e₂.eval ρ
  | neg e => -(e.eval ρ)
  | exp e => Real.exp (e.eval ρ)
  | log e => Real.log (e.eval ρ)

/-- `eml` 原語的語法見證：`exp (var 0) + neg (log (var 1))`。 -/
theorem eml_expressible :
    ∃ e : EmlExpr, ∀ ρ : ℕ → ℝ, e.eval ρ = eml (ρ 0) (ρ 1) := by
  refine ⟨add (exp (var 0)) (neg (log (var 1))), fun ρ ↦ ?_⟩
  simp [eval, eml, sub_eq_add_neg]

/-- 不含 `log` 的片段。 -/
def LogFree : EmlExpr → Prop
  | var _ => True
  | const _ => True
  | add e₁ e₂ => LogFree e₁ ∧ LogFree e₂
  | mul e₁ e₂ => LogFree e₁ ∧ LogFree e₂
  | neg e => LogFree e
  | exp e => LogFree e
  | log _ => False

/-- log-free 運算式的解釋器對環境全域連續（`ℕ → ℝ` 取乘積拓撲）。
`log` 在 `0` 不連續，故此定理無法擴到全語言 —— 這正是 Module 1
把 `eml` 的定義域限制在 `y > 0` 的原因。 -/
theorem continuous_eval_of_logFree :
    ∀ e : EmlExpr, LogFree e → Continuous fun ρ : ℕ → ℝ ↦ e.eval ρ
  | var n, _ => continuous_apply n
  | const _, _ => continuous_const
  | add e₁ e₂, h =>
      ((continuous_eval_of_logFree e₁ h.1).add (continuous_eval_of_logFree e₂ h.2))
  | mul e₁ e₂, h =>
      ((continuous_eval_of_logFree e₁ h.1).mul (continuous_eval_of_logFree e₂ h.2))
  | neg e, h => (continuous_eval_of_logFree e h).neg
  | exp e, h => Real.continuous_exp.comp (continuous_eval_of_logFree e h)

end EmlExpr

/-! ## 連續邏輯閘 -/

/-- 布林值嵌入實數：`false ↦ 0`，`true ↦ 1`。 -/
def boolToReal (b : Bool) : ℝ := bif b then 1 else 0

/-- 連續 NAND 閘：`nandR x y = 1 - x * y`。多項式，處處連續。 -/
noncomputable def nandR (x y : ℝ) : ℝ := 1 - x * y

/-- `nandR` 在布林嵌入上正確模擬**單一** NAND 閘（`nandR (bit a) (bit b) = bit (a.nand b)`）。
（NAND 泛函完備 ⟹「所有布林函數」是古典 folklore，**未於此形式化**——本定理只證單閘正確性。） -/
theorem nandR_boolean (a b : Bool) :
    nandR (boolToReal a) (boolToReal b) = boolToReal (!(a && b)) := by
  cases a <;> cases b <;> simp [nandR, boolToReal]

/-- NAND 閘的語法見證：`const 1 + neg (var 0 * var 1)` 是 log-free 運算式。 -/
theorem nand_expressible :
    ∃ e : EmlExpr, e.LogFree ∧
      ∀ ρ : ℕ → ℝ, e.eval ρ = nandR (ρ 0) (ρ 1) := by
  refine ⟨.add (.const 1) (.neg (.mul (.var 0) (.var 1))), ?_, fun ρ ↦ ?_⟩
  · exact ⟨trivial, trivial, trivial⟩
  · simp [EmlExpr.eval, nandR, sub_eq_add_neg]

end FluidTuring
