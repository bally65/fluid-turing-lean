import Mathlib.Computability.TuringMachine.Config
import Mathlib.Computability.StateTransition

/-!
# Module 15 — 通用機器接線 I（huniv 的機器側：mathlib TM 語意 → M14 停機形狀）

M14 `coupled_blowup_undecidable` 剩最後一條假設 `huniv`：
`(∃ k, step^[k+1] (init code) ∈ H) ⟺ (code.eval n).Dom`。本模組打通它的**機器側**：
把 mathlib 真的 TM 語意（`Turing.ToPartrec.step`，`StateTransition.eval` = Reaches + 停機）
翻譯成 M14 需要的 **`∃k` 迭代進停機集**形狀。

構造：`Turing.ToPartrec.step : Cfg → Option Cfg` 是部分函數（`none` = 已停機）。
**全化**：`stepT : Option Cfg → Option Cfg := ·.bind step`——`none` 是吸收固定點
（= M14 `hH` 停機區吸收假設的具體實現）。停機集 `H = {none}`。

**成果**：
- `stepT_iterate_of_reaches` / `dom_of_stepT_halts`：`stepT` 迭代 ⟺ `StateTransition.Reaches`。
- `stepT_halts_iff_eval_dom`：**`∃k` 迭代碰 `none` ⟺ `eval` 有定義**。
- `stepT_halts_iff_code_eval_dom`：接 `stepNormal_eval` ⟹ 對任意 mathlib
  `ToPartrec.Code` 與輸入 `v`：**機器停機 ⟺ `(c.eval v).Dom`**——huniv 的形狀、
  對 mathlib 真 TM 模型成立。

**誠實界線（剩餘接線、多 session）**：(i) `Nat.Partrec.Code`（M10 用的）→
`ToPartrec.Code` 的通用碼（mathlib `exists_code` + `eval_part` 鏈、純 computability
plumbing）；(ii) `stepT` 的**緊空間同胚實現**（`Option Cfg` 離散非緊；要走本專案
M3 康托爾編碼 + Bennett 管線需 machine-model 橋 `ToPartrec.Cfg` ↔ `BitTM`）。
本塊價值 = huniv 的停機介面**第一次接地到 mathlib 真 TM 語意**、非抽象假設。
-/

namespace FluidTuring

open Turing.ToPartrec

/-- **全化 step**：`none`（已停機）為吸收固定點、`some cfg` 走真 `step`。 -/
def stepT : Option Cfg → Option Cfg := fun oc ↦ oc.bind Turing.ToPartrec.step

@[simp] theorem stepT_none : stepT none = none := rfl

@[simp] theorem stepT_some (c : Cfg) : stepT (some c) = Turing.ToPartrec.step c := rfl

/-- `Reaches` ⟹ 迭代：可達的組態必為某步迭代的落點。 -/
theorem stepT_iterate_of_reaches {a b : Cfg}
    (h : StateTransition.Reaches Turing.ToPartrec.step a b) :
    ∃ k : ℕ, stepT^[k] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, stepT_some, hbc]⟩

/-- 迭代碰到 `none` ⟹ `StateTransition.eval` 有定義（停機語意的正向）。 -/
theorem dom_of_stepT_halts (cfg : Cfg) (k : ℕ) (h : stepT^[k + 1] (some cfg) = none) :
    (StateTransition.eval Turing.ToPartrec.step cfg).Dom := by
  induction k generalizing cfg with
  | zero =>
    rw [Function.iterate_one, stepT_some] at h
    exact Part.dom_iff_mem.mpr ⟨cfg, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h⟩⟩
  | succ m ih =>
    cases hstep : Turing.ToPartrec.step cfg with
    | none =>
      exact Part.dom_iff_mem.mpr
        ⟨cfg, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hstep⟩⟩
    | some cfg' =>
      have h' : stepT^[m + 1] (some cfg') = none := by
        have := h
        rw [Function.iterate_succ_apply, stepT_some, hstep] at this
        exact this
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (ih cfg' h')
      obtain ⟨hreach, hnone⟩ := StateTransition.mem_eval.mp hb
      exact Part.dom_iff_mem.mpr ⟨b, StateTransition.mem_eval.mpr
        ⟨Relation.ReflTransGen.head (Option.mem_def.mpr hstep) hreach, hnone⟩⟩

/-- **★停機 ⟺ eval 有定義★**（M14 `huniv` 需要的形狀、對 mathlib 真 TM 語意成立）：
`stepT` 迭代有限步碰到吸收停機點 `none` ⟺ `StateTransition.eval` 有定義。 -/
theorem stepT_halts_iff_eval_dom (cfg : Cfg) :
    (∃ k : ℕ, stepT^[k + 1] (some cfg) = none) ↔
      (StateTransition.eval Turing.ToPartrec.step cfg).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    exact dom_of_stepT_halts cfg k hk
  · intro hdom
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨hreach, hnone⟩ := StateTransition.mem_eval.mp hb
    obtain ⟨k, hk⟩ := stepT_iterate_of_reaches hreach
    exact ⟨k, by rw [Function.iterate_succ_apply', hk, stepT_some, hnone]⟩

/-- **機器停機 ⟺ `Code.eval` 有定義**：對 mathlib `ToPartrec.Code` 的任意程式 `c` 與
輸入 `v`，從標準初始組態（`stepNormal c Cont.halt v`）出發的 `stepT` 迭代停機
⟺ `(c.eval v).Dom`。經 `stepNormal_eval`（mathlib 已證的機器⟺語意橋）。 -/
theorem stepT_halts_iff_code_eval_dom (c : Code) (v : List ℕ) :
    (∃ k : ℕ, stepT^[k + 1] (some (stepNormal c Cont.halt v)) = none) ↔ (c.eval v).Dom := by
  rw [stepT_halts_iff_eval_dom, stepNormal_eval]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
    obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
    exact Part.dom_iff_mem.mpr ⟨a, ha⟩
  · intro h
    exact Part.dom_iff_mem.mpr
      ⟨Cfg.halt ((c.eval v).get h), Part.mem_map _ (Part.get_mem h)⟩

end FluidTuring
