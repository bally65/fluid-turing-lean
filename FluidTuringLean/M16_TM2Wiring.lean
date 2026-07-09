import FluidTuringLean.M15_UniversalWiring
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Module 16 — TM2 停機介面（(ii) B1：`docs/UNDECIDABILITY_LINE.md` 規格第一塊）

(ii) 路線 A 經 mathlib TM2：`Turing.PartrecToTM2.tr` 是**一台固定的 TM2 機器**
（有限狀態、有限字母堆疊——**每步丟失有界**，Bennett 適用、BitTM 可編譯），
mathlib 已證 `tr_eval : eval (TM2.step tr) (init c v) = halt <$> c.eval v`。

本模組 = M15 模式**泛化**到任意 `f : σ → Option σ`（M15 的證明骨架逐字通用），再
實例化到 TM2：
- `totalize f`：任意部分 step 的全化（`none` 吸收）。
- `totalize_halts_iff_eval_dom`：`∃k` 迭代碰 `none` ⟺ `StateTransition.eval` 有定義。
- `tm2_halts_iff_code_eval_dom`：**TM2 機器停機 ⟺ `ToPartrec.Code.eval` 有定義**。
- `tm2_univ_wiring` + **`tm2_halting_undecidable`（無條件）**：TM2 家族停機不可判定。

下一塊 B2（核心）：把 `tr` 編譯成本專案 `BitTM`（宏步、方案 C 走位機器復用）。
-/

namespace FluidTuring

/-- **泛化全化**：任意部分 step `f : σ → Option σ` 的全化，`none` 為吸收固定點。 -/
def totalize {σ : Type*} (f : σ → Option σ) : Option σ → Option σ := fun oc ↦ oc.bind f

@[simp] theorem totalize_none {σ : Type*} (f : σ → Option σ) : totalize f none = none := rfl

@[simp] theorem totalize_some {σ : Type*} (f : σ → Option σ) (c : σ) :
    totalize f (some c) = f c := rfl

/-- 泛化：`Reaches` ⟹ 迭代（M15 `stepT_iterate_of_reaches` 的通用版）。 -/
theorem totalize_iterate_of_reaches {σ : Type*} {f : σ → Option σ} {a b : σ}
    (h : StateTransition.Reaches f a b) :
    ∃ k : ℕ, (totalize f)^[k] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, totalize_some, hbc]⟩

/-- 泛化：迭代碰 `none` ⟹ `eval` 有定義（M15 `dom_of_stepT_halts` 的通用版）。 -/
theorem dom_of_totalize_halts {σ : Type*} {f : σ → Option σ} (cfg : σ) (k : ℕ)
    (h : (totalize f)^[k + 1] (some cfg) = none) :
    (StateTransition.eval f cfg).Dom := by
  induction k generalizing cfg with
  | zero =>
    rw [Function.iterate_one, totalize_some] at h
    exact Part.dom_iff_mem.mpr
      ⟨cfg, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h⟩⟩
  | succ m ih =>
    cases hstep : f cfg with
    | none =>
      exact Part.dom_iff_mem.mpr
        ⟨cfg, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hstep⟩⟩
    | some cfg' =>
      have h' : (totalize f)^[m + 1] (some cfg') = none := by
        have := h
        rw [Function.iterate_succ_apply, totalize_some, hstep] at this
        exact this
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (ih cfg' h')
      obtain ⟨hreach, hnone⟩ := StateTransition.mem_eval.mp hb
      exact Part.dom_iff_mem.mpr ⟨b, StateTransition.mem_eval.mpr
        ⟨Relation.ReflTransGen.head (Option.mem_def.mpr hstep) hreach, hnone⟩⟩

/-- **泛化停機介面**：任意部分 step——`∃k` 迭代碰 `none` ⟺ `eval` 有定義。 -/
theorem totalize_halts_iff_eval_dom {σ : Type*} (f : σ → Option σ) (cfg : σ) :
    (∃ k : ℕ, (totalize f)^[k + 1] (some cfg) = none) ↔
      (StateTransition.eval f cfg).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    exact dom_of_totalize_halts cfg k hk
  · intro hdom
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨hreach, hnone⟩ := StateTransition.mem_eval.mp hb
    obtain ⟨k, hk⟩ := totalize_iterate_of_reaches hreach
    exact ⟨k, by rw [Function.iterate_succ_apply', hk, totalize_some, hnone]⟩

/-! ## TM2 實例：mathlib 通用 TM2 機器 `tr` 的停機介面 -/

open Turing.PartrecToTM2 in
/-- **TM2 機器停機 ⟺ `ToPartrec.Code.eval` 有定義**（經 mathlib `tr_eval`）。 -/
theorem tm2_halts_iff_code_eval_dom (c : Turing.ToPartrec.Code) (v : List ℕ) :
    (∃ k : ℕ, (totalize (Turing.TM2.step tr))^[k + 1] (some (init c v)) = none) ↔
      (c.eval v).Dom := by
  rw [totalize_halts_iff_eval_dom, tr_eval]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
    obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
    exact Part.dom_iff_mem.mpr ⟨a, ha⟩
  · intro h
    exact Part.dom_iff_mem.mpr
      ⟨halt ((c.eval v).get h), Part.mem_map _ (Part.get_mem h)⟩

open Turing.PartrecToTM2 in
/-- **TM2 通用機器接線**（B1 版 `univ_wiring`）：∃ 初始組態族，∀ `Nat.Partrec.Code`：
TM2 機器迭代停機 ⟺ `(code.eval n₀).Dom`。 -/
theorem tm2_univ_wiring (n₀ : ℕ) :
    ∃ init' : Nat.Partrec.Code → Option Cfg',
      ∀ code : Nat.Partrec.Code,
        (∃ k : ℕ, (totalize (Turing.TM2.step tr))^[k + 1] (init' code) = none) ↔
          (code.eval n₀).Dom := by
  have hf : Partrec fun m : ℕ ↦
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n₀ :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const n₀)
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨fun code ↦ some (init cu [Encodable.encode code]), fun code ↦ ?_⟩
  change (∃ k : ℕ, (totalize (Turing.TM2.step tr))^[k + 1]
      (some (init cu [Encodable.encode code])) = none) ↔ (code.eval n₀).Dom
  rw [tm2_halts_iff_code_eval_dom]
  have hv := hcu (Encodable.encode code ::ᵥ List.Vector.nil)
  simp only [List.Vector.head_cons, Denumerable.ofNat_encode] at hv
  have hv' : cu.eval [Encodable.encode code] = pure <$> code.eval n₀ := hv
  rw [hv']
  exact Iff.rfl

open Turing.PartrecToTM2 in
/-- **★TM2 家族停機不可判定（無條件、零假設）★**：B1 capstone。`tr` 是有限狀態 ×
有限字母堆疊的機器（每步丟失有界）——**這台**機器的家族停機不可判定，且它可
Bennett 化、可 BitTM 編譯（= B2 的輸入）。 -/
theorem tm2_halting_undecidable (n₀ : ℕ) :
    ∃ init' : Nat.Partrec.Code → Option Cfg',
      ¬ ComputablePred fun code : Nat.Partrec.Code =>
          ∃ k : ℕ, (totalize (Turing.TM2.step tr))^[k + 1] (init' code) = none := by
  obtain ⟨init', hiff⟩ := tm2_univ_wiring n₀
  refine ⟨init', ?_⟩
  have heq : (fun code : Nat.Partrec.Code =>
        ∃ k : ℕ, (totalize (Turing.TM2.step tr))^[k + 1] (init' code) = none)
      = fun code : Nat.Partrec.Code => (code.eval n₀).Dom :=
    funext fun code ↦ propext (hiff code)
  rw [heq]
  exact ComputablePred.halting_problem n₀

end FluidTuring
