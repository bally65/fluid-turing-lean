import FluidTuringLean.M33_FluidCapstone

/-!
# Module 36 — 封頂推論：流全域封閉（avoidance）不可判定

封頂 `fluid_blowup_undecidable`（M33）證「流軌道**到達**編碼停機區」不可判定。`ComputablePred`
對補集封閉（`ComputablePred.not`），故其**否定**——「流軌道**永遠避開**目標區（全域封閉 /
不爆、confinement）」——**亦不可判定**。這是封頂的乾淨補集推論，補上「不可判定線」的另一半
（M10 `global_existence_undecidable` 的流層實例）。
-/

namespace FluidTuring

open Nat.Partrec

/-- **★流全域封閉（avoidance）不可判定★**：存在緊空間連續時間流 `F`、基點族 `base`、目標集
`Target`，使「code 的軌道於**所有正時間都避開** `Target`（全域封閉 / 永不到達）」**無演算法可判定**。

= 封頂 `fluid_blowup_undecidable`（到達不可判定）的補集（`ComputablePred.not`）；`ComputablePred`
對補集封閉，故到達不可判定 ⟺ 避開不可判定。 -/
theorem fluid_confinement_undecidable (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (F : ContinuousFlowOn X)
      (base : Nat.Partrec.Code → X) (Target : Set X),
      ¬ ComputablePred (fun code : Nat.Partrec.Code =>
          ¬ ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target) := by
  obtain ⟨X, tX, cX, F, base, Target, hundec⟩ := fluid_blowup_undecidable n
  refine ⟨X, tX, cX, F, base, Target, fun hcomp ↦ hundec ?_⟩
  exact hcomp.not.of_eq (fun _ ↦ not_not)

end FluidTuring
