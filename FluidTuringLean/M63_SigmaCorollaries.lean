import FluidTuringLean.M59_SmoothUndecidable

/-!
# Module 63 — σ 線推論：`sigmaRL3_reachability_undecidable` 的補集版

流線（連續流）在 M36 有 `fluid_confinement_undecidable`——「避開 `Target`」與「打進 `Target`」
同樣不可判定，因為 `ComputablePred` 對補集封閉。**σ 線（離散光滑映射）一直沒有這條**，
本磚補上，形狀與證明逐字鏡射 `M36_Corollaries.lean:22-28`。

## ★誠實範圍★

- **零新內容。** 這是 `ComputablePred.not` 的一行套用；強度與 `sigmaRL3_reachability_undecidable`
  （M59:211）完全相同，不多不少。列出來的理由是對稱性：流線有、σ 線沒有，讀者會問為什麼。
- σ 為 **C^∞ 而非 analytic**（`sfloor_not_analytic`，M60:78：本 scaffold 經 `sfloor`
  （M46:75 → M58:90），**永遠**升不到 analytic），且 `sigmaM` 與其編碼器皆 `noncomputable`。
- 離散映射**不是**連續流；連續流版本的 robustification 是死牆（M56）。
-/

namespace FluidTuring

open Turing

/-- **σ 線的「避開」版不可判定**（`sigmaRL3_reachability_undecidable` 的補集）。

`ComputablePred` 對補集封閉（`ComputablePred.not`），故「軌道於某步打進 `Target`」不可判定
⟺「軌道**永遠避開** `Target`」不可判定。與 M36 的 `fluid_confinement_undecidable`
（連續流版）成對。 -/
theorem sigmaRL3_confinement_undecidable (n : ℕ) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : Nat.Partrec.Code → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ¬ ComputablePred (fun code : Nat.Partrec.Code =>
            ¬ ∃ k : ℕ, σ^[k] (base code) ∈ Target) := by
  obtain ⟨σ, hσ, base, Target, hundec⟩ := sigmaRL3_reachability_undecidable n
  exact ⟨σ, hσ, base, Target, fun hcomp ↦ hundec (hcomp.not.of_eq (fun _ ↦ not_not))⟩

/-! ## σ 線的完整計算複雜度定位（單一 σ、四合一） -/

/-- **★σ 軌道可達性的完整定位（單一 σ、四合一）★**：存在**同一個**顯式 C^∞ 映射 `σ`、基點族
`base`、目標集 `Target`，其可達謂詞同時滿足——

1. **精確歸約**：`∀ code, 可達 ⟺ (code.eval n).Dom`（= 停機問題，多一還原）；
2. **不可判定**：`¬ComputablePred 可達`；
3. **r.e./半可判定（Σ₁）**：`REPred 可達`——有部分程序半判定；
4. **補集亦不可判定**：`¬ComputablePred (¬可達)`。

⟹ 這個**顯式 C^∞ 的 ℝ³ 自映射**，其軌道可達性**恰好坐落在 Σ₁ \ Δ₁**，與停機問題**同級**。
全部由 `sigmaRL3_reach_characterization`（M59）的單一 iff 導出。
與流線的 `fluid_reach_full_characterization`（M37:189）成對。

**這比 `sigmaRL3_reachability_undecidable` 強**：那條只說「不可判定」，這條說「是停機問題本身」。
零新數學——證明是四次套用 mathlib 的 `ComputablePred.halting_problem` /
`halting_problem_re` / `ComputablePred.not`。 -/
theorem sigmaRL3_reach_full_characterization (n : ℕ) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : Nat.Partrec.Code → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        (∀ code : Nat.Partrec.Code,
            (∃ k : ℕ, σ^[k] (base code) ∈ Target) ↔ (code.eval n).Dom)
        ∧ ¬ ComputablePred (fun code : Nat.Partrec.Code =>
              ∃ k : ℕ, σ^[k] (base code) ∈ Target)
        ∧ REPred (fun code : Nat.Partrec.Code =>
              ∃ k : ℕ, σ^[k] (base code) ∈ Target)
        ∧ ¬ ComputablePred (fun code : Nat.Partrec.Code =>
              ¬ ∃ k : ℕ, σ^[k] (base code) ∈ Target) := by
  obtain ⟨σ, hσ, base, Target, hiff⟩ := sigmaRL3_reach_characterization n
  have heq : (fun code : Nat.Partrec.Code => ∃ k : ℕ, σ^[k] (base code) ∈ Target)
      = (fun code => (code.eval n).Dom) := funext fun code ↦ propext (hiff code)
  refine ⟨σ, hσ, base, Target, hiff, ?_, ?_, ?_⟩
  · rw [heq]; exact ComputablePred.halting_problem n
  · rw [heq]; exact ComputablePred.halting_problem_re n
  · intro hcomp
    exact ComputablePred.halting_problem n (heq ▸ hcomp.not.of_eq (fun _ ↦ not_not))

end FluidTuring
