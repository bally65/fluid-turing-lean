import FluidTuringLean.M27_MtrMachine

/-!
# Module 28 — TM0(Bool) → 我們 BitTM 橋之四：停機橋（M_tr 本體 4b-4d）

M27 給了一步模擬的兩案：`Mtr_step_run`（TM0 續跑 `M q head = some (q',act)` → 追蹤）、
`Mtr_step_halt`（`encHalt` 自環 = 停機吸收）。缺第三案：**TM0 在此停機**
（`M q head = none`）→ M_tr 走到 `encHalt`。三案齊 = 完整一步語意。

本塊起手（4b-4d-i）：`Mtr_step_toHalt`。之後（4b-4d-ii）把三案串成迭代 + 對接 TM0 停機
（`StateTransition.eval`）：`∃k, (M_tr.step^[k] (encTM0 c0)).1 = encHalt` ⟺ TM0 從 `c0` 停機。
-/

namespace FluidTuring

/-- **停機轉移**：TM0 在 `⟨q,T⟩` 停機（`M q head = none`、`q ∈ S`）⟹ M_tr 一步走到 `encHalt`
（控制 → 停機槽、帶不變）。完成一步語意第三案。 -/
theorem Mtr_step_toHalt {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    {q : Λ} {T : Turing.Tape Bool} (hq : q ∈ S) (hact : M q T.head = none) :
    (Mtr M S).step (encTM0 M S ⟨q, T⟩) = (encHalt S, fun i ↦ T.nth i) := by
  have hdec : decCtrl S (encCtrl S (ctrlOfLabel S q)) = some ⟨q, hq⟩ := by
    rw [decCtrl_encCtrl]; simp [ctrlOfLabel, hq]
  simp only [encTM0]
  rw [BitTM.step_eval]
  simp only [Turing.Tape.nth_zero]
  have hsd : stepData M S (encCtrl S (ctrlOfLabel S q)) T.head
      = ((none : ctrlType S), T.head, Dir.stay) := by
    simp only [stepData, hdec, hact]
  simp only [Mtr, hsd, Dir.toInt, add_zero]
  refine Prod.ext rfl ?_
  funext n
  by_cases hn : n = 0 <;> simp [hn, Turing.Tape.nth_zero]

end FluidTuring
