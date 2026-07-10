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

/-! ## 4b-4d-ii：串成迭代 -/

/-- 控制在 `encHalt` 的組態，一步後控制仍在 `encHalt`（`Mtr_step_halt` 的第一分量版）。 -/
theorem Mtr_step_fst_halt {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    (c : (Mtr M S).Cfg) (h : c.1 = encHalt S) : ((Mtr M S).step c).1 = encHalt S := by
  obtain ⟨s, t⟩ := c
  obtain rfl : s = encHalt S := h
  rw [Mtr_step_halt]

/-- 執行中組態的控制 ≠ `encHalt`（可達標籤 `some ≠ none`、`encCtrl` 單射）。 -/
theorem encTM0_fst_ne_encHalt {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) {c : Turing.TM0.Cfg Bool Λ} (hc : c.q ∈ S) :
    (encTM0 M S c).1 ≠ encHalt S := by
  intro h
  simp only [encTM0] at h
  have h2 := encCtrl_injective S h
  rw [ctrlOfLabel, dif_pos hc] at h2
  exact absurd h2 (Option.some_ne_none _)

/-- `TM0.step` 展開（用 `actApply`）。 -/
theorem tm0_step_eq {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (c : Turing.TM0.Cfg Bool Λ) :
    Turing.TM0.step M c = (M c.q c.Tape.head).map fun p ↦ ⟨p.1, actApply p.2 c.Tape⟩ := by
  obtain ⟨q, T⟩ := c
  simp only [Turing.TM0.step]
  congr 1
  funext p
  obtain ⟨q', a⟩ := p
  cases a <;> rfl

/-- **★軌道追蹤不變式★**：`totalize (TM0.step)` 迭代 `k` 步的結果決定 M_tr 迭代 `k` 步的狀態
（`some ck` → M_tr = `encTM0 ck` 且 `ck.q ∈ S`；`none` → M_tr 控制 = `encHalt`）。串 M27/M28
一步三案 + `Supports` 前向封閉，對 `k` 歸納。 -/
theorem Mtr_track {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    (hSupp : Turing.TM0.Supports M ↑S) (c0 : Turing.TM0.Cfg Bool Λ) (hc0 : c0.q ∈ S) (k : ℕ) :
    (∀ ck, (totalize (Turing.TM0.step M))^[k] (some c0) = some ck →
        (Mtr M S).step^[k] (encTM0 M S c0) = encTM0 M S ck ∧ ck.q ∈ S) ∧
    ((totalize (Turing.TM0.step M))^[k] (some c0) = none →
        ((Mtr M S).step^[k] (encTM0 M S c0)).1 = encHalt S) := by
  induction k with
  | zero =>
    refine ⟨fun ck hck ↦ ?_, fun h ↦ ?_⟩
    · simp only [Function.iterate_zero, id_eq] at hck ⊢
      obtain rfl := Option.some.inj hck
      exact ⟨rfl, hc0⟩
    · simp only [Function.iterate_zero, id_eq] at h
      exact absurd h (Option.some_ne_none c0)
  | succ k ih =>
    obtain ⟨ih_some, ih_none⟩ := ih
    simp only [Function.iterate_succ_apply']
    rcases Option.eq_none_or_eq_some ((totalize (Turing.TM0.step M))^[k] (some c0)) with
      hk | ⟨ck, hk⟩
    · -- IH：M_tr 第 k 步已在 encHalt；totalize 停留 none
      have hmtr : ((Mtr M S).step^[k] (encTM0 M S c0)).1 = encHalt S := ih_none hk
      rw [hk]
      exact ⟨fun c hc ↦ absurd hc (by simp [totalize_none]),
        fun _ ↦ Mtr_step_fst_halt M S _ hmtr⟩
    · -- IH：M_tr 第 k 步 = encTM0 ck
      obtain ⟨hmtr, hckS⟩ := ih_some ck hk
      rw [hk, totalize_some, hmtr, tm0_step_eq]
      cases hM : M ck.q ck.Tape.head with
      | none =>
        simp only [Option.map_none]
        refine ⟨fun c hc ↦ absurd hc (by simp), fun _ ↦ ?_⟩
        rw [show encTM0 M S ck = encTM0 M S ⟨ck.q, ck.Tape⟩ from rfl, Mtr_step_toHalt M S hckS hM]
      | some p =>
        obtain ⟨q', a⟩ := p
        simp only [Option.map_some]
        have hq' : q' ∈ S := Finset.mem_coe.mp (hSupp.2 hM (Finset.mem_coe.mpr hckS))
        refine ⟨fun c hc ↦ ?_, fun h ↦ absurd h (by simp)⟩
        obtain rfl := Option.some.inj hc
        rw [show encTM0 M S ck = encTM0 M S ⟨ck.q, ck.Tape⟩ from rfl,
          Mtr_step_run M S hckS hq' hM]
        exact ⟨rfl, hq'⟩

/-- **★停機橋★**：M_tr 從 `encTM0 c0` 迭代到 `encHalt` 控制 ⟺ TM0 從 `c0` 停機
（`StateTransition.eval` 有定義）。= 把一步模擬串成迭代 + M16 `totalize_halts_iff_eval_dom`。 -/
theorem Mtr_halts_iff {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    (hSupp : Turing.TM0.Supports M ↑S) (c0 : Turing.TM0.Cfg Bool Λ) (hc0 : c0.q ∈ S) :
    (∃ k : ℕ, ((Mtr M S).step^[k + 1] (encTM0 M S c0)).1 = encHalt S) ↔
      (StateTransition.eval (Turing.TM0.step M) c0).Dom := by
  rw [← totalize_halts_iff_eval_dom]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rcases Option.eq_none_or_eq_some ((totalize (Turing.TM0.step M))^[k + 1] (some c0)) with
      h | ⟨ck, h⟩
    · exact h
    · exfalso
      obtain ⟨hmtr, hckS⟩ := (Mtr_track M S hSupp c0 hc0 (k + 1)).1 ck h
      rw [hmtr] at hk
      exact encTM0_fst_ne_encHalt M S hckS hk
  · rintro ⟨k, hk⟩
    exact ⟨k, (Mtr_track M S hSupp c0 hc0 (k + 1)).2 hk⟩

end FluidTuring
