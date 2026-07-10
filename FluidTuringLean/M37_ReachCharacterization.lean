import FluidTuringLean.M33_FluidCapstone

/-!
# Module 37 — 到達性特徵化（reduction 顯式化）+ 統一推論

封頂 `fluid_blowup_undecidable`（M33）只**外顯** ¬Computable，把核心的**還原 iff**
（`到達 ⟺ code.eval 停機`）藏在證明內部。本模組把該 iff **抬到定理層**——得**特徵化**

> `∃ 流 F、基點 base、目標 Target，∀ code，(∃ t>0, F.φ t (base code) ∈ Target) ⟺ (code.eval n).Dom`

= reduction 的**顯式**陳述（不只「不可判定」，而是「精確**等於**停機問題」）。所有推論
（不可判定、r.e./半可判定、全域封閉不可判定）由此**單一源頭**乾淨導出。

作法：沿 M14→M20→M29 的既有鏈，各層加**平行**的 `_characterization` 定理（回傳 iff 而非
¬Computable，複用各層內部已算好的 iff——比 ¬Computable 版更簡單）。**不動既有定理、零破壞**。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2 Nat.Partrec

/-! ## 特徵化鏈（各層回傳還原 iff） -/

/-- **耦合層特徵化**（= `coupled_blowup_undecidable` 內部的 `hred`）：忠實模擬 + 吸收停機區 +
通用接線 ⟹ 「到達編碼停機區」**恰等於** `code.eval n` 停機。 -/
theorem coupled_blowup_characterization {M : Type} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M}
    (hsim : Simulates F step enc) (hfaith : OrbitFaithful F step enc)
    (H : Set Γ) (init : Nat.Partrec.Code → Γ)
    (hH : ∀ code, init code ∈ H → step (init code) ∈ H) (n : ℕ)
    (huniv : ∀ code, (∃ k : ℕ, step^[k + 1] (init code) ∈ H) ↔ (code.eval n).Dom) :
    ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code)) ∈ enc '' H) ↔ (code.eval n).Dom :=
  fun code ↦ (orbitReaches_iff_halts hsim hfaith (init code) H (hH code)).trans (huniv code)

/-- **懸掛頂石特徵化**：任意緊自同胚 `e` + 前向可達接線 ⟹ **存在**其懸掛流，使到達性**恰等於**
通用機停機。 -/
theorem suspension_trigger_characterization {X : Type} [TopologicalSpace X] [CompactSpace X]
    (e : X ≃ₜ X) (H : Set X) (init : Nat.Partrec.Code → X)
    (hH : ∀ code, init code ∈ H → e (init code) ∈ H) (n : ℕ)
    (huniv : ∀ code, (∃ k : ℕ, (⇑e)^[k + 1] (init code) ∈ H) ↔ (code.eval n).Dom) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M) (F : ContinuousFlowOn M)
      (enc : X → M),
      ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code)) ∈ enc '' H) ↔ (code.eval n).Dom := by
  obtain ⟨M, tM, cM, F, enc, hsim, hfaith⟩ := suspension_flow_simulates_faithful e
  exact ⟨M, tM, cM, F, enc, coupled_blowup_characterization hsim hfaith H init hH n huniv⟩

open BitTM in
/-- **bennett 層特徵化**：任意位元機 `M`（機器級停機對應 + 停機集 bennett-封閉）⟹ 其 Bennett
可逆化懸掛流的到達性**恰等於**通用機停機。（huniv 由 `bennettAut_iterate` 從機器層證出，同
`bitTM_bennett_blowup_undecidable`。） -/
theorem bitTM_bennett_characterization (M : BitTM)
    (Hcfg : Set M.Cfg) (init : Nat.Partrec.Code → M.Cfg) (n : ℕ)
    (hHclosed : ∀ code, init code ∈ Hcfg → M.step (init code) ∈ Hcfg)
    (hmachine : ∀ code, (∃ k : ℕ, M.step^[k + 1] (init code) ∈ Hcfg) ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (_ : CompactSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : (M.Cfg × (ℤ → M.HistRec)) → Mt),
      ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code, M.blankHist))
          ∈ enc '' {p | p.1 ∈ Hcfg}) ↔ (code.eval n).Dom := by
  have hfst : ∀ (c : M.Cfg) (k : ℕ),
      ((⇑M.bennettHomeo)^[k] (c, M.blankHist)).1 = M.step^[k] c := by
    intro c k
    simp only [M.coe_bennettHomeo]
    obtain ⟨η, heq, _⟩ := M.bennettAut_iterate c k
    exact congrArg Prod.fst heq
  have hH : ∀ code,
      (init code, M.blankHist) ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg} →
      M.bennettHomeo (init code, M.blankHist) ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg} := by
    intro code hmem
    simp only [Set.mem_setOf_eq] at hmem ⊢
    have h1 : (M.bennettHomeo (init code, M.blankHist)).1 = M.step (init code) := by
      simpa using hfst (init code) 1
    rw [h1]; exact hHclosed code hmem
  have huniv : ∀ code,
      (∃ k : ℕ, (⇑M.bennettHomeo)^[k + 1] (init code, M.blankHist)
        ∈ {p : M.Cfg × (ℤ → M.HistRec) | p.1 ∈ Hcfg}) ↔ (code.eval n).Dom := by
    intro code
    rw [← hmachine code]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa only [Set.mem_setOf_eq, hfst (init code) (k + 1)] using hk⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only [Set.mem_setOf_eq, hfst (init code) (k + 1)]; exact hk
  exact suspension_trigger_characterization M.bennettHomeo
    {p | p.1 ∈ Hcfg} (fun code ↦ (init code, M.blankHist)) hH n huniv

/-- **M_tr 流層特徵化**：TM0-Bool 機器 `M`（`hcorr`：eval 停機 ⟺ code.eval）⟹ 其 M_tr Bennett
可逆化懸掛流到達性**恰等於** `code.eval n` 停機。 -/
theorem mtr_flow_characterization {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ)
    (hClosed : ∀ {q : Λ} {a : Bool} {q' : Λ} {s : Turing.TM0.Stmt Bool},
        (q', s) ∈ M q a → q ∈ (↑S : Set Λ) → q' ∈ (↑S : Set Λ))
    (init : Nat.Partrec.Code → Turing.TM0.Cfg Bool Λ) (n : ℕ)
    (hinit_q : ∀ code, (init code).q ∈ S)
    (hcorr : ∀ code, (StateTransition.eval (Turing.TM0.step M) (init code)).Dom
        ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (_ : CompactSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : ((Mtr M S).Cfg × (ℤ → (Mtr M S).HistRec)) → Mt),
      ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (encTM0 M S (init code), (Mtr M S).blankHist))
          ∈ enc '' {p | p.1 ∈ {c : (Mtr M S).Cfg | c.1 = encHalt S}}) ↔ (code.eval n).Dom := by
  refine bitTM_bennett_characterization (Mtr M S) {c : (Mtr M S).Cfg | c.1 = encHalt S}
    (fun code ↦ encTM0 M S (init code)) n ?_ ?_
  · intro code hmem
    exact Mtr_step_fst_halt M S _ hmem
  · intro code
    simp only [Set.mem_setOf_eq]
    rw [Mtr_halts_iff M S hClosed (init code) (hinit_q code), hcorr code]

/-! ## 特徵化封頂 + 統一推論 -/

/-- **★到達性特徵化封頂（reduction 顯式）★**：存在緊空間連續時間流 `F`、基點族 `base`、
目標集 `Target`，使 code 的軌道到達性**恰等於**停機問題：

> `∀ code, (∃ t > 0, F.φ t (base code) ∈ Target) ⟺ (code.eval n).Dom`

比 `fluid_blowup_undecidable` 強：不只「不可判定」，而是**精確歸約到停機問題**（多一多的還原）。
不可判定、r.e.、全域封閉不可判定皆由此單一 iff 導出。 -/
theorem fluid_reach_characterization (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (F : ContinuousFlowOn X)
      (base : Nat.Partrec.Code → X) (Target : Set X),
      ∀ code : Nat.Partrec.Code,
        (∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target) ↔ (code.eval n).Dom := by
  have hf : Partrec fun m : ℕ ↦
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const n)
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  obtain ⟨N, enc, dec, enc0, encdec⟩ :=
    tm1to1_enc (Turing.TM2to1.Γ' K' (fun _ ↦ Γ'))
  classical
  set M1 := Turing.TM2to1.tr tr with hM1
  set M2 := Turing.TM1to1.tr enc dec M1 with hM2
  set S0 : Finset Λ' := codeSupp cu Cont'.halt with hS0def
  set S1 := Turing.TM2to1.trSupp tr S0 with hS1def
  set S2 := Turing.TM1to1.trSupp M1 S1 with hS2def
  set SU := Turing.TM1to0.trStmts M2 S2 with hSUdef
  have hClosed : ∀ {q : Turing.TM1to0.Λ' M2} {a : Bool} {q' : Turing.TM1to0.Λ' M2}
      {s : Turing.TM0.Stmt Bool}, (q', s) ∈ Muniv enc dec q a →
      q ∈ (↑SU : Set (Turing.TM1to0.Λ' M2)) → q' ∈ (↑SU : Set (Turing.TM1to0.Λ' M2)) := by
    letI : Inhabited Λ' := ⟨trNormal cu Cont'.halt⟩
    intro q a q' s h hq
    exact (tm1to0_supports M2 (tm1to1_supports M1 enc dec
      (Turing.TM2to1.tr_supports (M := tr)
        (Turing.PartrecToTM2.tr_supports cu Cont'.halt)))).2 h hq
  have hInS0 : trNormal cu Cont'.halt ∈ S0 := trNormal_mem_trLabels cu
  have hInS1 : Turing.TM2to1.Λ'.normal (trNormal cu Cont'.halt) ∈ S1 :=
    Finset.mem_biUnion.2 ⟨_, hInS0, Finset.mem_insert_self _ _⟩
  have hInS2 : Turing.TM1to1.Λ'.normal (Turing.TM2to1.Λ'.normal (trNormal cu Cont'.halt)) ∈ S2 :=
    Finset.mem_biUnion.2 ⟨_, hInS1, Finset.mem_insert_self _ _⟩
  have hinit_q : ∀ code : Nat.Partrec.Code,
      (univTM0Cfg enc dec enc0 cu [Encodable.encode code]).q ∈ SU := by
    intro code
    refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
    exact Finset.some_mem_insertNone.2
      (Finset.mem_biUnion.2 ⟨_, hInS2, Turing.TM1.stmts₁_self⟩)
  have hcorr : ∀ code : Nat.Partrec.Code,
      (StateTransition.eval (Turing.TM0.step (Muniv enc dec))
        (univTM0Cfg enc dec enc0 cu [Encodable.encode code])).Dom ↔ (code.eval n).Dom := by
    intro code
    rw [univ_eval_chain enc dec encdec enc0 cu [Encodable.encode code]]
    have hv := hcu (Encodable.encode code ::ᵥ List.Vector.nil)
    simp only [List.Vector.head_cons, Denumerable.ofNat_encode] at hv
    have hv' : cu.eval [Encodable.encode code] = pure <$> code.eval n := hv
    rw [hv']
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
      obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
      exact Part.dom_iff_mem.mpr ⟨a, ha⟩
    · intro h
      exact Part.dom_iff_mem.mpr ⟨pure ((code.eval n).get h), Part.mem_map _ (Part.get_mem h)⟩
  obtain ⟨Mt, tMt, cMt, F, enc', hiff⟩ :=
    mtr_flow_characterization (Muniv enc dec) SU hClosed
      (fun code ↦ univTM0Cfg enc dec enc0 cu [Encodable.encode code]) n hinit_q hcorr
  exact ⟨Mt, tMt, cMt, F,
    fun code ↦ enc' (encTM0 (Muniv enc dec) SU
      (univTM0Cfg enc dec enc0 cu [Encodable.encode code]), (Mtr (Muniv enc dec) SU).blankHist),
    enc' '' {p | p.1 ∈ {c | c.1 = encHalt SU}}, hiff⟩

/-- **★流到達性的完整計算複雜度定位（單一流、四合一）★**：存在**同一個**緊空間流 `F`、基點
`base`、目標 `Target`，其到達謂詞同時滿足——

1. **精確歸約**：`∀ code, 到達 ⟺ (code.eval n).Dom`（= 停機問題，多一還原）；
2. **不可判定**：`¬ComputablePred 到達`（`ComputablePred.halting_problem`）；
3. **r.e./半可判定（Σ₁）**：`REPred 到達`（`ComputablePred.halting_problem_re`）——有部分程序半判定；
4. **全域封閉亦不可判定**：`¬ComputablePred (¬到達)`（補集封閉）。

⟹ 這條流的到達性**精確坐落在 Σ₁ \ Δ₁**（r.e. 但不遞迴），與停機問題**同級**——不只「難以判定」，
是「恰好是停機問題」。全由 `fluid_reach_characterization` 的單一 iff 導出。 -/
theorem fluid_reach_full_characterization (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (F : ContinuousFlowOn X)
      (base : Nat.Partrec.Code → X) (Target : Set X),
      (∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target) ↔ (code.eval n).Dom)
      ∧ ¬ ComputablePred (fun code : Nat.Partrec.Code =>
            ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target)
      ∧ REPred (fun code : Nat.Partrec.Code =>
            ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target)
      ∧ ¬ ComputablePred (fun code : Nat.Partrec.Code =>
            ¬ ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target) := by
  obtain ⟨X, tX, cX, F, base, Target, hiff⟩ := fluid_reach_characterization n
  have heq : (fun code : Nat.Partrec.Code => ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target)
      = (fun code => (code.eval n).Dom) := funext fun code ↦ propext (hiff code)
  refine ⟨X, tX, cX, F, base, Target, hiff, ?_, ?_, ?_⟩
  · rw [heq]; exact ComputablePred.halting_problem n
  · rw [heq]; exact ComputablePred.halting_problem_re n
  · intro hcomp
    exact ComputablePred.halting_problem n (heq ▸ hcomp.not.of_eq (fun _ ↦ not_not))

end FluidTuring
