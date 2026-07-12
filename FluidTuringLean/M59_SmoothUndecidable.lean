import FluidTuringLean.M58_SmoothStep3
import FluidTuringLean.M33_FluidCapstone

/-!
# Module 59 — G6 封頂：顯式 C^∞ **映射**的軌道可達性不可判定（★GPAC 線里程碑★）

**承 M57（`gStepRL3` = `BitTM` 一步）+ M58（`sigmaRL3` = `gStepRL3` 步對步、C^∞）+ M28
（`Mtr_halts_iff`、機器停機橋，無條件）+ M33（通用碼組裝 block，直接複用）**。本磚把整條 GPAC 鏈
焊到 mathlib 停機問題，得**第一個關於「顯式光滑映射」的不可判定結果**：

> **存在一個顯式 C^∞ 映射 `σ : ℝ³ → ℝ³`，其軌道可達性（∃k，σ^[k](base code) ∈ Target）不可計算。**

這與主線 M33（連續**流**、無條件）是**不同的數學物件**（離散**映射** vs 連續**流**），皆源自同一
`Mtr_halts_iff` 機器層 + mathlib `ComputablePred.halting_problem`，**不冗餘、非取代**。

## 鏈條（全機器背書、零 sorry、標準三公理）

```
mathlib halting_problem  ──(M33 block: cu/enc/SU/hcorr)──→  TM0(Bool) 停機
   ↑                                                            │ Mtr_halts_iff (M28)
   │ ComputablePred                                    (Mtr M S).step^[k] 到 encHalt
   │                                                            │ bitStep_iterate (本磚)
顯式 C^∞ σ 軌道可達 Target  ←(reach_at_k 本磚)─  bitStepTape^[k] 到 vhalt
   ↑ sigmaRL3_iterate_exactB (M58)                              │ gStepRL3_iterate_tape (本磚)
   └───────────────────  gStepRL3^[k]（離散玩具步）──────────────┘  gStepRL3_simulates_BitTM (M57)
```

## 交付

- **帶橋** `bitStepTape`/`encPair`/`bitStep_commute`/`bitStep_iterate`（`BitTM.step` 在 `Tape`-編碼
  組態上 = `Tape`-層步的編碼；M25 `tapeStep_nth` 抬到 N 步）。
- `gStepRL3_iterate_tape`（M57 單步橋抬到 N 步、`Tape`-層）。
- **`reach_at_k`（★核心 iff★）**：`(σ^[k](gEncB(bitEnc v T))).1 = bitVecToNat(vhalt) ↔
  ((BitTM.step)^[k](encPair(v,T))).1 = vhalt`（M58 iterate + 兩 `Tape` iterate + `Nat.cast_inj` +
  `bitVecToNat` 單射）。
- `wfCfgB_bitEnc`/`hQ_bitEnc`/`hW_bitEnc`（Bool 字母 k=2、K=8、狀態 <2^m、寫符 <2——wf 前提對
  `bitEnc` 全免費）。
- **`sigmaM_reach_undecidable_of`（★機器參數化 headline★）**：任意 TM0 機器 + 封閉性 + 停機對應
  `hcorr` ⟹ `∃ σ C^∞, ¬ComputablePred(軌道可達 Target)`（`reach_at_k` + `offset` + `Mtr_halts_iff`
  + `hcorr` + `funext`/`propext` + `halting_problem`）。
- **`sigmaRL3_reachability_undecidable`（★封頂★）**：複用 M33 的通用碼 block（cu/enc/SU/hClosed/
  hinit_q/hcorr 逐字），落地**無條件**「存在顯式 C^∞ 映射軌道可達性不可判定」。

## ★誠實範圍（禁 overclaim）★

- **是離散映射、非連續流**：`σ` 是裸 ℝ³ 自映射 + `Function.iterate`（不需緊空間/懸掛流機器）；
  連續 ODE 流版本 = **已證死牆**（`M56_G5Wall.lean`、`K>1` 讀增益）。**不宣稱**連續流。
- **C^∞ 非 analytic**（承 M46-M58）；`σ` 由 `smoothTransition` 組。若要求嚴格 GPAC(analytic)，
  exact-on-lattice 不可能（承既有語意分歧記錄）。
- **可達性版本**：斷言 = `∃k, σ^[k](base) ∈ Target`（打進編碼停機區），非字面 halting-state 唯一性
  之外的更強性質。玩具編碼（Bool 字母、`Fin m→Bool` 狀態經 `bitVecToNat`）。
- **與 M33 關係**：不同數學物件（映射 vs 流），共用機器層，**平行**不取代；本磚**不**弱化亦不
  強化 M33。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2 Nat.Partrec

/-! ## `BitTM.step` ↔ `Tape`-層步 的橋（`ℤ→Bool` 移動帶 = `Tape Bool` 的 `nth` 視圖） -/

/-- `Tape`-層一步（停留在 `Tape Bool`-形狀，不像 `BitTM.step` 落到 `ℤ→Bool`）。 -/
def bitStepTape (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) : (Fin M.m → Bool) × Tape Bool :=
  (M.next p.1 p.2.head, tapeStep (M.write p.1 p.2.head) (M.move p.1 p.2.head) p.2)

/-- 把 `Tape`-形狀 pair 編成真 `BitTM.Cfg`（帶 = `Tape.nth`）。 -/
def encPair (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) : M.Cfg := (p.1, fun n => p.2.nth n)

/-- **★`BitTM.step` 在編碼組態上 = `Tape`-層步的編碼★**（`step_eval` + M25 `tapeStep_nth` + `funext`）。 -/
theorem bitStep_commute (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) :
    M.step (encPair M p) = encPair M (bitStepTape M p) := by
  rw [encPair, BitTM.step_eval]
  have hh : (fun n => p.2.nth n) (0 : ℤ) = p.2.head := tape_head_nth p.2
  simp only [hh]
  refine Prod.ext rfl ?_
  funext n
  rw [encPair, bitStepTape]
  simp only
  rw [tapeStep_nth]

/-- N 步版本。 -/
theorem bitStep_iterate (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) (k : ℕ) :
    (M.step)^[k] (encPair M p) = encPair M ((bitStepTape M)^[k] p) := by
  induction k generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih (bitStepTape M p),
      bitStep_commute]

/-- M57 單步橋（`Tape`-層改寫）。 -/
theorem gStepRL3_step_tape (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) :
    gStepRL3 (δqOf M) (δwOf M) (moveOf M) (bitEnc p.1 p.2)
      = bitEnc (bitStepTape M p).1 (bitStepTape M p).2 :=
  gStepRL3_simulates_BitTM M p.1 p.2

/-- M57 橋抬到 N 步（`Tape`-層）。 -/
theorem gStepRL3_iterate_tape (M : BitTM) (p : (Fin M.m → Bool) × Tape Bool) (k : ℕ) :
    (gStepRL3 (δqOf M) (δwOf M) (moveOf M))^[k] (bitEnc p.1 p.2)
      = bitEnc ((bitStepTape M)^[k] p).1 ((bitStepTape M)^[k] p).2 := by
  induction k generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, gStepRL3_step_tape, ih]

/-! ## wf 前提對 `bitEnc` 全免費（Bool 字母 k=2、K=8） -/

theorem wfCfgB_bitEnc (M : BitTM) (v : Fin M.m → Bool) (T : Tape Bool) :
    wfCfgB (2 ^ M.m) 2 (bitEnc v T) :=
  ⟨bitVecToNat_lt M.m v, digitsLtB_two_map T.left, digitsLtB_two_map (T.right.cons T.head)⟩

theorem hQ_bitEnc (M : BitTM) : ∀ q s, q < 2 ^ M.m → s < 2 → δqOf M q s < 2 ^ M.m :=
  fun _ _ _ _ => bitVecToNat_lt M.m _

theorem hW_bitEnc (M : BitTM) : ∀ q s, q < 2 ^ M.m → s < 2 → δwOf M q s < 2 := by
  intro q s _ _
  unfold δwOf boolToNatPM
  simp only
  split <;> norm_num

/-- 機器 `M` 的具體 C^∞ σ（`K=8`、`k=2`、`w=1/4`；headroom `1/7 ≤ 1/4`）。 -/
noncomputable def sigmaM (M : BitTM) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  sigmaRL3 (fun a b => (δqOf M a b : ℝ)) (fun a b => (δwOf M a b : ℝ))
    (fun a b => (dirNat (moveOf M a b) : ℝ)) (2 ^ M.m) 8 (1 / 4)

theorem sigmaM_contDiff (M : BitTM) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaM M) :=
  sigmaRL3_contDiff _ _ _ _ _ _

/-! ## ★核心 iff：σ 軌道到達 = `BitTM` 到達 halt 狀態 -/

/-- **★per-step 到達等價★**：`(σ^[k](gEncB(bitEnc v T))).1 = bitVecToNat vhalt ↔
`((BitTM.step)^[k](encPair(v,T))).1 = vhalt`（M58 iterate + `Tape` iterate + `Nat.cast_inj` +
`bitVecToNat` 單射）。 -/
theorem reach_at_k (M : BitTM) (v vhalt : Fin M.m → Bool) (T : Tape Bool) (k : ℕ) :
    ((sigmaM M)^[k] (gEncB 8 (bitEnc v T))).1 = (bitVecToNat M.m vhalt : ℝ)
      ↔ ((M.step)^[k] (encPair M (v, T))).1 = vhalt := by
  have hstep : (sigmaM M)^[k] (gEncB 8 (bitEnc v T))
      = gEncB 8 ((gStepRL3 (δqOf M) (δwOf M) (moveOf M))^[k] (bitEnc v T)) := by
    rw [sigmaM]
    exact sigmaRL3_iterate_exactB (δqOf M) (δwOf M) (moveOf M) (2 ^ M.m) 2 8
      (by norm_num) (by norm_num) (by norm_num) (hQ_bitEnc M) (hW_bitEnc M)
      (by norm_num) (by norm_num) (by norm_num) (bitEnc v T) (wfCfgB_bitEnc M v T) k
  rw [hstep, gStepRL3_iterate_tape M (v, T) k, bitStep_iterate M (v, T) k]
  change (bitVecToNat M.m ((bitStepTape M)^[k] (v, T)).1 : ℝ) = (bitVecToNat M.m vhalt : ℝ)
    ↔ ((bitStepTape M)^[k] (v, T)).1 = vhalt
  rw [Nat.cast_inj]
  exact (bitVecToNat_injective M.m).eq_iff

/-- `∃k, P k ↔ ∃k, P (k+1)`（`P 0` 假；把 `Mtr_halts_iff` 的 `k+1` 對齊到 `reach_at_k` 的 `k`）。 -/
theorem offset_exists {P : ℕ → Prop} (h0 : ¬ P 0) : (∃ k, P k) ↔ (∃ k, P (k + 1)) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk h0
    | succ m => exact ⟨m, hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k + 1, hk⟩

/-! ## ★機器參數化 headline★：TM0 + 封閉性 + `hcorr` ⟹ σ 可達性不可判定 -/

/-- **★機器參數化不可判定★**：任意 TM0(Bool) 機器 `M0` + 封閉性 `hClosed` + 停機對應 `hcorr`
（`init code` 的 TM0-eval 停機 ⟺ `code.eval n` 停機）⟹ **存在顯式 C^∞ 映射 `σ`，其軌道可達性
不可計算**。橋：`reach_at_k`（σ↔BitTM 到達）+ `offset_exists` + `Mtr_halts_iff`（M28）+ `hcorr` +
`funext`/`propext` + `ComputablePred.halting_problem`。 -/
theorem sigmaM_reach_undecidable_of {Λ : Type*} [Inhabited Λ]
    (M0 : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    (hClosed : ∀ {q : Λ} {a : Bool} {q' : Λ} {s : Turing.TM0.Stmt Bool},
        (q', s) ∈ M0 q a → q ∈ (↑S : Set Λ) → q' ∈ (↑S : Set Λ))
    (init : Nat.Partrec.Code → Turing.TM0.Cfg Bool Λ) (n : ℕ)
    (hinit_q : ∀ code, (init code).q ∈ S)
    (hcorr : ∀ code, (StateTransition.eval (Turing.TM0.step M0) (init code)).Dom
        ↔ (code.eval n).Dom) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : Nat.Partrec.Code → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ¬ ComputablePred (fun code : Nat.Partrec.Code => ∃ k : ℕ, σ^[k] (base code) ∈ Target) := by
  refine ⟨sigmaM (Mtr M0 S), sigmaM_contDiff _,
    fun code => gEncB 8 (bitEnc (encCtrl S (ctrlOfLabel S (init code).q)) (init code).Tape),
    {x | x.1 = (bitVecToNat (ctrlCard S) (encHalt S) : ℝ)}, ?_⟩
  intro hcomp
  have key : (fun code : Nat.Partrec.Code => ∃ k : ℕ, (sigmaM (Mtr M0 S))^[k]
        (gEncB 8 (bitEnc (encCtrl S (ctrlOfLabel S (init code).q)) (init code).Tape))
          ∈ {x | x.1 = (bitVecToNat (ctrlCard S) (encHalt S) : ℝ)})
      = fun code => (code.eval n).Dom := by
    funext code
    apply propext
    have step1 : (∃ k : ℕ, (sigmaM (Mtr M0 S))^[k]
          (gEncB 8 (bitEnc (encCtrl S (ctrlOfLabel S (init code).q)) (init code).Tape))
            ∈ {x | x.1 = (bitVecToNat (ctrlCard S) (encHalt S) : ℝ)})
        ↔ ∃ k : ℕ, ((Mtr M0 S).step^[k] (encTM0 M0 S (init code))).1 = encHalt S := by
      apply exists_congr
      intro k
      rw [Set.mem_setOf_eq]
      exact reach_at_k (Mtr M0 S) (encCtrl S (ctrlOfLabel S (init code).q)) (encHalt S)
        (init code).Tape k
    rw [step1]
    have h0 : ¬ ((Mtr M0 S).step^[0] (encTM0 M0 S (init code))).1 = encHalt S := by
      simp only [Function.iterate_zero, id]
      exact encTM0_fst_ne_encHalt M0 S (hinit_q code)
    rw [offset_exists h0, Mtr_halts_iff M0 S hClosed (init code) (hinit_q code), hcorr code]
  rw [key] at hcomp
  exact ComputablePred.halting_problem n hcomp

/-! ## ★封頂：無條件「顯式 C^∞ 映射軌道可達性不可判定」 -/

/-- **★★G6 封頂（無條件）★★**：存在一個**顯式 C^∞ 映射** `σ : ℝ³ → ℝ³`、基點族 `base`、目標集
`Target`，使「`code` 的軌道於某步打進 `Target`」**無演算法可判定**。通用碼組裝 block（`cu`/`enc`/`SU`/
`hClosed`/`hinit_q`/`hcorr`）**逐字複用 M33**，尾端接 `sigmaM_reach_undecidable_of`（離散映射版、
非 M33 的懸掛流版）。

**與主線 M33 的關係**：不同數學物件（**離散映射** vs **連續流**）、共用機器層、平行不取代。
C^∞ 非 analytic；離散映射非連續流（連續流升級 = 死牆 M56）。 -/
theorem sigmaRL3_reachability_undecidable (n : ℕ) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : Nat.Partrec.Code → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ¬ ComputablePred (fun code : Nat.Partrec.Code => ∃ k : ℕ, σ^[k] (base code) ∈ Target) := by
  -- 暴露通用 code cu（複用 M33）
  have hf : Partrec fun m : ℕ ↦
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const n)
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  -- 位元編碼
  obtain ⟨N, enc, dec, enc0, encdec⟩ :=
    tm1to1_enc (Turing.TM2to1.Γ' K' (fun _ ↦ Γ'))
  classical
  -- 機器 + supports 鏈
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
  -- 接離散映射版 headline（非 M33 的懸掛流）
  exact sigmaM_reach_undecidable_of (Muniv enc dec) SU hClosed
    (fun code ↦ univTM0Cfg enc dec enc0 cu [Encodable.encode code]) n hinit_q hcorr

end FluidTuring
