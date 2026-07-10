import FluidTuringLean.M32_EvalChain

/-!
# Module 33 — 流體端 blowup 不可判定（無條件）★專案封頂★（M_tr 本體 4b-5b-B4）

B4：把化約鏈（M30-M32）+ supports threading 焊死，兌現 M29 `mtr_flow_blowup_undecidable` 的
`hcorr`，得**無條件**的最終定理：存在一個緊空間上的連續時間流，其（由 code 索引的）
**到達謂詞**（∃ 正時間打進編碼停機區 `Target`）**不可計算**。

**★誠實範圍（審計後校正 2026-07-10）★**：本定理**實際證的**是「緊空間懸掛流的**到達性
（reachability）不可判定」——`∃ t>0, F.φ t (base code) ∈ Target`。**這是「blowup 觸發」的
*到達性版本*、不是字面的有限時間爆破**：懸掛流在緊空間上，座標不可能真的跑到無窮（緊性），
故此處**無**字面 blowup。字面的 Riccati `z'=z²` 有限時間爆破**另證於 M11-M13**（`blowupSol` /
`halts_imp_smooth_blowup`，且**僅正向** `停機 ⟹ 爆破`、於非自治混成系統），**並未**組進本鏈
（M14/M20/M29/M33 不含 M12/M13）。「blowup」在此是把「到達編碼停機區」**詮釋**為觸發（經 M12/M13
的正向橋），非本定理直接斷言的爆破。

= 全專案「特定流的圖靈完備性 ⟹ 到達性（blowup 觸發）不可判定」核心目標的無條件達成
（離散/拓撲流端全鏈機器背書、零 sorry、標準三公理）。真微分幾何/真 Euler/NS 幾何流、以及把 M12/M13
字面爆破組進緊空間流，仍是外部 paper-blocked、明寫範圍。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2 Nat.Partrec

/-- **★流體端到達性（blowup 觸發）不可判定（無條件）★**：存在緊空間連續時間流 `F`、基點族
`base`、目標集 `Target`，使「code 的軌道於**某正時間**打進 `Target`」（= 懸掛流到達編碼停機區
= blowup **觸發**的到達性版本）**無演算法可判定**。

**注意**：實際斷言 = **到達性**（緊空間上無字面爆破）；字面 Riccati 有限時間爆破另證於 M11-M13
（僅正向、未組進本鏈）。詳見檔頭誠實範圍。

證明鏈：mathlib `halting_problem`（M16 via M30）→ 化約鏈 `TM2→TM1→TM1(Bool)→TM0(Bool)`
（M31/M32）→ 我們 `BitTM` `M_tr`（M27，一步模擬 + 停機橋 M28）→ Bennett 可逆化（M3c）→ 懸掛流
（M4/M14）→ 到達性不可判定（M10 `finite_time_blowup_undecidable` 的到達性實例）。 -/
theorem fluid_blowup_undecidable (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (F : ContinuousFlowOn X)
      (base : Nat.Partrec.Code → X) (Target : Set X),
      ¬ ComputablePred (fun code : Nat.Partrec.Code =>
          ∃ t : ℝ, 0 < t ∧ F.φ t (base code) ∈ Target) := by
  -- 暴露通用 code cu
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
  -- supports 封閉性：supports 鏈用 PartrecToTM2 的自訂 Inhabited（default = trNormal cu halt ∈
  -- codeSupp），letI 限縮在本證內；封閉性 .2 型別與 Inhabited 無關，故橋接回標準 Muniv/SU。
  have hClosed : ∀ {q : Turing.TM1to0.Λ' M2} {a : Bool} {q' : Turing.TM1to0.Λ' M2}
      {s : Turing.TM0.Stmt Bool}, (q', s) ∈ Muniv enc dec q a →
      q ∈ (↑SU : Set (Turing.TM1to0.Λ' M2)) → q' ∈ (↑SU : Set (Turing.TM1to0.Λ' M2)) := by
    letI : Inhabited Λ' := ⟨trNormal cu Cont'.halt⟩
    intro q a q' s h hq
    exact (tm1to0_supports M2 (tm1to1_supports M1 enc dec
      (Turing.TM2to1.tr_supports (M := tr)
        (Turing.PartrecToTM2.tr_supports cu Cont'.halt)))).2 h hq
  -- init 標籤 ∈ SU（3 段穿線）
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
  -- hcorr：reduced TM0-Bool eval 停機 ⟺ code.eval
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
  -- 接 M_tr 流層 → 最終定理
  obtain ⟨Mt, tMt, cMt, F, enc', _, hundec⟩ :=
    mtr_flow_blowup_undecidable (Muniv enc dec) SU hClosed
      (fun code ↦ univTM0Cfg enc dec enc0 cu [Encodable.encode code]) n hinit_q hcorr
  exact ⟨Mt, tMt, cMt, F,
    fun code ↦ enc' (encTM0 (Muniv enc dec) SU
      (univTM0Cfg enc dec enc0 cu [Encodable.encode code]), (Mtr (Muniv enc dec) SU).blankHist),
    enc' '' {p | p.1 ∈ {c | c.1 = encHalt SU}}, hundec⟩

end FluidTuring
