import FluidTuringLean.M62_DecideDrill
import Mathlib.Computability.RE

/-!
# Module 64 — 半可判定謂詞的通用閘門，與它的質數實例（「質數電腦」誠實版）

**承 M59（`sigmaM_reach_iff_of` 結構閘門、通用機組裝 block）+ M62（`reach_at_k_tape`）**。
起因＝使用者問「流體電腦能不能變質數電腦」；稽核裁 NO-GO（`docs/PRIME_COMPUTER_AUDIT_2026-09-20.md`），
使用者於 2026-09-21 拍板實作。實作過程暴露：證明裡與質數有關的只有一行，其餘全是通用零件——
所以本模組真正交付的是**通用閘門**，質數只是它的一個（零內容的）實例。

> **`rePred_computer_uniform`（★核心★）**：對任何半可判定 `p : ℕ → Prop`，存在一台固定 `BitTM`、固定
> 起始字 `v₀`、固定停機字 `vhalt`、與只依賴 `n` 的帶子 `tape n`，使得對所有 `n`：機器從 `(v₀, tape n)`
> 有限步到 `vhalt` ⟺ `p n`；同一組資料經 `sigmaM M` 給出光滑映射版（`sigma_reach_of_rePred`）。
>
> **規則**：填可判定的 `p` → 零可計算性內容；填不可判定的 `p`（停機、Collatz 實例、Goldbach 反例存在）→
> 才有內容。M59 capstone 是前者以外的實例；下方的質數電腦是前者。

> **質數實例**：`prime_computer_uniform` = 閘門填入 `Nat.Prime`；
> `primeSigma_reach_iff`：`(∃ k, primeSigma^[k] (primeBase n) ∈ primeTarget) ↔ Nat.Prime n`，
> 其中 `primeSigma`、`primeTarget` 是與 `n` 無關的常數，`n` 在陳述裡只出現一次。

## 交付（零 sorry、標準三公理）

- `primrecPred_nat_prime`：**`Nat.Prime` 是原始遞迴謂詞**（mathlib 此 pin 缺；獨立可上游，= 稽核 B4）。
- `rePart` / `partrec_rePart` / `rePart_dom`：半可判定謂詞 → 定義域恰為它的部分函數。
- `rePred_computer_uniform`（★核心閘門★）、`sigma_reach_of_rePred`（∃ 版）。
- 質數實例：`prime_computer_uniform`、`sigmaRL3_prime_computer`、`primeSigma_reach_iff`（具名常數版）、
  `primeSigma_not_reach_of_not_prime` 等推論。

## ★誠實範圍（禁 overclaim）★

1. **本模組不產生任何可計算性內容。** `Nat.Prime` 可判定（`Nat.decidablePrime`），
   `∃ k, σ^[k](base n) ∈ Target` 經 `reach_at_k` 恰等價於它——兩邊都在 Δ₁。
   證明 = `sigmaM_reach_iff_of`（M59）的**全稱實例化** + 通用機組裝（逐字複用 M59 capstone 的 block，
   只把「通用碼」換成「質數程式」）。質性內容全部經 `Nat.prime_def_lt'` **流進來**，沒有一滴流出去。
   **這是一個 characterization，不是不可判定性結果，也不是關於質數的新知識。**
2. **單邊。** 只有「到達 ⟺ 質數」：合數（與 `0`、`1`）的軌道**永不**到達 `Target`，
   本模組**沒有**第二個「合數區」、**永遠吐不出因數**。原因是 `Mtr`（M27）把所有 TM0 停機塌成單一字
   `encHalt`；兩區版本要走 M37 `bitTM_bennett_characterization` 的 `Hcfg` 路線，本模組未做。
3. **一步也跑不動。** `sigmaM` 與其編碼器（`bitVecToNat`、`bitEnc`）皆 `noncomputable`（M59 §誠實範圍）；
   而且通用機層的 `enc`/`dec` 來自 `tm1to1_enc` 的存在量詞，**連離散側都不能 `decide`**——
   與 M62 的 `readTM` 演習不同，這台機器沒有可點火的具體實例。
4. **不是流體、不是流。** `sigmaM` 是 ℝ³ 上的離散自映射；`README.md`「not claims about real Navier–Stokes」
   原封適用。C^∞ 非 analytic（`sfloor_not_analytic`，M60）。
5. **反循環靠陳述形狀，不靠 kernel。** `#print axioms` 對「先查 `Nat.Prime n` 再挑起點」的假橋是瞎的
   （`Nat.decidablePrime` 可算，假橋也只會顯示標準三公理）。真正的保證是 `prime_computer_uniform` 的**形狀**：
   `M`、`v₀`、`vhalt` 全綁在 `∀ n` 之外，`n` 只出現在 `tape n`；而 `tape n` 在證明裡是
   `(univTM0Cfg enc dec enc0 cu [n]).Tape`——固定機器在輸入 `[n]` 上的初始帶，對 `n` 一致、無 case split。
   讀者檢查簽名即可，不需信任本段散文。
6. **價值定位**：稽核裁定此類型為既有通用定理的第六片終端葉子（零下游消費者）。本模組的**唯一**獨立價值是
   副產品 `primrecPred_nat_prime`。
7. 本模組名稱**不得**被引為 headline。
-/

namespace FluidTuring

open Turing Turing.PartrecToTM2 Nat.Partrec

/-! ## 1. 質數判定是原始遞迴的（mathlib 缺這條） -/

/-- `Nat.Prime` 是原始遞迴謂詞：`2 ≤ n ∧ ∀ m < n, ¬ (2 ≤ m ∧ n % m = 0)`。 -/
theorem primrecPred_nat_prime : PrimrecPred Nat.Prime := by
  have hR : PrimrecRel fun m n : ℕ => 2 ≤ m ∧ n % m = 0 := by
    show PrimrecPred fun p : ℕ × ℕ => 2 ≤ p.1 ∧ p.2 % p.1 = 0
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.nat_le.comp (Primrec.const 2) Primrec.fst
    · exact Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)
  have h : PrimrecPred fun n : ℕ => 2 ≤ n ∧ ∀ m < n, ¬ (2 ≤ m ∧ n % m = 0) := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.nat_le.comp (Primrec.const 2) Primrec.id
    · exact (PrimrecRel.forall_lt hR.not).comp Primrec.id Primrec.id
  refine h.of_eq fun n => ?_
  rw [Nat.prime_def_lt']
  simp only [Nat.dvd_iff_mod_eq_zero, not_and]
  exact ⟨fun ⟨h2, hm⟩ => ⟨h2, fun m hm2 hmn => hm m hmn hm2⟩,
    fun ⟨h2, hm⟩ => ⟨h2, fun m hmn hm2 => hm m hm2 hmn⟩⟩

theorem computablePred_nat_prime : ComputablePred Nat.Prime := by
  obtain ⟨_, h⟩ := primrecPred_nat_prime
  exact ⟨_, h.to_comp⟩

theorem rePred_nat_prime : REPred Nat.Prime := computablePred_nat_prime.to_re

/-! ## 2. 半可判定謂詞 → 部分函數（定義域恰為 `p`）；質數是其中一個實例 -/

/-- 把半可判定謂詞 `p` 變成部分函數：`p n` 成立時回 `0`，否則不停機。 -/
def rePart (p : ℕ → Prop) : ℕ →. ℕ :=
  fun n => (Part.assert (p n) fun _ => Part.some ()).map fun _ => 0

theorem partrec_rePart {p : ℕ → Prop} (hp : REPred p) : Partrec (rePart p) :=
  hp.map (Computable.const 0).to₂

theorem rePart_dom (p : ℕ → Prop) (n : ℕ) : (rePart p n).Dom ↔ p n := by
  unfold rePart
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
    obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hy
    obtain ⟨hpn, -⟩ := Part.mem_assert_iff.mp ha
    exact hpn
  · intro hpn
    exact Part.dom_iff_mem.mpr
      ⟨0, (Part.mem_map_iff _).mpr ⟨(), Part.mem_assert_iff.mpr ⟨hpn, Part.mem_some ()⟩, rfl⟩⟩

/-- 質數程式 = `rePart Nat.Prime`。 -/
abbrev primePart : ℕ →. ℕ := rePart Nat.Prime

theorem partrec_primePart : Partrec primePart := partrec_rePart rePred_nat_prime

theorem primePart_dom (n : ℕ) : (primePart n).Dom ↔ Nat.Prime n := rePart_dom Nat.Prime n

/-! ## 3. ★通用閘門★：任何半可判定謂詞 → 一台固定機器／一個固定 σ 的軌道可達性 -/

/-- **★通用閘門（機器層、反循環可由陳述形狀檢查）★**：對**任何**半可判定謂詞 `p`，存在一台固定
`BitTM`、固定起始字、固定停機字，`n` 只寫進帶子，使得：從 `(v₀, tape n)` 有限步到 `vhalt` ⟺ `p n`；
且同一組資料經 `sigmaM M` 給出光滑映射版。

規則：填**可判定**的 `p`（如 `Nat.Prime`）得到零可計算性內容的 characterization；填**不可判定**的 `p`
（如停機、Collatz 實例、Goldbach 反例存在）才有內容。M59 的 capstone 與下方的質數電腦都是本定理的實例。 -/
theorem rePred_computer_uniform {p : ℕ → Prop} (hp : REPred p) :
    ∃ (M : BitTM) (v₀ vhalt : Fin M.m → Bool) (tape : ℕ → Tape Bool),
      (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape M)^[k] (v₀, tape n)).1 = vhalt) ↔ p n) ∧
      (∀ n : ℕ, (∃ k : ℕ, (sigmaM M)^[k] (gEncB 8 (bitEnc v₀ (tape n)))
          ∈ {x | x.1 = (bitVecToNat M.m vhalt : ℝ)}) ↔ p n) := by
  -- `p` 的程式編成 TM2 碼 cu
  obtain ⟨cu, hcu⟩ :=
    Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr (partrec_rePart hp))
  -- 位元編碼
  obtain ⟨N, enc, dec, enc0, encdec⟩ :=
    tm1to1_enc (Turing.TM2to1.Γ' K' (fun _ ↦ Γ'))
  classical
  -- 機器 + supports 鏈（與 M59 相同）
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
  have hinit_q : ∀ n : ℕ, (univTM0Cfg enc dec enc0 cu [n]).q ∈ SU := by
    intro n
    refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
    exact Finset.some_mem_insertNone.2
      (Finset.mem_biUnion.2 ⟨_, hInS2, Turing.TM1.stmts₁_self⟩)
  -- 停機 ⟺ p n（與 M59 唯一不同處：右端是 `p n`，不是 `(code.eval n).Dom`）
  have hcorr : ∀ n : ℕ,
      (StateTransition.eval (Turing.TM0.step (Muniv enc dec))
        (univTM0Cfg enc dec enc0 cu [n])).Dom ↔ p n := by
    intro n
    rw [univ_eval_chain enc dec encdec enc0 cu [n]]
    have hv := hcu (n ::ᵥ List.Vector.nil)
    simp only [List.Vector.head_cons] at hv
    have hv' : cu.eval [n] = pure <$> rePart p n := hv
    rw [hv', ← rePart_dom p n]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
      obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
      exact Part.dom_iff_mem.mpr ⟨a, ha⟩
    · intro h
      exact Part.dom_iff_mem.mpr ⟨pure ((rePart p n).get h), Part.mem_map _ (Part.get_mem h)⟩
  -- ★起始狀態字與 n 無關★：輸入只進帶子（`univTM0Cfg` 的 `.q` 由 trCfg 鏈決定，`rfl`）
  set q₀ := (univTM0Cfg enc dec enc0 cu []).q with hq₀
  have hq : ∀ n : ℕ, (univTM0Cfg enc dec enc0 cu [n]).q = q₀ := fun _ => rfl
  -- σ 版（逐 n）：結構閘門 sigmaM_reach_iff_of（M59）
  have hσ : ∀ n : ℕ, (∃ k : ℕ, (sigmaM (Mtr (Muniv enc dec) SU))^[k]
      (gEncB 8 (bitEnc (encCtrl SU (ctrlOfLabel SU q₀)) (univTM0Cfg enc dec enc0 cu [n]).Tape))
        ∈ {x | x.1 = (bitVecToNat (ctrlCard SU) (encHalt SU) : ℝ)}) ↔ p n := by
    intro n
    have h := (sigmaM_reach_iff_of (Muniv enc dec) SU hClosed _ (hinit_q n)).trans (hcorr n)
    rw [hq n] at h
    exact h
  refine ⟨Mtr (Muniv enc dec) SU, encCtrl SU (ctrlOfLabel SU q₀), encHalt SU,
    fun n ↦ (univTM0Cfg enc dec enc0 cu [n]).Tape, fun n ↦ ?_, hσ⟩
  -- 離散機器版：M62 的 `reach_at_k_tape` 把 σ 側逐 k 翻成 `bitStepTape` 側
  refine Iff.trans (exists_congr fun k ↦ ?_) (hσ n)
  rw [Set.mem_setOf_eq]
  exact (reach_at_k_tape _ _ _ _ k).symm

/-! ## 4. 推論：通用 ∃ 版、質數實例、具名常數版 -/

/-- **★通用閘門（∃ 版）★**：任何半可判定 `p`，存在固定 C^∞ `σ`、固定 `Target`、起點族 `base`，
`∀ n, 到達 ↔ p n`。 -/
theorem sigma_reach_of_rePred {p : ℕ → Prop} (hp : REPred p) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : ℕ → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ∀ n : ℕ, (∃ k : ℕ, σ^[k] (base n) ∈ Target) ↔ p n := by
  obtain ⟨M, v₀, vhalt, tape, -, hσ⟩ := rePred_computer_uniform hp
  exact ⟨sigmaM M, sigmaM_contDiff M, fun n ↦ gEncB 8 (bitEnc v₀ (tape n)),
    {x | x.1 = (bitVecToNat M.m vhalt : ℝ)}, hσ⟩

/-- **閘門的第一個非平凡消費者**：M59 capstone 的形狀（軌道可達 ⟺ 第 `m` 台機器在輸入 `n` 停機）
由閘門一行重得。不取代 M59（那裡的 σ 是具體組裝、且進一步推出不可判定與 Σ₁ 定位）；
此處只證明閘門確實涵蓋不可判定的實例——與下方零內容的質數實例對照。 -/
theorem sigma_reach_halting_of_gate (n : ℕ) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : ℕ → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ∀ m : ℕ, (∃ k : ℕ, σ^[k] (base m) ∈ Target) ↔
          ((Denumerable.ofNat Nat.Partrec.Code m).eval n).Dom :=
  sigma_reach_of_rePred ((ComputablePred.halting_problem_re n).of_eq fun _ => Iff.rfl)

/-- **質數電腦（機器層）** = 通用閘門填入 `Nat.Prime`。 -/
theorem prime_computer_uniform :
    ∃ (M : BitTM) (v₀ vhalt : Fin M.m → Bool) (tape : ℕ → Tape Bool),
      (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape M)^[k] (v₀, tape n)).1 = vhalt) ↔ Nat.Prime n) ∧
      (∀ n : ℕ, (∃ k : ℕ, (sigmaM M)^[k] (gEncB 8 (bitEnc v₀ (tape n)))
          ∈ {x | x.1 = (bitVecToNat M.m vhalt : ℝ)}) ↔ Nat.Prime n) :=
  rePred_computer_uniform rePred_nat_prime

/-- **質數電腦（∃ 版）** = 通用閘門填入 `Nat.Prime`。 -/
theorem sigmaRL3_prime_computer :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : ℕ → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ∀ n : ℕ, (∃ k : ℕ, σ^[k] (base n) ∈ Target) ↔ Nat.Prime n :=
  sigma_reach_of_rePred rePred_nat_prime

/-- 質數電腦的機器（由 `prime_computer_uniform` 取出的固定見證）。 -/
noncomputable def primeMachine : BitTM := Classical.choose prime_computer_uniform

/-- 固定起始狀態字。 -/
noncomputable def primeInit : Fin primeMachine.m → Bool :=
  Classical.choose (Classical.choose_spec prime_computer_uniform)

/-- 固定停機字。 -/
noncomputable def primeHalt : Fin primeMachine.m → Bool :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec prime_computer_uniform))

/-- 輸入帶：`n` 唯一進入的地方。 -/
noncomputable def primeTape : ℕ → Tape Bool :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prime_computer_uniform)))

/-- 四個見證的規格（`prime_computer_uniform` 的內容，套在具名常數上）。 -/
theorem primeSpec :
    (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape primeMachine)^[k] (primeInit, primeTape n)).1 = primeHalt)
        ↔ Nat.Prime n) ∧
    (∀ n : ℕ, (∃ k : ℕ, (sigmaM primeMachine)^[k] (gEncB 8 (bitEnc primeInit (primeTape n)))
        ∈ {x | x.1 = (bitVecToNat primeMachine.m primeHalt : ℝ)}) ↔ Nat.Prime n) :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prime_computer_uniform)))

/-- 質數電腦的光滑映射（常數，與 `n` 無關）。 -/
noncomputable def primeSigma : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := sigmaM primeMachine

/-- 目標集（常數，與 `n` 無關）。 -/
noncomputable def primeTarget : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 = (bitVecToNat primeMachine.m primeHalt : ℝ)}

/-- 起點：`n` 寫上帶子後的編碼。 -/
noncomputable def primeBase (n : ℕ) : ℝ × ℝ × ℝ := gEncB 8 (bitEnc primeInit (primeTape n))

theorem primeSigma_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) primeSigma :=
  sigmaM_contDiff primeMachine

/-- **★具名常數版★**：`n` 在陳述中只出現一次（在 `primeBase n` 裡），`primeSigma`、`primeTarget` 是常數。 -/
theorem primeSigma_reach_iff (n : ℕ) :
    (∃ k : ℕ, primeSigma^[k] (primeBase n) ∈ primeTarget) ↔ Nat.Prime n :=
  primeSpec.2 n

/-- 機器層具名版：`n` 只在 `primeTape n`。 -/
theorem primeMachine_reach_iff (n : ℕ) :
    (∃ k : ℕ, ((bitStepTape primeMachine)^[k] (primeInit, primeTape n)).1 = primeHalt)
      ↔ Nat.Prime n :=
  primeSpec.1 n

/-- 合數（與 0、1）的軌道永不到達目標。 -/
theorem primeSigma_not_reach_of_not_prime {n : ℕ} (h : ¬ Nat.Prime n) :
    ∀ k : ℕ, primeSigma^[k] (primeBase n) ∉ primeTarget := by
  intro k hk
  exact h ((primeSigma_reach_iff n).mp ⟨k, hk⟩)

theorem primeSigma_not_reach_zero : ∀ k : ℕ, primeSigma^[k] (primeBase 0) ∉ primeTarget :=
  primeSigma_not_reach_of_not_prime Nat.not_prime_zero

theorem primeSigma_not_reach_one : ∀ k : ℕ, primeSigma^[k] (primeBase 1) ∉ primeTarget :=
  primeSigma_not_reach_of_not_prime Nat.not_prime_one

/-- 質數的軌道會到達目標（存在有限步）。 -/
theorem primeSigma_reach_of_prime {n : ℕ} (h : Nat.Prime n) :
    ∃ k : ℕ, primeSigma^[k] (primeBase n) ∈ primeTarget :=
  (primeSigma_reach_iff n).mpr h

end FluidTuring
