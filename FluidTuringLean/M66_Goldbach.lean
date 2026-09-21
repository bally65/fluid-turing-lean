import FluidTuringLean.M65_Collatz

/-!
# Module 66 — 閘門的第二個實例：Goldbach（猜想 ⟺ 軌道永不到達）

**承 M64（通用閘門）+ M65（Collatz 實例的樣板）**。半可判定謂詞：

> `GoldbachFailsFrom n := ∃ m, n ≤ m ∧ GoldbachCounterexample m`

（從 `n` 往上存在 Goldbach 反例——找到就停，找不到就跑下去）。塞進閘門得到

> **`goldbachSigma_reach_iff`**：`(∃ k, goldbachSigma^[k] (goldbachBase n) ∈ goldbachTarget) ↔ GoldbachFailsFrom n`
>
> **`goldbachConjecture_iff_never_reach`**：Goldbach 猜想 ⟺ 從 `goldbachBase 0` 出發的軌道**永不**打進
> `goldbachTarget`。

與 M65 的對偶：Collatz 猜想 = **所有**正整數起點都到達；Goldbach 猜想 = **一個**起點永不到達
（confinement 形狀，對照 M63 `sigmaRL3_confinement_undecidable`）。

## 交付（零 sorry、標準三公理）

- `GoldbachCounterexample`（可判定；`primrecPred_goldbachCounterexample` 重用 M64 的 `primrecPred_nat_prime`）、
  `GoldbachFailsFrom`（Σ₁；`rePred_goldbachFailsFrom`）、`GoldbachConjecture`（標準陳述）與
  `goldbachConjecture_iff_not_failsFrom_zero`（兩種寫法的橋）。
- 閘門實例 `goldbach_computer_uniform` / `sigma_reach_goldbach`；具名常數與 `goldbachSigma_reach_iff`；
  `goldbachConjecture_iff_never_reach`。
- `decide` 小例：`28` 不是反例（`5 + 23`）。

## ★誠實範圍（禁 overclaim）★

1. **零新數論內容。** 不證、不逼近 Goldbach；`goldbachConjecture_iff_never_reach` 是把猜想的真值搬進
   一個動力系統的 confinement 問題——**重述，不是進展**。
2. **不可宣稱不可判定。** `GoldbachFailsFrom` 是 Σ₁。注意它與 Collatz 不同：若猜想為真，它**恆假**
   （平凡可判定）；若猜想為假且反例有限，它是「存在反例 ≥ n」＝有限門檻函數（也可判定）。
   我們不知道是哪一種——內容在「不知道」，不在「難」。
3. **一步也跑不動**（同 M64）；不是流體、不是流；C^∞ 非 analytic。
4. 本模組是閘門的示範實例，不是 repo headline。
-/

namespace FluidTuring

open Turing

/-! ## 1. 定義 -/

/-- `m` 是 Goldbach 反例：`m ≥ 4`、偶數、且對所有 `p ≤ m` 不成立「`p` 與 `m - p` 皆質數」。 -/
def GoldbachCounterexample (m : ℕ) : Prop :=
  4 ≤ m ∧ Even m ∧ ∀ p, p ≤ m → ¬ (Nat.Prime p ∧ Nat.Prime (m - p))

/-- 從 `n` 起存在 Goldbach 反例（半可判定：往上搜）。 -/
def GoldbachFailsFrom (n : ℕ) : Prop := ∃ m, n ≤ m ∧ GoldbachCounterexample m

/-- Goldbach 猜想（標準陳述）：每個 `≥ 4` 的偶數是兩質數之和。 -/
def GoldbachConjecture : Prop :=
  ∀ m, 4 ≤ m → Even m → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m

/-- `28 = 5 + 23` 不是反例。 -/
theorem not_goldbachCounterexample_28 : ¬ GoldbachCounterexample 28 := by
  rintro ⟨-, -, h⟩
  exact h 5 (by norm_num) ⟨by norm_num, by norm_num⟩

/-- 兩種寫法的橋：猜想 ⟺ 從 `0` 起不存在反例。 -/
theorem goldbachConjecture_iff_not_failsFrom_zero :
    GoldbachConjecture ↔ ¬ GoldbachFailsFrom 0 := by
  unfold GoldbachConjecture GoldbachFailsFrom GoldbachCounterexample
  constructor
  · rintro h ⟨m, -, h4, he, hnot⟩
    obtain ⟨p, q, hp, hq, hpq⟩ := h m h4 he
    refine hnot p (by omega) ⟨hp, ?_⟩
    rw [show m - p = q by omega]; exact hq
  · intro h m h4 he
    by_contra hcon
    push Not at hcon
    exact h ⟨m, Nat.zero_le m, h4, he,
      fun p hp ⟨hpp, hqp⟩ => hcon p (m - p) hpp hqp (Nat.add_sub_of_le hp)⟩

/-! ## 2. 可計算性 -/

/-- 反例謂詞是原始遞迴的（重用 M64 `primrecPred_nat_prime`）。 -/
theorem primrecPred_goldbachCounterexample : PrimrecPred GoldbachCounterexample := by
  have h1 : PrimrecPred fun m : ℕ => 4 ≤ m :=
    Primrec.nat_le.comp (Primrec.const 4) Primrec.id
  have h2 : PrimrecPred fun m : ℕ => m % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  have hR : PrimrecRel fun p m : ℕ => ¬ (Nat.Prime p ∧ Nat.Prime (m - p)) := by
    refine PrimrecRel.not ?_
    unfold PrimrecRel
    exact PrimrecPred.and (primrecPred_nat_prime.comp Primrec.fst)
      (primrecPred_nat_prime.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst))
  have h3 : PrimrecPred fun m : ℕ => ∀ p < m + 1, ¬ (Nat.Prime p ∧ Nat.Prime (m - p)) :=
    (PrimrecRel.forall_lt hR).comp Primrec.succ Primrec.id
  refine ((h1.and h2).and h3).of_eq fun m => ?_
  unfold GoldbachCounterexample
  rw [Nat.even_iff, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact forall_congr' fun p => imp_congr_left Nat.lt_succ_iff

/-- **`GoldbachFailsFrom` 是 r.e.**：`Nat.rfind` 從 `n` 往上找第一個反例。 -/
theorem rePred_goldbachFailsFrom : REPred GoldbachFailsFrom := by
  obtain ⟨_, hdec⟩ := primrecPred_goldbachCounterexample
  have hc : Computable₂ fun n d : ℕ => decide (GoldbachCounterexample (n + d)) := by
    refine Primrec₂.to_comp ?_
    unfold Primrec₂
    exact (hdec.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)).of_eq
      fun q => decide_eq_decide.mpr Iff.rfl
  have hr : Partrec fun n : ℕ =>
      Nat.rfind fun d => (Part.some (decide (GoldbachCounterexample (n + d))) : Part Bool) :=
    Partrec.rfind hc.partrec₂
  refine hr.dom_re.of_eq fun n => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨d, hd, -⟩
    exact ⟨n + d, Nat.le_add_right n d, by simpa using hd⟩
  · rintro ⟨m, hnm, hm⟩
    refine ⟨m - n, ?_, fun _ => trivial⟩
    rw [Nat.add_sub_of_le hnm]; simpa using hm

/-! ## 3. 塞進閘門 -/

theorem goldbach_computer_uniform :
    ∃ (M : BitTM) (v₀ vhalt : Fin M.m → Bool) (tape : ℕ → Tape Bool),
      (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape M)^[k] (v₀, tape n)).1 = vhalt) ↔ GoldbachFailsFrom n) ∧
      (∀ n : ℕ, (∃ k : ℕ, (sigmaM M)^[k] (gEncB 8 (bitEnc v₀ (tape n)))
          ∈ {x | x.1 = (bitVecToNat M.m vhalt : ℝ)}) ↔ GoldbachFailsFrom n) :=
  rePred_computer_uniform rePred_goldbachFailsFrom

theorem sigma_reach_goldbach :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : ℕ → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ∀ n : ℕ, (∃ k : ℕ, σ^[k] (base n) ∈ Target) ↔ GoldbachFailsFrom n :=
  sigma_reach_of_rePred rePred_goldbachFailsFrom

/-! ## 4. 具名常數與猜想的重述 -/

noncomputable def goldbachMachine : BitTM := Classical.choose goldbach_computer_uniform

noncomputable def goldbachInit : Fin goldbachMachine.m → Bool :=
  Classical.choose (Classical.choose_spec goldbach_computer_uniform)

noncomputable def goldbachHalt : Fin goldbachMachine.m → Bool :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec goldbach_computer_uniform))

noncomputable def goldbachTape : ℕ → Tape Bool :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec goldbach_computer_uniform)))

theorem goldbachSpec :
    (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape goldbachMachine)^[k] (goldbachInit, goldbachTape n)).1
        = goldbachHalt) ↔ GoldbachFailsFrom n) ∧
    (∀ n : ℕ, (∃ k : ℕ, (sigmaM goldbachMachine)^[k]
        (gEncB 8 (bitEnc goldbachInit (goldbachTape n)))
        ∈ {x | x.1 = (bitVecToNat goldbachMachine.m goldbachHalt : ℝ)}) ↔ GoldbachFailsFrom n) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec goldbach_computer_uniform)))

noncomputable def goldbachSigma : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := sigmaM goldbachMachine

noncomputable def goldbachTarget : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 = (bitVecToNat goldbachMachine.m goldbachHalt : ℝ)}

noncomputable def goldbachBase (n : ℕ) : ℝ × ℝ × ℝ :=
  gEncB 8 (bitEnc goldbachInit (goldbachTape n))

theorem goldbachSigma_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) goldbachSigma :=
  sigmaM_contDiff goldbachMachine

/-- **★具名常數版★**：`n` 只出現一次。 -/
theorem goldbachSigma_reach_iff (n : ℕ) :
    (∃ k : ℕ, goldbachSigma^[k] (goldbachBase n) ∈ goldbachTarget) ↔ GoldbachFailsFrom n :=
  goldbachSpec.2 n

/-- **★Goldbach 猜想的動力系統重述★**：猜想成立 ⟺ 從 `goldbachBase 0` 出發的軌道永不打進
`goldbachTarget`。重述，不是進展（見檔頭）。 -/
theorem goldbachConjecture_iff_never_reach :
    GoldbachConjecture ↔ ∀ k : ℕ, goldbachSigma^[k] (goldbachBase 0) ∉ goldbachTarget := by
  rw [goldbachConjecture_iff_not_failsFrom_zero, ← goldbachSigma_reach_iff 0]
  exact not_exists

end FluidTuring
