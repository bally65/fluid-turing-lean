import FluidTuringLean.M64_PrimeComputer

/-!
# Module 65 — 閘門的第一個非平凡實例：Collatz

**承 M64（`rePred_computer_uniform` / `sigma_reach_of_rePred` 通用閘門）**。把半可判定謂詞
`CollatzReaches n := ∃ k, collatzStep^[k] n = 1` 塞進閘門，得到：

> **`collatzSigma_reach_iff`**：`(∃ k, collatzSigma^[k] (collatzBase n) ∈ collatzTarget) ↔ CollatzReaches n`
> （`collatzSigma`、`collatzTarget` 為常數，`n` 只出現一次）。
>
> **`collatzConjecture_iff_reach`**：Collatz 猜想 ⟺ 所有正整數起點的軌道都到達 `collatzTarget`。

## 為什麼這個實例有內容而質數實例沒有

`Nat.Prime` 有完整判定程序（Δ₁），所以「軌道可達性」對它是繞遠路；`CollatzReaches` 只知道是 Σ₁
（半可判定：找到到達 1 的步數就停），**是否可判定是開放問題**——沒有已知的完整判定程序可以拿來比。
因此對這個 `p`，「丟進去看停不停」是目前已知最好的形狀。這是 M64 檔頭那條規則的正例。

## 交付（零 sorry、標準三公理）

- `collatzStep`、`CollatzReaches`、`CollatzConjecture`（定義）；`primrec_collatzStep`、`primrec_collatzIter`、
  `rePred_collatzReaches`（Σ₁ 證明：`Partrec.rfind` + `Partrec.dom_re`）。
- `collatz_computer_uniform`、`sigma_reach_collatz`（閘門實例）；具名常數 `collatzSigma` / `collatzBase` /
  `collatzTarget` 與 `collatzSigma_reach_iff`；`collatzConjecture_iff_reach`。
- `not_collatzReaches_zero`（起點 0 永不到達）、小例 `collatzReaches_one`、`collatzReaches_six`。

## ★誠實範圍（禁 overclaim）★

1. **零新數論內容。** 本模組**不證** Collatz、**不逼近** Collatz、對 Collatz 的真假沒有任何新資訊。
   `collatzConjecture_iff_reach` 是把猜想的真值**搬運**到一個動力系統的可達性問題——是**重述**，不是進展。
2. **不可宣稱不可判定。** `CollatzReaches` 是否可判定是開放的；本模組只用到它是 Σ₁（半可判定）。
   「有內容」的意思是「沒有更好的形狀可比」，不是「證明了它難」。
3. **一步也跑不動**（同 M64：`sigmaM`、編碼器、通用機的 enc/dec 皆 noncomputable）。
4. **不是流體、不是流**；C^∞ 非 analytic（M60）。
5. 本模組是閘門的**示範實例**，不是 repo headline。
-/

namespace FluidTuring

open Turing

/-! ## 1. Collatz 映射與到達謂詞 -/

/-- Collatz 一步：偶數除二、奇數乘三加一。 -/
def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- 從 `n` 出發有限步到達 `1`。 -/
def CollatzReaches (n : ℕ) : Prop := ∃ k : ℕ, collatzStep^[k] n = 1

/-- Collatz 猜想：所有正整數都到達 `1`。 -/
def CollatzConjecture : Prop := ∀ n : ℕ, 0 < n → CollatzReaches n

theorem collatzReaches_one : CollatzReaches 1 := ⟨0, rfl⟩

/-- `6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1`（8 步）。 -/
theorem collatzReaches_six : CollatzReaches 6 := ⟨8, by decide⟩

theorem collatzStep_iterate_zero (k : ℕ) : collatzStep^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- 起點 `0` 永不到達（`collatzStep 0 = 0`）。 -/
theorem not_collatzReaches_zero : ¬ CollatzReaches 0 := by
  rintro ⟨k, hk⟩
  rw [collatzStep_iterate_zero] at hk
  exact absurd hk (by decide)

/-! ## 2. 可計算性：`CollatzReaches` 是半可判定的（Σ₁） -/

theorem primrec_collatzStep : Primrec collatzStep := by
  unfold collatzStep
  refine Primrec.ite ?_ ?_ ?_
  · exact Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  · exact Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id) (Primrec.const 1)

/-- `(n, k) ↦ collatzStep^[k] n` 原始遞迴（`Primrec.nat_iterate`）。 -/
theorem primrec_collatzIter : Primrec₂ fun n k : ℕ => collatzStep^[k] n :=
  Primrec.nat_iterate Primrec.snd Primrec.fst (primrec_collatzStep.comp Primrec.snd)

/-- **`CollatzReaches` 是 r.e.**：`Nat.rfind` 找最小的 `k` 使 `collatzStep^[k] n = 1`，其定義域恰為
`CollatzReaches`。 -/
theorem rePred_collatzReaches : REPred CollatzReaches := by
  have hp : PrimrecPred fun q : ℕ × ℕ => collatzStep^[q.2] q.1 = 1 :=
    Primrec.eq.comp primrec_collatzIter (Primrec.const 1)
  obtain ⟨_, hdec⟩ := hp
  have hc : Computable₂ fun n k : ℕ => decide (collatzStep^[k] n = 1) := by
    refine Primrec₂.to_comp ?_
    unfold Primrec₂
    exact hdec.of_eq fun q => decide_eq_decide.mpr Iff.rfl
  have hr : Partrec fun n : ℕ =>
      Nat.rfind fun k => (Part.some (decide (collatzStep^[k] n = 1)) : Part Bool) :=
    Partrec.rfind hc.partrec₂
  refine hr.dom_re.of_eq fun n => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk, fun _ => trivial⟩

/-! ## 3. 塞進閘門 -/

/-- Collatz 電腦（機器層）= 閘門填入 `CollatzReaches`。 -/
theorem collatz_computer_uniform :
    ∃ (M : BitTM) (v₀ vhalt : Fin M.m → Bool) (tape : ℕ → Tape Bool),
      (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape M)^[k] (v₀, tape n)).1 = vhalt) ↔ CollatzReaches n) ∧
      (∀ n : ℕ, (∃ k : ℕ, (sigmaM M)^[k] (gEncB 8 (bitEnc v₀ (tape n)))
          ∈ {x | x.1 = (bitVecToNat M.m vhalt : ℝ)}) ↔ CollatzReaches n) :=
  rePred_computer_uniform rePred_collatzReaches

/-- Collatz 電腦（∃ 版）。 -/
theorem sigma_reach_collatz :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : ℕ → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ∀ n : ℕ, (∃ k : ℕ, σ^[k] (base n) ∈ Target) ↔ CollatzReaches n :=
  sigma_reach_of_rePred rePred_collatzReaches

/-! ## 4. 具名常數與猜想的重述 -/

noncomputable def collatzMachine : BitTM := Classical.choose collatz_computer_uniform

noncomputable def collatzInit : Fin collatzMachine.m → Bool :=
  Classical.choose (Classical.choose_spec collatz_computer_uniform)

noncomputable def collatzHalt : Fin collatzMachine.m → Bool :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec collatz_computer_uniform))

noncomputable def collatzTape : ℕ → Tape Bool :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec collatz_computer_uniform)))

theorem collatzSpec :
    (∀ n : ℕ, (∃ k : ℕ, ((bitStepTape collatzMachine)^[k] (collatzInit, collatzTape n)).1
        = collatzHalt) ↔ CollatzReaches n) ∧
    (∀ n : ℕ, (∃ k : ℕ, (sigmaM collatzMachine)^[k] (gEncB 8 (bitEnc collatzInit (collatzTape n)))
        ∈ {x | x.1 = (bitVecToNat collatzMachine.m collatzHalt : ℝ)}) ↔ CollatzReaches n) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec collatz_computer_uniform)))

/-- Collatz 電腦的光滑映射（常數）。 -/
noncomputable def collatzSigma : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := sigmaM collatzMachine

/-- 目標集（常數）。 -/
noncomputable def collatzTarget : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 = (bitVecToNat collatzMachine.m collatzHalt : ℝ)}

/-- 起點：`n` 寫上帶子後的編碼。 -/
noncomputable def collatzBase (n : ℕ) : ℝ × ℝ × ℝ := gEncB 8 (bitEnc collatzInit (collatzTape n))

theorem collatzSigma_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) collatzSigma :=
  sigmaM_contDiff collatzMachine

/-- **★具名常數版★**：`n` 只出現一次。 -/
theorem collatzSigma_reach_iff (n : ℕ) :
    (∃ k : ℕ, collatzSigma^[k] (collatzBase n) ∈ collatzTarget) ↔ CollatzReaches n :=
  collatzSpec.2 n

theorem collatzMachine_reach_iff (n : ℕ) :
    (∃ k : ℕ, ((bitStepTape collatzMachine)^[k] (collatzInit, collatzTape n)).1 = collatzHalt)
      ↔ CollatzReaches n :=
  collatzSpec.1 n

/-- **★Collatz 猜想的動力系統重述★**：猜想成立 ⟺ 每個正整數起點的 `collatzSigma` 軌道都在有限步內
打進 `collatzTarget`。這是重述，不是進展（見檔頭誠實範圍）。 -/
theorem collatzConjecture_iff_reach :
    CollatzConjecture ↔
      ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatzSigma^[k] (collatzBase n) ∈ collatzTarget := by
  unfold CollatzConjecture
  exact forall_congr' fun n => imp_congr_right fun _ => (collatzSigma_reach_iff n).symm

/-- 起點 `0` 的軌道永不到達目標（與 `not_collatzReaches_zero` 對照）。 -/
theorem collatzSigma_not_reach_zero : ∀ k : ℕ, collatzSigma^[k] (collatzBase 0) ∉ collatzTarget := by
  intro k hk
  exact not_collatzReaches_zero ((collatzSigma_reach_iff 0).mp ⟨k, hk⟩)

end FluidTuring
