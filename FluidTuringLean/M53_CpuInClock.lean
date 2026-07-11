import Mathlib
import FluidTuringLean.M52_AutonomousLeapfrog

/-!
# Module 53 — L3 合體：時鐘插進 CPU（自振盪流驅動真 `sigmaRL` 步、玩具晶片成形）

**承 M51/M52（自治時鐘 + 純量自治 leapfrog）+ M48-50（玩具 σ = `sigmaRL` + N 步精確）**。本磚把 M52 的
**純量**自治 leapfrog 抬到**向量**（兩個 `ℝ³` 暫存器 = 兩份完整組態編碼），並把抽象 `σ₁,σ₂` 換成**真的**
`sigmaRL` 玩具 CPU 步——**單一自治 C^∞ 向量場 `cpuField`，其流的一個時鐘窗把組態推進一個玩具 TM 步**。
= 「把外源時鐘內建進 CPU、讓 ODE 晶片自己跑玩具程式」的字面見證。

## 交付（全顯式、零 sorry、標準三公理）

- `gtVec`（向量 gated targeting = 3 座標各一份 `targetingGatedSol`）+ `gtVec_hasDerivAt`（`prodMk` × 3）。
- **`cpuField σstep C`（★自振盪 CPU 向量場★）**：`(r₁,r₂,θ) ↦ (−C·gate2(θ)·(r₁−σstep r₂),
  −C·gate2(θ−1)·(r₂−σstep r₁), 1)`——**只依賴狀態**、兩暫存器各讀對方跑 `σstep`、A/B 閘互補。
- **`cpuWindow_isSolution`（★HEADLINE★）**：A-窗 `[0,1]` 全閉區間上，凍結-`r₂` 顯式解真滿足 `cpuField`。
- `cpuField_contDiff`（`σstep` C^∞ ⟹ 場 C^∞）。
- **`cpuWindow_advances`（★晶片跑一步★）**：`σstep := sigmaRL`、`r₂ := gEnc c`（良編碼）⟹ 窗後 `r₁`
  = `gEnc(gStepRL c) + (r₁₀ − gEnc(gStepRL c))·e^{−C}`——**一個時鐘週期把組態推進一個玩具 TM 步**
  （接 `sigmaRL_exact_of_wf`）。

## ★誠實範圍（禁 overclaim、這是關鍵誠實點）★

- **連續流是 ε-近似、非精確**：離散映射 `sigmaRL` 是**字面精確**（M48-50）；但**連續時間流**在一個窗只把
  `r₁` 拉到 `gEnc(gStepRL c)` 的 **`e^{−C}`-鄰域**（`exp` 永不精確到達）。把 ε-流橋回精確需**每步 re-rounding**
  （`sround`/G3 施於狀態暫存器）= Wall B 的連續版，**本磚不做**（`cpuWindow_advances` 誠實顯示 `e^{−C}` 殘差）。
- **玩具、非真機**：`sigmaRL`/`gEnc`/`gStepRL` 是 module-local 玩具（有限 List 帶、兩堆疊非空、良編碼假設）。
  真通用機 = G4e（BitTM 無限帶橋）。**禁**宣稱線三 undecidability。
- **窗解、非全域軌道**：單一 A-窗；B-窗鏡像 + N 窗自治接力 = 後續。同 M42/M52「寫法耦合、動態解耦」
  （窗上 `r₂≡` 常數 ansatz、B-閘恰 0 使其與場一致）。C^∞ 非 analytic。
-/

namespace FluidTuring

open Real

/-- 組態編碼型別 `ℝ³`（= `gEnc` 的輸出型別）。 -/
abbrev Cfg3 := ℝ × ℝ × ℝ

/-- **向量 gated targeting**：3 座標各一份 `targetingGatedSol`（同閘 `Φ`、同 `C`）。 -/
noncomputable def gtVec (a tgt : Cfg3) (C : ℝ) (Φ : ℝ → ℝ) : ℝ → Cfg3 :=
  fun t => (targetingGatedSol a.1 tgt.1 C Φ t,
            targetingGatedSol a.2.1 tgt.2.1 C Φ t,
            targetingGatedSol a.2.2 tgt.2.2 C Φ t)

/-- **向量 gated ODE**：`gtVec` 真滿足逐座標閘控場（`prodMk` × 3）。 -/
theorem gtVec_hasDerivAt (a tgt : Cfg3) (C : ℝ) (Φ : ℝ → ℝ) (φ t : ℝ) (hΦ : HasDerivAt Φ φ t) :
    HasDerivAt (gtVec a tgt C Φ)
      (-C * φ * ((gtVec a tgt C Φ t).1 - tgt.1),
       -C * φ * ((gtVec a tgt C Φ t).2.1 - tgt.2.1),
       -C * φ * ((gtVec a tgt C Φ t).2.2 - tgt.2.2)) t := by
  have h1 := targetingGatedSol_hasDerivAt a.1 tgt.1 C Φ φ t hΦ
  have h2 := targetingGatedSol_hasDerivAt a.2.1 tgt.2.1 C Φ φ t hΦ
  have h3 := targetingGatedSol_hasDerivAt a.2.2 tgt.2.2 C Φ φ t hΦ
  exact h1.prodMk (h2.prodMk h3)

/-- 起點值 `= a`（`Φ(0)=0`）。 -/
theorem gtVec_start (a tgt : Cfg3) (C : ℝ) (Φ : ℝ → ℝ) (h0 : Φ 0 = 0) :
    gtVec a tgt C Φ 0 = a := by
  simp only [gtVec, targetingGatedSol, h0, mul_zero, neg_zero, Real.exp_zero, mul_one]
  ext <;> ring

/-- 窗後值（`Φ(1)=1`）：`= tgt + (a−tgt)·e^{−C}`（逐座標）。 -/
theorem gtVec_end (a tgt : Cfg3) (C : ℝ) (Φ : ℝ → ℝ) (h1 : Φ 1 = 1) :
    gtVec a tgt C Φ 1 = (tgt.1 + (a.1 - tgt.1) * Real.exp (-C),
      tgt.2.1 + (a.2.1 - tgt.2.1) * Real.exp (-C),
      tgt.2.2 + (a.2.2 - tgt.2.2) * Real.exp (-C)) := by
  simp only [gtVec, targetingGatedSol, h1, mul_one]

/-- **★自振盪 CPU 向量場★**：兩暫存器各讀對方跑 `σstep`、A/B 閘互補、`θ̇=1`——只依賴狀態。 -/
noncomputable def cpuField (σstep : Cfg3 → Cfg3) (C : ℝ) : Cfg3 × Cfg3 × ℝ → Cfg3 × Cfg3 × ℝ :=
  fun p =>
    ((-C * clockGate2 p.2.2 * (p.1.1 - (σstep p.2.1).1),
      -C * clockGate2 p.2.2 * (p.1.2.1 - (σstep p.2.1).2.1),
      -C * clockGate2 p.2.2 * (p.1.2.2 - (σstep p.2.1).2.2)),
     (-C * clockGate2 (p.2.2 - 1) * (p.2.1.1 - (σstep p.1).1),
      -C * clockGate2 (p.2.2 - 1) * (p.2.1.2.1 - (σstep p.1).2.1),
      -C * clockGate2 (p.2.2 - 1) * (p.2.1.2.2 - (σstep p.1).2.2)),
     1)

/-- A-窗（`θ₀=2n` 起）的凍結-`r₂` 顯式解：`(gtVec r₁₀ (σstep c₂), c₂, 2n+t)`。 -/
noncomputable def cpuWindowSol (r1₀ c₂ : Cfg3) (σstep : Cfg3 → Cfg3) (C : ℝ) (n : ℤ) :
    ℝ → Cfg3 × Cfg3 × ℝ :=
  fun t => (gtVec r1₀ (σstep c₂) C
      (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t,
    c₂, 2 * (n : ℝ) + t)

/-- **★HEADLINE：CPU 窗解真滿足自振盪場★**：A-窗 `t∈[0,1]` 上
`HasDerivAt (cpuWindowSol …) (cpuField σstep C (cpuWindowSol … t)) t`。B-閘恰 0 ⟹ `r₂` 分量吸收。 -/
theorem cpuWindow_isSolution (r1₀ c₂ : Cfg3) (σstep : Cfg3 → Cfg3) (C : ℝ) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (cpuWindowSol r1₀ c₂ σstep C n)
      (cpuField σstep C (cpuWindowSol r1₀ c₂ σstep C n t)) t := by
  obtain ⟨ht0, ht1⟩ := ht
  have hθ : HasDerivAt (fun s : ℝ => 2 * (n : ℝ) + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (2 * (n : ℝ))
  have hstair : HasDerivAt (fun s => clockStair2 (2 * (n : ℝ) + s))
      (clockGate2 (2 * (n : ℝ) + t)) t :=
    HasDerivAt.comp_const_add _ _ (clockStair2_hasDerivAt _)
  have hΦ := hstair.sub_const (clockStair2 (2 * (n : ℝ)))
  have hr1 := gtVec_hasDerivAt r1₀ (σstep c₂) C
    (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ)))
    (clockGate2 (2 * (n : ℝ) + t)) t hΦ
  have hr2 : HasDerivAt (fun _ : ℝ => c₂) (0 : Cfg3) t := hasDerivAt_const t c₂
  have hBzero : clockGate2 (2 * (n : ℝ) + t - 1) = 0 := by
    apply clockGate2_hold (n := n - 1)
    · push_cast; linarith
    · push_cast; linarith
  have hfield : cpuField σstep C (cpuWindowSol r1₀ c₂ σstep C n t)
      = ((-C * clockGate2 (2 * (n : ℝ) + t)
            * ((gtVec r1₀ (σstep c₂) C
              (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t).1
              - (σstep c₂).1),
          -C * clockGate2 (2 * (n : ℝ) + t)
            * ((gtVec r1₀ (σstep c₂) C
              (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t).2.1
              - (σstep c₂).2.1),
          -C * clockGate2 (2 * (n : ℝ) + t)
            * ((gtVec r1₀ (σstep c₂) C
              (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t).2.2
              - (σstep c₂).2.2)),
         (0 : Cfg3), 1) := by
    simp only [cpuField, cpuWindowSol, hBzero]
    refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
      (Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) rfl) <;>
      simp only [Prod.fst_zero, Prod.snd_zero] <;> ring
  rw [hfield]
  exact hr1.prodMk (hr2.prodMk hθ)

/-- **場 C^∞**（`σstep` C^∞ ⟹）。 -/
theorem cpuField_contDiff (σstep : Cfg3 → Cfg3) (C : ℝ)
    (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σstep) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cpuField σstep C) := by
  unfold cpuField
  have hg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Cfg3 × Cfg3 × ℝ => clockGate2 p.2.2) :=
    clockGate2_contDiff.comp contDiff_snd.snd
  have hg2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Cfg3 × Cfg3 × ℝ => clockGate2 (p.2.2 - 1)) :=
    clockGate2_contDiff.comp (contDiff_snd.snd.sub contDiff_const)
  have hs2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Cfg3 × Cfg3 × ℝ => σstep p.2.1) := hσ.comp contDiff_snd.fst
  have hs1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Cfg3 × Cfg3 × ℝ => σstep p.1) := hσ.comp contDiff_fst
  refine ContDiff.prodMk (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_))
    (ContDiff.prodMk (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)) contDiff_const)
  · exact (contDiff_const.mul hg1).mul (contDiff_fst.fst.sub hs2.fst)
  · exact (contDiff_const.mul hg1).mul (contDiff_fst.snd.fst.sub hs2.snd.fst)
  · exact (contDiff_const.mul hg1).mul (contDiff_fst.snd.snd.sub hs2.snd.snd)
  · exact (contDiff_const.mul hg2).mul (contDiff_snd.fst.fst.sub hs1.fst)
  · exact (contDiff_const.mul hg2).mul (contDiff_snd.fst.snd.fst.sub hs1.snd.fst)
  · exact (contDiff_const.mul hg2).mul (contDiff_snd.fst.snd.snd.sub hs1.snd.snd)

/-! ## ★晶片跑一步★：自振盪流的一個時鐘窗把玩具組態推進一個 `gStepRL` 步（ε-近似） -/

/-- 窗後 `r₁` 值（一般 `σstep`、`Φ(1)=1`）：`= σstep c₂ + (r₁₀ − σstep c₂)·e^{−C}`（逐座標）。 -/
theorem cpuWindowSol_end (r1₀ c₂ : Cfg3) (σstep : Cfg3 → Cfg3) (C : ℝ) (n : ℤ) :
    (cpuWindowSol r1₀ c₂ σstep C n 1).1
      = ((σstep c₂).1 + (r1₀.1 - (σstep c₂).1) * Real.exp (-C),
         (σstep c₂).2.1 + (r1₀.2.1 - (σstep c₂).2.1) * Real.exp (-C),
         (σstep c₂).2.2 + (r1₀.2.2 - (σstep c₂).2.2) * Real.exp (-C)) := by
  have hΦ1 : (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) 1 = 1 := by
    have := clockStair2_frozen (n := n) (θ := 2 * (n : ℝ) + 1) (by linarith) (by linarith)
    rw [clockStair2_even] at *
    simp only
    rw [show 2 * (n : ℝ) + 1 = 2 * (n : ℝ) + 1 from rfl] at this
    rw [this]; ring
  simp only [cpuWindowSol]
  rw [gtVec_end _ _ _ _ hΦ1]

/-- **★晶片跑一步（ε-近似）★**：`σstep := sigmaRL`、`r₂ := gEnc c`（良編碼 + headroom）⟹ 窗後 `r₁`
`= gEnc(gStepRL c) + (r₁₀ − gEnc(gStepRL c))·e^{−C}`——**一個自治時鐘週期把玩具組態推進一個 TM 步**
（誠實 `e^{−C}` 殘差 = 連續流非精確、需 re-rounding 橋、見檔頭）。 -/
theorem cpuWindow_advances (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (r1₀ : Cfg3) (C : ℝ) (n : ℤ)
    (q l₀ s : ℕ) (L' R' : List ℕ) (hwf : wfCfg Q k ⟨q, l₀ :: L', s :: R'⟩) :
    (cpuWindowSol r1₀ (gEnc K ⟨q, l₀ :: L', s :: R'⟩)
        (sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
          (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w) C n 1).1
      = ((gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).1
          + (r1₀.1 - (gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).1) * Real.exp (-C),
         (gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).2.1
          + (r1₀.2.1 - (gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).2.1) * Real.exp (-C),
         (gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).2.2
          + (r1₀.2.2 - (gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩)).2.2)
            * Real.exp (-C)) := by
  have hstep := sigmaRL_exact_of_wf δqN δwN moveB Q k K hk hkK hK hw0 hw1 hwhead
    q l₀ s L' R' hwf
  rw [cpuWindowSol_end, hstep]

end FluidTuring
