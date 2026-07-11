import Mathlib
import FluidTuringLean.M51_AutonomousClock

/-!
# Module 52 — L3 整合磚：自治 leapfrog（period-2 閘 + 精確 HOLD + 耦合自治場的窗解）

**承 M51（L3 主磚）**。M51 的 period-1 閘無平坦段（無 HOLD）；leapfrog 需**互補窗**：A-閘活在
`[2n,2n+1]`、B-閘活在 `[2n+1,2n+2]`，各自 off-窗**恰 0**。本磚交付 period-2 時鐘 + **自治耦合
leapfrog 場**的窗解——M42 leapfrog 的**自治版**。

## 交付（全顯式、零 FTC、零 MeasureTheory、零 sorry、標準三公理）

- `φ₀_at_zero`（`φ₀ 0 = 0` 邊界、左側極限——M51 `φ₀_at_one` 的鏡像）；
- **period-2 閘** `clockGate2 θ := φ₀(2·fract(θ/2))`（活 `[2n,2n+1]`、**恰 0 於 `[2n+1,2n+2]` 閉區間**
  = `clockGate2_hold`，含兩端點）+ 局部兩項和 ⟹ C^∞；
- **period-2 階梯** `clockStair2 := smoothTransition(2·fract(θ/2)) + ⌊θ/2⌋`（顯式反導數、
  `clockStair2_hasDerivAt` 逐點）+ **HOLD 期值凍結** `clockStair2_frozen`（`= n+1` 恰）；
- **★自治耦合 leapfrog 場★**
  `leapField (y₁,y₂,θ) = (−C·gate2(θ)·(y₁−σ₁ y₂), −C·gate2(θ−1)·(y₂−σ₂ y₁), 1)`
  ——**只依賴狀態**、目標讀**對方 live 值**；
- **★L3 整合 HEADLINE★** `leapWindow_isSolution`：A-窗 `[2n,2n+1]` 上，凍結-`y₂` 顯式解
  `(targetingGatedSol（Φ=階梯差）, c₂, 2n+t)` **真滿足耦合自治場**（`t∈[0,1]` 全閉區間；B-閘於窗上
  恰 0 ⟹ `y₂` 分量吸收——M42 write-protect 的自治版）；`leapField_contDiff`（σ 光滑時場 C^∞）。

## ★誠實範圍（禁 overclaim）★

- 同 M42 的「寫法耦合、動態解耦」誠實：窗上 `y₂` 被 HOLD 凍成 `c₂` ⟹ `σ₁(y₂ live)=σ₁ c₂` 常數、
  B-分量恰 0——**每窗一分量 live**（leapfrog 本意）、非同時雙向。`σ₁` 只在凍結值取值（無正則性假設）。
- **窗解、非全域軌道**：本磚給單一 A-窗的解；B-窗鏡像 + N 窗接力串接（M43 相位版）= 後續磚。
- 不動 σ 具體化/undecidability（正交、禁宣稱）。C^∞ 非 analytic。
-/

namespace FluidTuring

open Real Filter Topology

/-! ## φ₀ 於 0 的邊界精確消沒（M51 `φ₀_at_one` 鏡像） -/

/-- **邊界精確**：`φ₀ 0 = 0`（連續性 + 左側極限唯一）。 -/
theorem φ₀_at_zero : deriv Real.smoothTransition 0 = 0 := by
  have h1 : Tendsto (deriv Real.smoothTransition) (nhdsWithin 0 (Set.Iio 0))
      (nhds (deriv Real.smoothTransition 0)) :=
    (φ₀_continuous.continuousAt.continuousWithinAt).tendsto
  have h2 : Tendsto (deriv Real.smoothTransition) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (φ₀_neg hx).symm
  exact tendsto_nhds_unique h1 h2

/-! ## period-2 閘與階梯 -/

/-- **period-2 閘**：活在 `[2n,2n+1]`、恰 0 於 `[2n+1,2n+2]`。 -/
noncomputable def clockGate2 (θ : ℝ) : ℝ :=
  deriv Real.smoothTransition (2 * Int.fract (θ / 2))

/-- **period-2 階梯**（`clockGate2` 的顯式反導數；HOLD 期值凍結）。 -/
noncomputable def clockStair2 (θ : ℝ) : ℝ :=
  Real.smoothTransition (2 * Int.fract (θ / 2)) + (⌊θ / 2⌋ : ℝ)

/-- 每點都落在 `(2⌊θ/2⌋−2, 2⌊θ/2⌋+2)`。 -/
theorem mem_Ioo_floor2 (θ : ℝ) :
    θ ∈ Set.Ioo (2 * ((⌊θ / 2⌋ : ℤ) : ℝ) - 2) (2 * ((⌊θ / 2⌋ : ℤ) : ℝ) + 2) := by
  constructor
  · linarith [Int.floor_le (θ / 2)]
  · linarith [Int.lt_floor_add_one (θ / 2)]

/-- **閘的局部兩項和**（period-2）：於 `(2n−2, 2n+2)` 上
`clockGate2 = φ₀(θ−2(n−1)) + φ₀(θ−2n)`。 -/
theorem clockGate2_eq_local (n : ℤ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (2 * (n : ℝ) - 2) (2 * (n : ℝ) + 2)) :
    clockGate2 θ = deriv Real.smoothTransition (θ - 2 * ((n : ℝ) - 1))
      + deriv Real.smoothTransition (θ - 2 * (n : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := hθ
  rcases lt_trichotomy θ (2 * (n : ℝ)) with hlt | heq | hgt
  · have hfl : ⌊θ / 2⌋ = n - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * ((n : ℝ) - 1) := by
      simp only [Int.fract, hfl]; push_cast; ring
    rw [clockGate2, hfr, φ₀_neg (by linarith : θ - 2 * (n : ℝ) < 0), add_zero]
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [heq]
      rw [show 2 * (n : ℝ) / 2 = (n : ℝ) by ring, Int.floor_intCast]
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    have e2 : θ - 2 * (n : ℝ) = 0 := by rw [heq]; ring
    have e1 : θ - 2 * ((n : ℝ) - 1) = 2 := by rw [heq]; ring
    rw [clockGate2, hfr, e1, e2, φ₀_gt_one (by norm_num : (1 : ℝ) < 2), zero_add]
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    rw [clockGate2, hfr,
      φ₀_gt_one (by linarith : 1 < θ - 2 * ((n : ℝ) - 1)), zero_add]

/-- **階梯的局部兩項和**（period-2）。 -/
theorem clockStair2_eq_local (n : ℤ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (2 * (n : ℝ) - 2) (2 * (n : ℝ) + 2)) :
    clockStair2 θ = Real.smoothTransition (θ - 2 * ((n : ℝ) - 1))
      + Real.smoothTransition (θ - 2 * (n : ℝ)) + ((n : ℝ) - 1) := by
  obtain ⟨hlo, hhi⟩ := hθ
  rcases lt_trichotomy θ (2 * (n : ℝ)) with hlt | heq | hgt
  · have hfl : ⌊θ / 2⌋ = n - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * ((n : ℝ) - 1) := by
      simp only [Int.fract, hfl]; push_cast; ring
    rw [clockStair2, hfr,
      Real.smoothTransition.zero_of_nonpos (by linarith : θ - 2 * (n : ℝ) ≤ 0), hfl]
    push_cast; ring
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [heq, show 2 * (n : ℝ) / 2 = (n : ℝ) by ring, Int.floor_intCast]
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    have e2 : θ - 2 * (n : ℝ) = 0 := by rw [heq]; ring
    have e1 : θ - 2 * ((n : ℝ) - 1) = 2 := by rw [heq]; ring
    rw [clockStair2, hfr, e1, e2, Real.smoothTransition.zero,
      Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2), hfl]
    ring
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    rw [clockStair2, hfr,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ θ - 2 * ((n : ℝ) - 1)), hfl]
    ring

/-- **period-2 閘 C^∞**。 -/
theorem clockGate2_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) clockGate2 := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  set n : ℤ := ⌊θ / 2⌋ with hn
  have hmem := mem_Ioo_floor2 θ
  have hloc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => deriv Real.smoothTransition (u - 2 * ((n : ℝ) - 1))
        + deriv Real.smoothTransition (u - 2 * (n : ℝ))) :=
    (φ₀_contDiff.comp (by fun_prop)).add (φ₀_contDiff.comp (by fun_prop))
  apply hloc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
  exact clockGate2_eq_local n u hu

/-- **★period-2 階梯 = 閘的顯式反導數（逐點、零 FTC）★**。 -/
theorem clockStair2_hasDerivAt (θ : ℝ) : HasDerivAt clockStair2 (clockGate2 θ) θ := by
  set n : ℤ := ⌊θ / 2⌋ with hn
  have hmem := mem_Ioo_floor2 θ
  have h1 := windowΦ_hasDerivAt (2 * ((n : ℝ) - 1)) θ
  have h2 := windowΦ_hasDerivAt (2 * (n : ℝ)) θ
  have hloc : HasDerivAt
      (fun u => Real.smoothTransition (u - 2 * ((n : ℝ) - 1))
        + Real.smoothTransition (u - 2 * (n : ℝ)) + ((n : ℝ) - 1))
      (deriv Real.smoothTransition (θ - 2 * ((n : ℝ) - 1))
        + deriv Real.smoothTransition (θ - 2 * (n : ℝ))) θ :=
    (h1.add h2).add_const _
  have hval : deriv Real.smoothTransition (θ - 2 * ((n : ℝ) - 1))
      + deriv Real.smoothTransition (θ - 2 * (n : ℝ)) = clockGate2 θ :=
    (clockGate2_eq_local n θ hmem).symm
  rw [← hval]
  apply hloc.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
  exact clockStair2_eq_local n u hu

/-! ## HOLD：閘於 `[2n+1, 2n+2]` **閉區間**恰 0、階梯值凍結 -/

/-- **★HOLD（閘恰 0、含兩端點）★**：`θ ∈ [2n+1, 2n+2] ⟹ clockGate2 θ = 0`。 -/
theorem clockGate2_hold {n : ℤ} {θ : ℝ} (h1 : 2 * (n : ℝ) + 1 ≤ θ)
    (h2 : θ ≤ 2 * (n : ℝ) + 2) : clockGate2 θ = 0 := by
  rcases eq_or_lt_of_le h2 with heq | hlt
  · have hfl : ⌊θ / 2⌋ = n + 1 := by
      rw [heq, show (2 * (n : ℝ) + 2) / 2 = ((n + 1 : ℤ) : ℝ) by push_cast; ring,
        Int.floor_intCast]
    have hfr : 2 * Int.fract (θ / 2) = 0 := by
      simp only [Int.fract, hfl]; rw [heq]; push_cast; ring
    rw [clockGate2, hfr, φ₀_at_zero]
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    rw [clockGate2, hfr]
    exact φ₀_ge_one (by linarith)

/-- **HOLD（階梯值凍結）**：`θ ∈ [2n+1, 2n+2] ⟹ clockStair2 θ = n + 1` 恰。 -/
theorem clockStair2_frozen {n : ℤ} {θ : ℝ} (h1 : 2 * (n : ℝ) + 1 ≤ θ)
    (h2 : θ ≤ 2 * (n : ℝ) + 2) : clockStair2 θ = (n : ℝ) + 1 := by
  rcases eq_or_lt_of_le h2 with heq | hlt
  · have hfl : ⌊θ / 2⌋ = n + 1 := by
      rw [heq, show (2 * (n : ℝ) + 2) / 2 = ((n + 1 : ℤ) : ℝ) by push_cast; ring,
        Int.floor_intCast]
    have hfr : 2 * Int.fract (θ / 2) = 0 := by
      simp only [Int.fract, hfl]; rw [heq]; push_cast; ring
    rw [clockStair2, hfr, Real.smoothTransition.zero, hfl]
    push_cast; ring
  · have hfl : ⌊θ / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : 2 * Int.fract (θ / 2) = θ - 2 * (n : ℝ) := by
      simp only [Int.fract, hfl]; ring
    rw [clockStair2, hfr,
      Real.smoothTransition.one_of_one_le (by linarith), hfl]
    ring

/-! ## ★自治耦合 leapfrog 場 + 窗解★ -/

/-- **自治耦合 leapfrog 場**：`(y₁,y₂,θ) ↦ (−C·gate2(θ)·(y₁−σ₁ y₂), −C·gate2(θ−1)·(y₂−σ₂ y₁), 1)`
——**只依賴狀態**、目標讀**對方 live 值**、A/B 閘互補。 -/
noncomputable def leapField (σ₁ σ₂ : ℝ → ℝ) (C : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun p => (-C * clockGate2 p.2.2 * (p.1 - σ₁ p.2.1),
            -C * clockGate2 (p.2.2 - 1) * (p.2.1 - σ₂ p.1),
            1)

/-- A-窗（`θ₀ = 2n` 起）的凍結-`y₂` 顯式解：`(targetingGatedSol（Φ=階梯差）, c₂, 2n+t)`。 -/
noncomputable def leapWindowSol (y₁₀ c₂ C : ℝ) (σ₁ : ℝ → ℝ) (n : ℤ) : ℝ → ℝ × ℝ × ℝ :=
  fun t => (targetingGatedSol y₁₀ (σ₁ c₂) C
      (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t,
    c₂, 2 * (n : ℝ) + t)

/-- **★L3 整合 HEADLINE：窗解真滿足自治耦合場★**：`t ∈ [0,1]`（A-窗全閉區間）上
`HasDerivAt (leapWindowSol …) (leapField σ₁ σ₂ C (leapWindowSol … t)) t`。
B-閘於窗上**恰 0**（`clockGate2_hold`，端點靠 `φ₀_at_zero/φ₀_at_one`）⟹ `y₂` 分量吸收
（M42 write-protect 的自治版）；`σ₁` 只在凍結值 `c₂` 取值。 -/
theorem leapWindow_isSolution (y₁₀ c₂ C : ℝ) (σ₁ σ₂ : ℝ → ℝ) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (leapWindowSol y₁₀ c₂ C σ₁ n)
      (leapField σ₁ σ₂ C (leapWindowSol y₁₀ c₂ C σ₁ n t)) t := by
  obtain ⟨ht0, ht1⟩ := ht
  -- θ 分量
  have hθ : HasDerivAt (fun s : ℝ => 2 * (n : ℝ) + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (2 * (n : ℝ))
  -- y₁ 分量（M51 手法）
  have hstair : HasDerivAt (fun s => clockStair2 (2 * (n : ℝ) + s))
      (clockGate2 (2 * (n : ℝ) + t)) t :=
    HasDerivAt.comp_const_add _ _ (clockStair2_hasDerivAt _)
  have hΦ := hstair.sub_const (clockStair2 (2 * (n : ℝ)))
  have hy₁ := targetingGatedSol_hasDerivAt y₁₀ (σ₁ c₂) C
    (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ)))
    (clockGate2 (2 * (n : ℝ) + t)) t hΦ
  -- y₂ 分量：常數
  have hy₂ : HasDerivAt (fun _ : ℝ => c₂) 0 t := hasDerivAt_const t c₂
  -- B-閘於窗上恰 0
  have hBzero : clockGate2 (2 * (n : ℝ) + t - 1) = 0 := by
    apply clockGate2_hold (n := n - 1)
    · push_cast; linarith
    · push_cast; linarith
  -- 場在窗解上的值
  have hfield : leapField σ₁ σ₂ C (leapWindowSol y₁₀ c₂ C σ₁ n t)
      = (-C * clockGate2 (2 * (n : ℝ) + t) *
          (targetingGatedSol y₁₀ (σ₁ c₂) C
            (fun s => clockStair2 (2 * (n : ℝ) + s) - clockStair2 (2 * (n : ℝ))) t
            - σ₁ c₂), 0, 1) := by
    simp only [leapField, leapWindowSol]
    rw [hBzero]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    ring
  rw [hfield]
  exact hy₁.prodMk (hy₂.prodMk hθ)

/-- **場 C^∞**（σ 光滑時）。 -/
theorem leapField_contDiff (σ₁ σ₂ : ℝ → ℝ) (C : ℝ)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ₂) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (leapField σ₁ σ₂ C) := by
  unfold leapField
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ contDiff_const)
  · exact (contDiff_const.mul (clockGate2_contDiff.comp contDiff_snd.snd)).mul
      (contDiff_fst.sub (h₁.comp contDiff_snd.fst))
  · exact (contDiff_const.mul (clockGate2_contDiff.comp
      (contDiff_snd.snd.sub contDiff_const))).mul
      (contDiff_snd.fst.sub (h₂.comp contDiff_fst))

end FluidTuring
