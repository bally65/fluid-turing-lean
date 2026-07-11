import Mathlib
import FluidTuringLean.M50_TubeInvariant

/-!
# Module 51 — L3 Brick：φ 自治化（週期閘 + 光滑階梯 + 真自治向量場字面見證）

**L3 主 crux**（`docs/GPAC_ROADMAP.md`；M41/M42/`BRICK6_DECISION` 曾標「φ 自治化 = 多月牆」——
**本磚修正此難度誤判**）。把 M40-43 的**時變**窗 `φ(t)=deriv smoothTransition(t−k)` 換成**自治**：
加相位變數 `θ`、`θ̇=1`（懸掛），閘 = `θ` 的**週期光滑函數**。

## 核心構造（全顯式、零 FTC、零 MeasureTheory、零商空間、零無限和）

- `φ₀ := deriv smoothTransition`；**邊界精確消沒**：`φ₀=0` 於 `x<0`（`eventuallyEq`）、`x>1`、
  **及 `x=1` 邊界點**（`φ₀_at_one`，連續性 + 單側極限 `tendsto_nhds_unique`）。
- **週期閘** `clockGate θ := φ₀(Int.fract θ)`（period 1）。**光滑性 = 局部兩項和技巧**：於開區間
  `(n−1,n+1)` 上 `clockGate = φ₀(θ−(n−1)) + φ₀(θ−n)`（兩項互斥觸零、逐點案例）——此局部式是
  **全域** C^∞ 閉式 ⟹ `ContDiffAt` 處處 ⟹ `ContDiff`。
- **光滑階梯** `clockStair θ := smoothTransition(Int.fract θ) + ⌊θ⌋` = `clockGate` 的**顯式反導數**：
  **`clockStair_hasDerivAt : ∀ θ, HasDerivAt clockStair (clockGate θ) θ`**（逐點、非 a.e.、零 FTC）。
- **★L3 HEADLINE★** `autoSol_isSolution`：`(Y,Θ)` 滿足
  `HasDerivAt (autoSol …) (autoField b C (autoSol … t)) t`，其中
  **`autoField (y,θ) = (−C·clockGate θ·(y−b), 1)` 只依賴狀態**——真自治的**字面見證**，且解
  **完全顯式閉式**（`targetingGatedSol` 餵 `Φ(t):=clockStair(θ₀+t)−clockStair θ₀`）。
  `autoField_contDiff`：向量場 **C^∞**。

## ★誠實範圍（禁 overclaim）★

- 本磚**只**清償「非自治（外源時鐘）」這一 caveat（M42 檔頭 (b)）——**單暫存器**版。leapfrog 兩暫存器
  自治耦合（`(y₁,y₂,θ)` 3D、HOLD 需 **period-2** 閘）= 下一磚（工作量 ≈ M42、非新難度）；N 步自治
  串接（M43 的相位版）再下一磚。
- **完全不動 σ**：不解 Wall A/B/C（σ 具體化/tube/re-rounding 已由 G4-G5 處理其玩具版，正交）。
  **禁**從本磚宣稱線三 undecidability。
- period-1 閘在每窗**無內部平坦段**（HOLD 需 period-2 版、後續磚）；`clockGate ≥ 0` 未證（未需）。
- C^∞ 非 analytic（承 M46-50）；量化導數界仍無（`deriv smoothTransition` 無 mathlib 界、M45 已標）。
-/

namespace FluidTuring

open Real Filter Topology

/-! ## φ₀ 邊界精確消沒 -/

/-- `φ₀ = deriv smoothTransition` 於負半軸恰 0（局部恆 0）。 -/
theorem φ₀_neg {x : ℝ} (h : x < 0) : deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [heq.deriv_eq]; exact deriv_const x 0

/-- `φ₀` 於 `x > 1` 恰 0（局部恆 1）。 -/
theorem φ₀_gt_one {x : ℝ} (h : 1 < x) : deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  rw [heq.deriv_eq]; exact deriv_const x 1

/-- `φ₀` 是 C^∞（C^∞ 函數的導數，`contDiff_infty_iff_deriv`）。 -/
theorem φ₀_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2

/-- `φ₀` 連續。 -/
theorem φ₀_continuous : Continuous (deriv Real.smoothTransition) :=
  φ₀_contDiff.continuous

/-- **邊界精確**：`φ₀ 1 = 0`（連續性 + 右側極限唯一）。 -/
theorem φ₀_at_one : deriv Real.smoothTransition 1 = 0 := by
  have h1 : Tendsto (deriv Real.smoothTransition) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (deriv Real.smoothTransition 1)) :=
    (φ₀_continuous.continuousAt.continuousWithinAt).tendsto
  have h2 : Tendsto (deriv Real.smoothTransition) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (φ₀_gt_one hx).symm
  exact tendsto_nhds_unique h1 h2

/-- `1 ≤ x ⟹ φ₀ x = 0`（含邊界）。 -/
theorem φ₀_ge_one {x : ℝ} (h : 1 ≤ x) : deriv Real.smoothTransition x = 0 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq]; exact φ₀_at_one
  · exact φ₀_gt_one hlt

/-! ## 週期閘 + 光滑階梯（局部兩項和技巧） -/

/-- **週期閘**（period 1）：`clockGate θ = φ₀(fract θ)`。 -/
noncomputable def clockGate (θ : ℝ) : ℝ := deriv Real.smoothTransition (Int.fract θ)

/-- **光滑階梯**：`clockStair θ = smoothTransition(fract θ) + ⌊θ⌋`（`clockGate` 的顯式反導數）。 -/
noncomputable def clockStair (θ : ℝ) : ℝ := Real.smoothTransition (Int.fract θ) + (⌊θ⌋ : ℝ)

/-- **閘的局部兩項和**：於 `(n−1, n+1)` 上 `clockGate = φ₀(θ−(n−1)) + φ₀(θ−n)`（兩項互斥觸零）。 -/
theorem clockGate_eq_local (n : ℤ) (θ : ℝ) (hθ : θ ∈ Set.Ioo ((n : ℝ) - 1) ((n : ℝ) + 1)) :
    clockGate θ = deriv Real.smoothTransition (θ - ((n : ℝ) - 1))
      + deriv Real.smoothTransition (θ - (n : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := hθ
  rcases lt_trichotomy θ (n : ℝ) with hlt | heq | hgt
  · have hfl : ⌊θ⌋ = n - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    have hfr : Int.fract θ = θ - ((n : ℝ) - 1) := by
      simp only [Int.fract, hfl]; push_cast; ring
    rw [clockGate, hfr, φ₀_neg (by linarith : θ - (n : ℝ) < 0), add_zero]
  · have e1 : θ - ((n : ℝ) - 1) = 1 := by rw [heq]; ring
    have e2 : θ - (n : ℝ) = 0 := by rw [heq]; ring
    rw [clockGate, e1, e2, φ₀_at_one, zero_add, heq, Int.fract_intCast]
  · have hfl : ⌊θ⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : Int.fract θ = θ - (n : ℝ) := by
      simp only [Int.fract, hfl]
    rw [clockGate, hfr, φ₀_gt_one (by linarith : 1 < θ - ((n : ℝ) - 1)), zero_add]

/-- 階梯於整數恰 = 該整數（downstream 串接錨點）。 -/
theorem clockStair_intCast (n : ℤ) : clockStair (n : ℝ) = (n : ℝ) := by
  rw [clockStair, Int.fract_intCast, Real.smoothTransition.zero, Int.floor_intCast, zero_add]

/-- **階梯的局部兩項和**：於 `(n−1, n+1)` 上
`clockStair = smoothTransition(θ−(n−1)) + smoothTransition(θ−n) + (n−1)`。 -/
theorem clockStair_eq_local (n : ℤ) (θ : ℝ) (hθ : θ ∈ Set.Ioo ((n : ℝ) - 1) ((n : ℝ) + 1)) :
    clockStair θ = Real.smoothTransition (θ - ((n : ℝ) - 1))
      + Real.smoothTransition (θ - (n : ℝ)) + ((n : ℝ) - 1) := by
  obtain ⟨hlo, hhi⟩ := hθ
  rcases lt_trichotomy θ (n : ℝ) with hlt | heq | hgt
  · have hfl : ⌊θ⌋ = n - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    have hfr : Int.fract θ = θ - ((n : ℝ) - 1) := by
      simp only [Int.fract, hfl]; push_cast; ring
    rw [clockStair, hfr,
      Real.smoothTransition.zero_of_nonpos (by linarith : θ - (n : ℝ) ≤ 0), hfl]
    push_cast; ring
  · subst heq
    have e1 : (n : ℝ) - ((n : ℝ) - 1) = 1 := by ring
    have e2 : (n : ℝ) - (n : ℝ) = 0 := by ring
    rw [clockStair_intCast, e1, e2, Real.smoothTransition.one, Real.smoothTransition.zero]
    ring
  · have hfl : ⌊θ⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hfr : Int.fract θ = θ - (n : ℝ) := by
      simp only [Int.fract, hfl]
    rw [clockStair, hfr,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ θ - ((n : ℝ) - 1)), hfl]
    ring

/-- 每點都落在 `(⌊θ⌋−1, ⌊θ⌋+1)`。 -/
theorem mem_Ioo_floor (θ : ℝ) :
    θ ∈ Set.Ioo (((⌊θ⌋ : ℤ) : ℝ) - 1) (((⌊θ⌋ : ℤ) : ℝ) + 1) :=
  ⟨by linarith [Int.floor_le θ], by linarith [Int.lt_floor_add_one θ]⟩

/-- **週期閘 C^∞**（局部兩項和 ⟹ `ContDiffAt` 處處）。 -/
theorem clockGate_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) clockGate := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  set n : ℤ := ⌊θ⌋ with hn
  have hmem := mem_Ioo_floor θ
  have hloc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => deriv Real.smoothTransition (u - ((n : ℝ) - 1))
        + deriv Real.smoothTransition (u - (n : ℝ))) := by
    exact (φ₀_contDiff.comp (by fun_prop)).add (φ₀_contDiff.comp (by fun_prop))
  apply hloc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
  exact clockGate_eq_local n u hu

/-- **★階梯 = 閘的顯式反導數（逐點、零 FTC）★**：`∀ θ, HasDerivAt clockStair (clockGate θ) θ`。 -/
theorem clockStair_hasDerivAt (θ : ℝ) : HasDerivAt clockStair (clockGate θ) θ := by
  set n : ℤ := ⌊θ⌋ with hn
  have hmem := mem_Ioo_floor θ
  have h1 := windowΦ_hasDerivAt ((n : ℝ) - 1) θ
  have h2 := windowΦ_hasDerivAt (n : ℝ) θ
  have hloc : HasDerivAt
      (fun u => Real.smoothTransition (u - ((n : ℝ) - 1))
        + Real.smoothTransition (u - (n : ℝ)) + ((n : ℝ) - 1))
      (deriv Real.smoothTransition (θ - ((n : ℝ) - 1))
        + deriv Real.smoothTransition (θ - (n : ℝ))) θ :=
    (h1.add h2).add_const _
  have hval : deriv Real.smoothTransition (θ - ((n : ℝ) - 1))
      + deriv Real.smoothTransition (θ - (n : ℝ)) = clockGate θ :=
    (clockGate_eq_local n θ hmem).symm
  rw [← hval]
  apply hloc.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
  exact clockStair_eq_local n u hu

/-! ## ★L3 HEADLINE：真自治向量場 + 顯式閉式解★ -/

/-- **自治向量場**：`autoField (y,θ) = (−C·clockGate θ·(y−b), 1)`——**只依賴狀態 `(y,θ)`、不依賴
時間**。 -/
noncomputable def autoField (b C : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (-C * clockGate p.2 * (p.1 - b), 1)

/-- **顯式閉式解**：`autoSol t = (targetingGatedSol …（Φ = 階梯差）, θ₀ + t)`。 -/
noncomputable def autoSol (y₀ b C θ₀ : ℝ) : ℝ → ℝ × ℝ :=
  fun t => (targetingGatedSol y₀ b C (fun s => clockStair (θ₀ + s) - clockStair θ₀) t, θ₀ + t)

/-- **★L3 HEADLINE：真自治字面見證★**：顯式閉式解真滿足自治向量場——
`HasDerivAt (autoSol …) (autoField b C (autoSol … t)) t`。右邊 `autoField` 只吃**狀態**。 -/
theorem autoSol_isSolution (y₀ b C θ₀ t : ℝ) :
    HasDerivAt (autoSol y₀ b C θ₀) (autoField b C (autoSol y₀ b C θ₀ t)) t := by
  have hθ : HasDerivAt (fun s : ℝ => θ₀ + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add θ₀
  have hstair : HasDerivAt (fun s => clockStair (θ₀ + s)) (clockGate (θ₀ + t)) t :=
    HasDerivAt.comp_const_add θ₀ t (clockStair_hasDerivAt (θ₀ + t))
  have hΦ : HasDerivAt (fun s => clockStair (θ₀ + s) - clockStair θ₀)
      (clockGate (θ₀ + t)) t := hstair.sub_const _
  have hy := targetingGatedSol_hasDerivAt y₀ b C
    (fun s => clockStair (θ₀ + s) - clockStair θ₀) (clockGate (θ₀ + t)) t hΦ
  exact hy.prodMk hθ

/-- **自治向量場 C^∞**（`clockGate_contDiff` + prod 組合）。 -/
theorem autoField_contDiff (b C : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (autoField b C) := by
  unfold autoField
  refine ContDiff.prodMk ?_ contDiff_const
  exact (contDiff_const.mul (clockGate_contDiff.comp contDiff_snd)).mul
    (contDiff_fst.sub contDiff_const)

end FluidTuring
