import FluidTuringLean.M2_Interpreter

/-!
# Module 3 — 康托爾編碼與圖靈同構

把可數的機器組態空間單射嵌入 `ℝ`，並把離散轉移函數共軛到實數上的函數：

* `encodeNat n = 3⁻ⁿ`：嚴格遞減故單射；像集堆積點只有 `0`（不在像內），
  故像集內每點都是孤立點。
* `encodeConfig`：任何 `Encodable` 組態型別經 `Encodable.encode` 嵌入 `ℝ`。
* `exists_step_conjugate`：任何轉移函數 `step : Γ → Γ` 都存在 `F : ℝ → ℝ`
  使 `F ∘ encode = encode ∘ step`（圖靈同構的實數側）。

**誠實備註**：在這個編碼下像集每點孤立，故「`F` 在像集上連續」不具內容
（任何函數限制在離散集上都連續）。有數學內容的版本是把編碼取值在
康托爾集（無孤立點）並要求 `F` 在其上連續 —— 那是 generalized shift
（Moore 1990）的核心，屬後續工作，不在本檔佯稱完成。

本檔零 sorry。
-/

namespace FluidTuring

/-- 自然數編碼進 `ℝ`：`n ↦ 3⁻ⁿ`。 -/
noncomputable def encodeNat (n : ℕ) : ℝ := (3 : ℝ)⁻¹ ^ n

theorem strictAnti_encodeNat : StrictAnti encodeNat :=
  pow_right_strictAnti₀ (by norm_num) (by norm_num)

theorem encodeNat_injective : Function.Injective encodeNat :=
  strictAnti_encodeNat.injective

theorem encodeNat_pos (n : ℕ) : 0 < encodeNat n := by
  unfold encodeNat; positivity

/-- 可數組態空間嵌入 `ℝ`。`Γ` 是機器組態型別（狀態 × 紙帶），
只要它 `Encodable`（mathlib 圖靈機組態皆可數）。 -/
noncomputable def encodeConfig {Γ : Type*} [Encodable Γ] (c : Γ) : ℝ :=
  encodeNat (Encodable.encode c)

theorem encodeConfig_injective {Γ : Type*} [Encodable Γ] :
    Function.Injective (encodeConfig (Γ := Γ)) :=
  encodeNat_injective.comp Encodable.encode_injective

/-- 圖靈同構（實數側）：任何離散轉移 `step` 都能共軛到 `ℝ` 上的函數 `F`，
使編碼圖交換：`F (encode c) = encode (step c)`。 -/
theorem exists_step_conjugate {Γ : Type*} [Encodable Γ] (step : Γ → Γ) :
    ∃ F : ℝ → ℝ, ∀ c : Γ, F (encodeConfig c) = encodeConfig (step c) := by
  classical
  refine ⟨fun x ↦
    if h : ∃ c : Γ, encodeConfig c = x then encodeConfig (step h.choose) else 0,
    fun c ↦ ?_⟩
  have h : ∃ c' : Γ, encodeConfig c' = encodeConfig c := ⟨c, rfl⟩
  simp only [dif_pos h]
  exact congrArg (fun z ↦ encodeConfig (step z)) (encodeConfig_injective h.choose_spec)

/-! ## 真康托爾集編碼（升級層）

上面 `encodeNat` 的像集每點孤立，連續性在其上不具內容。本節做**有內容**的
版本：把整個布林序列空間 `ℕ → Bool`（緊緻、無孤立點）以三進位嵌入 `ℝ`，
得到經典康托爾集。單射、連續、閉嵌入、以及 shift 動力學的連續共軛全部證出
—— 這是 generalized shift（Moore 1990）路線的解析核心。 -/

/-- 康托爾編碼的第 `n` 位項：`s n = true` 貢獻 `2·3⁻⁽ⁿ⁺¹⁾`，否則 `0`。 -/
noncomputable def cantorTerm (s : ℕ → Bool) (n : ℕ) : ℝ :=
  (if s n then 2 else 0) * (3 : ℝ)⁻¹ ^ (n + 1)

theorem cantorTerm_nonneg (s : ℕ → Bool) (n : ℕ) : 0 ≤ cantorTerm s n := by
  unfold cantorTerm; split <;> positivity

theorem cantorTerm_le (s : ℕ → Bool) (n : ℕ) :
    cantorTerm s n ≤ 2 * (3 : ℝ)⁻¹ ^ (n + 1) := by
  unfold cantorTerm
  have hpos : (0 : ℝ) ≤ (3 : ℝ)⁻¹ ^ (n + 1) := by positivity
  split <;> nlinarith

theorem summable_cantorTerm (s : ℕ → Bool) : Summable (cantorTerm s) := by
  have hgeom : Summable fun n : ℕ ↦ 2 * (3 : ℝ)⁻¹ ^ (n + 1) :=
    ((summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).mul_left (2 * (3 : ℝ)⁻¹)).congr fun n ↦ by ring
  exact Summable.of_nonneg_of_le (cantorTerm_nonneg s) (cantorTerm_le s) hgeom

/-- 康托爾編碼：`s ↦ Σ (s n) · 2 / 3^(n+1)`，像集 ⊆ 經典康托爾集 ⊆ [0,1]。 -/
noncomputable def cantorEncode (s : ℕ → Bool) : ℝ := ∑' n, cantorTerm s n

/-- 尾和上界：`Σ_{n≥k} ≤ 3⁻ᵏ`。 -/
theorem cantorTail_le (s : ℕ → Bool) (k : ℕ) :
    ∑' n, cantorTerm s (n + k) ≤ (3 : ℝ)⁻¹ ^ k := by
  have hgeom : Summable fun n : ℕ ↦ 2 * (3 : ℝ)⁻¹ ^ (n + k + 1) :=
    ((summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).mul_left (2 * (3 : ℝ)⁻¹ ^ (k + 1))).congr fun n ↦ by ring
  calc ∑' n, cantorTerm s (n + k)
      ≤ ∑' n, 2 * (3 : ℝ)⁻¹ ^ (n + k + 1) :=
        ((summable_cantorTerm s).comp_injective
          (add_left_injective k)).tsum_le_tsum
          (fun n ↦ cantorTerm_le s (n + k)) hgeom
  _ = 2 * (3 : ℝ)⁻¹ ^ (k + 1) * ∑' n, (3 : ℝ)⁻¹ ^ n := by
        rw [← tsum_mul_left]
        congr 1 with n
        ring
  _ = 2 * (3 : ℝ)⁻¹ ^ (k + 1) * (1 - (3 : ℝ)⁻¹)⁻¹ := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  _ = (3 : ℝ)⁻¹ ^ k := by
        have h32 : ((1 : ℝ) - 3⁻¹)⁻¹ = 3 / 2 := by norm_num
        rw [h32, pow_succ]
        ring

theorem cantorTail_nonneg (s : ℕ → Bool) (k : ℕ) :
    0 ≤ ∑' n, cantorTerm s (n + k) :=
  tsum_nonneg fun n ↦ cantorTerm_nonneg s (n + k)

/-- 反對稱核心：低位全同、第 `k` 位 `s` 讀 0 而 `s'` 讀 1 ⟹ 編碼嚴格變小。
（首異位的 `2/3^(k+1)` 差距吃掉整條尾和 `≤ 1/3^(k+1)`。） -/
theorem cantorEncode_lt {s s' : ℕ → Bool} {k : ℕ}
    (hagree : ∀ i < k, s i = s' i) (hs : s k = false) (hs' : s' k = true) :
    cantorEncode s < cantorEncode s' := by
  have hsplit : ∀ u : ℕ → Bool,
      cantorEncode u = ∑ i ∈ Finset.range (k + 1), cantorTerm u i +
        ∑' n, cantorTerm u (n + (k + 1)) := fun u ↦
    ((summable_cantorTerm u).sum_add_tsum_nat_add (k + 1)).symm
  rw [hsplit s, hsplit s']
  have hsum : ∀ u : ℕ → Bool, ∑ i ∈ Finset.range (k + 1), cantorTerm u i =
      ∑ i ∈ Finset.range k, cantorTerm u i + cantorTerm u k := fun u ↦
    Finset.sum_range_succ _ k
  rw [hsum s, hsum s']
  have heq : ∑ i ∈ Finset.range k, cantorTerm s i =
      ∑ i ∈ Finset.range k, cantorTerm s' i :=
    Finset.sum_congr rfl fun i hi ↦ by
      unfold cantorTerm; rw [hagree i (Finset.mem_range.1 hi)]
  rw [heq]
  have hks : cantorTerm s k = 0 := by unfold cantorTerm; rw [hs]; simp
  have hks' : cantorTerm s' k = 2 * (3 : ℝ)⁻¹ ^ (k + 1) := by
    unfold cantorTerm; rw [hs']; simp
  rw [hks, hks']
  have htail_s := cantorTail_le s (k + 1)
  have htail_s' := cantorTail_nonneg s' (k + 1)
  have hpow : (0 : ℝ) < (3 : ℝ)⁻¹ ^ (k + 1) := by positivity
  linarith

/-- 康托爾編碼單射。 -/
theorem cantorEncode_injective : Function.Injective cantorEncode := by
  intro s s' hss'
  by_contra hne
  have hex : ∃ n, s n ≠ s' n := Function.ne_iff.1 hne
  set k := Nat.find hex with hk
  have hdiff : s k ≠ s' k := Nat.find_spec hex
  have hagree : ∀ i < k, s i = s' i := fun i hi ↦ by
    by_contra hcon
    exact absurd (Nat.find_min' hex hcon) (not_le.2 hi)
  cases hsk : s k <;> cases hs'k : s' k
  · exact hdiff (hsk.trans hs'k.symm)
  · exact absurd hss' (ne_of_lt (cantorEncode_lt hagree hsk hs'k))
  · exact absurd hss'.symm
      (ne_of_lt (cantorEncode_lt (fun i hi ↦ (hagree i hi).symm) hs'k hsk))
  · exact hdiff (hsk.trans hs'k.symm)

/-- 康托爾編碼連續（`ℕ → Bool` 取乘積拓撲；Weierstrass M-判別法）。 -/
theorem continuous_cantorEncode : Continuous cantorEncode := by
  apply continuous_tsum (u := fun n ↦ 2 * (3 : ℝ)⁻¹ ^ (n + 1))
  · intro n
    have h1 : Continuous fun s : ℕ → Bool ↦ (if s n then (2 : ℝ) else 0) :=
      (continuous_of_discreteTopology (f := fun b : Bool ↦ if b then (2 : ℝ) else 0)).comp
        (continuous_apply n)
    exact h1.mul continuous_const
  · have := (summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).mul_left (2 * (3 : ℝ)⁻¹)
    refine this.congr fun n ↦ ?_
    ring
  · intro n s
    rw [Real.norm_eq_abs, abs_of_nonneg (cantorTerm_nonneg s n)]
    exact cantorTerm_le s n

/-- 康托爾編碼是閉嵌入：緊緻定義域 + T2 值域 + 連續單射。
像集是 `ℝ` 中的緊緻無孤立點集（經典康托爾集），拓撲結構整包保留。 -/
theorem isClosedEmbedding_cantorEncode :
    Topology.IsClosedEmbedding cantorEncode :=
  continuous_cantorEncode.isClosedEmbedding cantorEncode_injective

/-- 單邊 shift：`(shift s) n = s (n+1)`。 -/
def boolShift (s : ℕ → Bool) : ℕ → Bool := fun n ↦ s (n + 1)

theorem continuous_boolShift : Continuous boolShift :=
  continuous_pi fun n ↦ continuous_apply (n + 1)

/-- **有內容的圖靈同構**：shift 動力學共軛到 `ℝ` 上一個在康托爾集上
「連續」的函數 —— 對比 `exists_step_conjugate`（孤立點集上連續性免費），
這裡像集無孤立點，連續性是真命題，由閉嵌入的同胚結構得到。 -/
theorem exists_continuous_shift_conjugate :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.range cantorEncode) ∧
      ∀ s : ℕ → Bool, F (cantorEncode s) = cantorEncode (boolShift s) := by
  classical
  have hemb := isClosedEmbedding_cantorEncode.toIsEmbedding
  let e : (ℕ → Bool) ≃ₜ Set.range cantorEncode := hemb.toHomeomorph
  refine ⟨fun x ↦ if hx : x ∈ Set.range cantorEncode then
    cantorEncode (boolShift (e.symm ⟨x, hx⟩)) else 0, ?_, fun s ↦ ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.range cantorEncode)
        (fun x ↦ if hx : x ∈ Set.range cantorEncode then
          cantorEncode (boolShift (e.symm ⟨x, hx⟩)) else 0) =
        fun y : Set.range cantorEncode ↦
          cantorEncode (boolShift (e.symm y)) := by
      funext y
      simp [Set.restrict, y.2]
    rw [this]
    exact continuous_cantorEncode.comp
      (continuous_boolShift.comp (e.symm.continuous))
  · have hmem : cantorEncode s ∈ Set.range cantorEncode := ⟨s, rfl⟩
    simp only [dif_pos hmem]
    congr 1
    have : e.symm ⟨cantorEncode s, hmem⟩ = s := by
      apply cantorEncode_injective
      have := e.apply_symm_apply ⟨cantorEncode s, hmem⟩
      calc cantorEncode (e.symm ⟨cantorEncode s, hmem⟩)
          = ((e (e.symm ⟨cantorEncode s, hmem⟩) : Set.range cantorEncode) : ℝ) := rfl
      _ = ((⟨cantorEncode s, hmem⟩ : Set.range cantorEncode) : ℝ) := by rw [this]
    rw [this]

end FluidTuring
