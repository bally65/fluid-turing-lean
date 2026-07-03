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

end FluidTuring
