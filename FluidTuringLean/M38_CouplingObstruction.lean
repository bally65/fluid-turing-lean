import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Module 38 — 方向一 Brick C 的**結構障礙**（精確化 + 可形式化的乾淨半邊）

**背景**：方向一想把「字面 blowup」焊成單一**自治**耦合向量場 `z' = a(t) z²`，`a(t) = g(X(t))`
（X = 懸掛流、g = 停機偵測器）。Brick A+B（M35）已給真·耦合 Riccati 爆破核心；缺口 = Brick C
（造合法的 `g`）。

**earlier 障礙（測度零）有 workaround**：曾記「懸掛軌道只在整數時刻打進停機切片 → 測度零 →
∫g=0」。但可**加厚**停機區為整條纖維 `{base ∈ H*}`（H* = 最終停機盆）。因 H* 在 `e = bennettHomeo`
（雙射）下**不變**，一旦停機軌道**其後所有時間**都在加厚區 = 正測度 → ∫g 真累積。故測度零**非**真牆。

**真·結構障礙（更深、本模組主旨）**：合法的**自治**耦合要 `g` **連續**（真光滑 ODE 的係數）；
**連續的 `g` 只能偵測 clopen 集**（本模組 `continuous_detector_isClopen` 機器證）；但停機盆 H*
是 **Σ₁（r.e.）而非遞迴**（M37 `fluid_reach_full_characterization`：REPred 但 ¬Computable）
⟹ 在 Cantor 組態空間中 **H* 非 clopen** ⟹ **無連續 `g` 偵測 H*** ⟹ 自治「狀態讀出」耦合
**結構不可能**。唯一逃逸 = 讓**動力學本身計算**（Graça/Huynh：向量場 analog 模擬 TM，非靜態讀出）
= mathlib 無、**paper-blocked**。

本模組形式化障礙的**乾淨半邊**（連續 2 值偵測器 ⟹ clopen）；另半邊「H* 非 clopen（Σ₁\Δ₁ +
Cantor 拓撲）」= 精確的 paper-blocked 前沿，明寫於此。
-/

namespace FluidTuring

/-- **★耦合障礙的乾淨半邊★**：若 `g : X → ℝ` **連續**、在 `Basin` 上取值 1、補集上取值 0
（= 一個「連續狀態讀出」的停機偵測器），則 `Basin` 必為 **clopen**（開且閉）。

⟹ 反面：**非 clopen 的集合無連續 2 值偵測器**。停機盆 H* 是 Σ₁ 非遞迴（M37）→ 在 Cantor
組態空間非 clopen → **無連續 `g` 可作其自治耦合係數**。這是方向一 Brick C 的**真·結構障礙**
（比測度零深、無 workaround）。 -/
theorem continuous_detector_isClopen {X : Type*} [TopologicalSpace X] (Basin : Set X)
    (g : X → ℝ) (hg : Continuous g)
    (h1 : ∀ x ∈ Basin, g x = 1) (h0 : ∀ x ∉ Basin, g x = 0) :
    IsClopen Basin := by
  have hopen : IsOpen Basin := by
    have hset : Basin = g ⁻¹' Set.Ioi (1 / 2 : ℝ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor
      · intro hx; rw [h1 x hx]; norm_num
      · intro hx; by_contra hnb; rw [h0 x hnb] at hx; norm_num at hx
    rw [hset]; exact isOpen_Ioi.preimage hg
  have hclosed : IsClosed Basin := by
    have hset : Basinᶜ = g ⁻¹' Set.Iio (1 / 2 : ℝ) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio]
      constructor
      · intro hx; rw [h0 x hx]; norm_num
      · intro hx hb; rw [h1 x hb] at hx; norm_num at hx
    rw [← compl_compl Basin, hset]
    exact (isOpen_Iio.preimage hg).isClosed_compl
  exact ⟨hclosed, hopen⟩

/-- **障礙的形狀（對偶陳述）**：非 clopen 集**沒有**連續 2 值偵測器。直接由
`continuous_detector_isClopen` 反證。應用：停機盆非 clopen ⟹ 無連續自治耦合係數。 -/
theorem no_continuous_detector_of_not_isClopen {X : Type*} [TopologicalSpace X] (Basin : Set X)
    (hnc : ¬ IsClopen Basin) :
    ¬ ∃ g : X → ℝ, Continuous g ∧ (∀ x ∈ Basin, g x = 1) ∧ (∀ x ∉ Basin, g x = 0) := by
  rintro ⟨g, hg, h1, h0⟩
  exact hnc (continuous_detector_isClopen Basin g hg h1 h0)

end FluidTuring
