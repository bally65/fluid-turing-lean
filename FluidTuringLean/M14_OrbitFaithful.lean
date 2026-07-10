import FluidTuringLean.M13_SmoothSwitch
import FluidTuringLean.M10_BlowupUndecidable

/-!
# Module 14 — 軌道忠實性（(ii)：逆向「不停機 ⟹ 不爆」+ M10 實例化閉環）

M12/M13 給了「停機 ⟹ 耦合座標有限時間爆破」。**逆向**（不停機 ⟹ 觸發永不點火 ⟹
耦合座標恆 `1`、全域存在）需要 `Simulates` 沒給的：軌道不會**巧合**穿越編碼停機區。
本模組把該缺口分離成顯式不變量：

`OrbitFaithful`：從編碼組態出發的軌道**若打中編碼集、必打中正確的迭代**
`enc (step^[n] c)`。這是模擬層的幾何性質（懸掛構造的軌道結構給的），此處當
明寫假設（對 `suspension_flow_simulates` 的實例證明 = 未來工作、誠實標示）。

**成果鏈**：
1. `neverHalts_never_reaches`：忠實 + 永不停機 ⟹ 軌道永不進停機區（觸發永不點火、
   `z ≡ 1` 全域——「不爆」半邊）。
2. `orbitReaches_iff_halts`：忠實 + 停機區吸收（真 TM 停機態是 fixpoint）⟹
   **可達 ⟺ 停機**（M9 給 ⟸、忠實給 ⟹）。
3. **★`coupled_blowup_undecidable`★**：以 2 餵 M10 ⟹ **耦合家族的爆破觸發不可判定**
   ——M9（可達）→ M12/13（觸發爆破）→ M10（不可判定）**整環第一次以定理閉合**。
   剩餘未形式化物理全部收進兩條顯式假設：`OrbitFaithful`（模擬層幾何）+
   `huniv`（通用機器、mathlib TM 理論可接但接線是工作）。
-/

namespace FluidTuring

open Nat.Partrec

/-- **軌道忠實性**：從編碼組態出發的軌道，任何正時間若落在編碼集內，落點必為
某個**正確迭代**的編碼。懸掛構造的軌道結構性質、此處為明寫假設。 -/
def OrbitFaithful {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M)
    {Γ : Type*} (step : Γ → Γ) (enc : Γ → M) : Prop :=
  ∀ (c : Γ) (t : ℝ), 0 < t → F.φ t (enc c) ∈ Set.range enc →
    ∃ n : ℕ, F.φ t (enc c) = enc (step^[n] c)

/-- **不停機 ⟹ 軌道永不進停機區**（觸發永不點火 ⟹ 耦合座標恆 `1`、全域存在
——「不爆」半邊）。 -/
theorem neverHalts_never_reaches {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M}
    (hsim : Simulates F step enc) (hfaith : OrbitFaithful F step enc)
    (c : Γ) (H : Set Γ) (hnever : ∀ k : ℕ, step^[k] c ∉ H) :
    ¬ OrbitReaches F (enc c) (enc '' H) := by
  rintro ⟨t, ht, hmem⟩
  obtain ⟨h', hh', hEq⟩ := hmem
  obtain ⟨n, hn⟩ := hfaith c t ht ⟨h', hEq⟩
  have hnh : step^[n] c = h' := hsim.1 (by rw [← hn]; exact hEq.symm)
  exact hnever n (hnh ▸ hh')

/-- **可達 ⟺ 停機**：忠實性 + 停機區吸收（`step` 保 `H`，真 TM 停機態是 fixpoint）下，
軌道抵達編碼停機區 ⟺ 離散計算停機。⟸ 是 M9、⟹ 是忠實性 + 單射。 -/
theorem orbitReaches_iff_halts {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M}
    (hsim : Simulates F step enc) (hfaith : OrbitFaithful F step enc)
    (c : Γ) (H : Set Γ) (hH : c ∈ H → step c ∈ H) :
    OrbitReaches F (enc c) (enc '' H) ↔ ∃ k : ℕ, step^[k + 1] c ∈ H := by
  constructor
  · rintro ⟨t, ht, hmem⟩
    obtain ⟨h', hh', hEq⟩ := hmem
    obtain ⟨n, hn⟩ := hfaith c t ht ⟨h', hEq⟩
    have hnH : step^[n] c ∈ H := by
      have hnh : step^[n] c = h' := hsim.1 (by rw [← hn]; exact hEq.symm)
      exact hnh ▸ hh'
    cases n with
    | zero =>
      simp only [Function.iterate_zero_apply] at hnH
      exact ⟨0, by simpa using hH hnH⟩
    | succ m => exact ⟨m, hnH⟩
  · rintro ⟨k, hk⟩
    exact halts_imp_orbitReaches hsim c H k hk

/-- **★耦合家族的爆破觸發不可判定★（M9 → M12/13 → M10 閉環）**：給定忠實模擬 +
吸收停機區 + 通用機器假設（`init code` 的計算停機 ⟺ `code.eval n` 有定義），則
「code 的耦合軌道觸發爆破」（= `OrbitReaches`，= M12/13 耦合座標於有限時間爆破的
充要條件）**無演算法可判定**。以 `orbitReaches_iff_halts` 餵 M10
`finite_time_blowup_undecidable`。

剩餘未形式化物理**全部**收在兩條顯式假設：`OrbitFaithful`（懸掛軌道幾何、對
`suspension_flow_simulates` 實例證明 = 未來工作）與 `huniv`（通用機器接線）。 -/
theorem coupled_blowup_undecidable {M : Type} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M}
    (hsim : Simulates F step enc) (hfaith : OrbitFaithful F step enc)
    (H : Set Γ) (init : Code → Γ) (hH : ∀ code : Code, init code ∈ H → step (init code) ∈ H)
    (n : ℕ)
    (huniv : ∀ code : Code, (∃ k : ℕ, step^[k + 1] (init code) ∈ H) ↔ (code.eval n).Dom) :
    ¬ ComputablePred fun code : Code =>
        ∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code)) ∈ enc '' H := by
  have hred : ∀ code : Code,
      (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code)) ∈ enc '' H) ↔ (code.eval n).Dom := by
    intro code
    rw [← huniv code]
    exact orbitReaches_iff_halts hsim hfaith (init code) H (hH code)
  exact finite_time_blowup_undecidable
    (fun code t ↦ F.φ t (enc (init code)))
    (fun traj ↦ ∃ t : ℝ, 0 < t ∧ traj t ∈ enc '' H) n hred

/-! ## 忠實性實例：懸掛流真的忠實（假設 ① 變定理）

`OrbitFaithful` 對 M6 實際構造的懸掛流**成立**：軌道 `φ t [c,0] = [c,t]` 打中切片
`{[γ,0]}` ⟺ M4 完整不變量 `torusRep = (e^⌊t⌋ x, fract t)` 逼出 `fract t = 0` ⟺ `t` 是
（正）整數 ⟺ 落點 = `[e^⌊t⌋ c, 0]` = **正確迭代的編碼**。幾何內容 = 懸掛構造的
纖維結構：切片只在整數時間被打中、打中即跳正確步數。 -/

/-- **★懸掛流忠實模擬★（`suspension_flow_simulates` 的加強版）**：緊空間自同胚的
懸掛流不只模擬（M6）、且**軌道忠實**（M14 假設 ① 對此構造成立）。與
`coupled_blowup_undecidable` 合用時，懸掛家族只剩 `huniv`（通用機器接線）一條假設。 -/
theorem suspension_flow_simulates_faithful {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (e : X ≃ₜ X) :
    ∃ (M : Type u) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (F : ContinuousFlowOn M) (enc : X → M),
      Simulates F (⇑e) enc ∧ OrbitFaithful F (⇑e) enc := by
  refine ⟨MappingTorus ⇑e, inferInstance, MappingTorus.compactSpace e.toEquiv,
    { φ := MappingTorus.suspFlow
      continuous := MappingTorus.continuous_suspFlow_uncurried e
      map_zero := MappingTorus.suspFlow_zero
      map_add := MappingTorus.suspFlow_add },
    fun x ↦ MappingTorus.mk ⇑e (x, 0),
    ⟨MappingTorus.mk_slice_injective e.toEquiv,
      fun c ↦ ⟨1, one_pos, MappingTorus.suspFlow_one_realizes c⟩⟩, ?_⟩
  intro c t ht hmem
  obtain ⟨γ, hγ⟩ := hmem
  have hφ : MappingTorus.suspFlow t (MappingTorus.mk ⇑e (c, 0))
      = MappingTorus.mk ⇑e (c, 0 + t) := MappingTorus.suspFlow_mk t c 0
  have hγ' : MappingTorus.mk ⇑e (γ, 0) = MappingTorus.mk ⇑e (c, 0 + t) := by
    rw [← hφ]; exact hγ
  have hrep := (MappingTorus.mk_eq_mk_iff e.toEquiv (γ, 0) (c, 0 + t)).1 hγ'
  simp only [MappingTorus.torusRep, Int.floor_zero, zpow_zero, Equiv.Perm.coe_one, id_eq,
    Int.fract_zero, zero_add] at hrep
  have hfr : Int.fract t = 0 := (Prod.ext_iff.mp hrep).2.symm
  have hteq0 : ((⌊t⌋ : ℤ) : ℝ) = t := by
    have haf := Int.fract_add_floor t
    rw [hfr] at haf
    linarith
  have hzpos : 0 < ⌊t⌋ := by
    have : (0 : ℝ) < ((⌊t⌋ : ℤ) : ℝ) := by rw [hteq0]; exact ht
    exact_mod_cast this
  refine ⟨⌊t⌋.toNat, ?_⟩
  have hcast : ((⌊t⌋.toNat : ℕ) : ℝ) = t := by
    have h1 : ((⌊t⌋.toNat : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hzpos.le
    rw [h1, hteq0]
  have hbridge : (e.toEquiv ^ ⌊t⌋.toNat) c = (⇑e)^[⌊t⌋.toNat] c :=
    congrFun (Equiv.Perm.coe_pow e.toEquiv ⌊t⌋.toNat) c
  calc MappingTorus.suspFlow t (MappingTorus.mk ⇑e (c, 0))
      = MappingTorus.mk ⇑e (c, 0 + t) := hφ
    _ = MappingTorus.mk ⇑e (c, 0 + ((⌊t⌋.toNat : ℕ) : ℝ)) := by rw [hcast]
    _ = MappingTorus.mk ⇑e ((e.toEquiv ^ ⌊t⌋.toNat) c, 0) :=
        MappingTorus.mk_add_nat e.toEquiv ⌊t⌋.toNat c 0
    _ = MappingTorus.mk ⇑e ((⇑e)^[⌊t⌋.toNat] c, 0) := by rw [hbridge]

end FluidTuring
