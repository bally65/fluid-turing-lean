import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Module 17 — TM2→BitTM 帶佈局基元（(ii) B2a 第一塊）

依 B2 對抗設計裁決（`docs/UNDECIDABILITY_LINE.md`）：不可逆掃描解釋器 `M_tr` 的
**帶佈局** = 把 TM2 的 4 個堆疊 + 標記軌 + home + 垃圾 交錯到一條 `ℤ → Bool` 位帶。

本塊 = 該佈局的**基元**：`multiTrackEnc`——任意 `P = n+1` 條軌 `Fin (n+1) → ℤ → Bool`
交錯（軌 `t` 佔位址 `≡ t (mod P)`）成單一 `ℤ → Bool`，含 readback + 單射。泛化已證的
`M3e.fixedEnc4`（P=4 硬編碼）到任意軌數（B2 佈局需 ~11–12 軌）。純佈局、不碰 TM2/Γ' 特性。
-/

namespace FluidTuring

/-- 位址 `i` 落在哪條軌（`i mod P`，`P = n+1`）。 -/
def trackIdx {n : ℕ} (i : ℤ) : Fin (n + 1) :=
  ⟨(i % (n + 1)).toNat, by
    have h1 : (0 : ℤ) < (n : ℤ) + 1 := by positivity
    have hlt := Int.emod_lt_of_pos i h1
    have hnn := Int.emod_nonneg i (ne_of_gt h1)
    omega⟩

/-- **P 軌交錯編碼**：軌 `t` 的內容 `tr t` 放在位址 `≡ t (mod P)`、第 `i / P` 格。
泛化 `M3e.fixedEnc4`（P=4）。 -/
def multiTrackEnc {n : ℕ} (tr : Fin (n + 1) → ℤ → Bool) (i : ℤ) : Bool :=
  tr (trackIdx i) (i / (n + 1))

/-- **readback**：第 `k` 格軌 `t` 的位址 = `P*k + t`，取回 `tr t k`。 -/
theorem multiTrackEnc_get {n : ℕ} (tr : Fin (n + 1) → ℤ → Bool) (t : Fin (n + 1)) (k : ℤ) :
    multiTrackEnc tr ((n + 1) * k + (t : ℤ)) = tr t k := by
  have hP : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have htlt : (t : ℤ) < (n : ℤ) + 1 := by exact_mod_cast t.isLt
  have htnn : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg _
  have hmod : ((n + 1) * k + (t : ℤ)) % ((n : ℤ) + 1) = (t : ℤ) := by
    rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt htnn htlt]
  have hdiv : ((n + 1) * k + (t : ℤ)) / ((n : ℤ) + 1) = k := by
    rw [add_comm, Int.add_mul_ediv_left _ _ (ne_of_gt hP), Int.ediv_eq_zero_of_lt htnn htlt,
      zero_add]
  have hidx : trackIdx ((n + 1) * k + (t : ℤ)) = t := by
    apply Fin.ext
    change (((n + 1) * k + (t : ℤ)) % (n + 1)).toNat = (t : ℕ)
    rw [hmod, Int.toNat_natCast]
  unfold multiTrackEnc
  rw [hidx, hdiv]

/-- **單射**：P 軌各自取回 ⟹ 軌族由編碼帶唯一決定。 -/
theorem multiTrackEnc_injective {n : ℕ} {tr tr' : Fin (n + 1) → ℤ → Bool}
    (h : multiTrackEnc tr = multiTrackEnc tr') : tr = tr' := by
  funext t k
  have := congrFun h ((n + 1) * k + (t : ℤ))
  rwa [multiTrackEnc_get, multiTrackEnc_get] at this

/-! ## Γ' 位編碼：TM2 堆疊字母 `Γ'`（4 符號）↔ 2 位元

mathlib `Turing.PartrecToTM2.Γ'` = `{consₗ, cons, bit0, bit1}`（4 符號、Fintype）。
編碼成 2 位元供帶佈局（每堆疊格 = 2 個 Bool 軌）。 -/

open Turing.PartrecToTM2 in
/-- Γ' → 2 位元。 -/
def Γ'toBits : Γ' → Bool × Bool
  | .consₗ => (false, false)
  | .cons  => (false, true)
  | .bit0  => (true, false)
  | .bit1  => (true, true)

open Turing.PartrecToTM2 in
/-- 2 位元 → Γ'（手寫逆）。 -/
def bitsToΓ' : Bool × Bool → Γ'
  | (false, false) => .consₗ
  | (false, true)  => .cons
  | (true, false)  => .bit0
  | (true, true)   => .bit1

open Turing.PartrecToTM2 in
/-- **Γ' ≃ 2 位元**（TM2 堆疊字母的位帶編碼）。 -/
def Γ'BitEquiv : Γ' ≃ (Bool × Bool) where
  toFun := Γ'toBits
  invFun := bitsToΓ'
  left_inv g := by cases g <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

end FluidTuring
