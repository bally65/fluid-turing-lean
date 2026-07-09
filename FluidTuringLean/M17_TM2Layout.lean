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

/-! ## 堆疊 → 軌：一個 TM2 堆疊 `List Γ'` 編碼成（內容軌 + 頂標記軌）

堆疊 `s`（bottom = cell 0、top = cell `len-1`、next-push = cell `len`）：
- **內容軌** `stackContent s`：cell `j` 放 `s[j]` 的 2 位（`Γ'BitEquiv`）。
- **頂標記軌** `stackMark s`：唯一 1 在 cell `len`（= 下次 push 位；空堆疊在 0）。
push = append（標記 `len → len+1`）、pop = dropLast（`len → len-1`）——皆有界局部編輯 +
標記移一格，正是不可逆解釋器 `M_tr` 的堆疊操作。 -/

/-- 頂標記軌：唯一 1 在 `len`（= 堆疊深度 / 下次 push 位）。 -/
def stackMark (len : ℕ) : ℤ → Bool := fun j ↦ decide (j = (len : ℤ))

theorem stackMark_self (len : ℕ) : stackMark len (len : ℤ) = true := by simp [stackMark]

theorem stackMark_ne (len : ℕ) {j : ℤ} (h : j ≠ (len : ℤ)) : stackMark len j = false := by
  simp [stackMark, h]

/-- push/pop 移標記一格（深度 ±1）。 -/
theorem stackMark_push (len : ℕ) : stackMark (len + 1) = stackMark len ∘ (· - 1) := by
  funext j
  simp only [stackMark, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  exact decide_eq_decide.mpr (by omega)

open Turing.PartrecToTM2 in
/-- 內容軌：cell `j` 放 `s[j]` 的 2 位（越界取 `consₗ`、被標記遮蔽）。 -/
def stackContent (s : List Γ') (j : ℤ) : Bool × Bool :=
  Γ'BitEquiv (s.getD j.toNat Γ'.consₗ)

open Turing.PartrecToTM2 in
/-- **內容 readback**（`j < len`）：取回 `s[j]`。 -/
theorem stackContent_get (s : List Γ') (j : ℕ) (h : j < s.length) :
    stackContent s (j : ℤ) = Γ'BitEquiv s[j] := by
  simp only [stackContent, Int.toNat_natCast, List.getD_eq_getElem s _ h]

open Turing.PartrecToTM2 in
/-- **push 語意**：新符號 `x` 落在舊頂位 `len`（= 舊 next-push slot），舊內容不變。 -/
theorem stackContent_push_top (s : List Γ') (x : Γ') :
    stackContent (s ++ [x]) (s.length : ℤ) = Γ'BitEquiv x := by
  simp only [stackContent, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (le_refl s.length), Nat.sub_self]
  rfl

open Turing.PartrecToTM2 in
/-- **堆疊解碼**：給長度 `len`，從內容軌讀回 `len` 個符號的堆疊。 -/
def stackDecode (len : ℕ) (content : ℤ → Bool × Bool) : List Γ' :=
  List.ofFn fun j : Fin len ↦ Γ'BitEquiv.symm (content (j : ℤ))

open Turing.PartrecToTM2 in
/-- **★編碼忠實性（round-trip）★**：從（長度 + 內容軌）**唯一復原**原堆疊。這是不可逆
`M_tr` 正確性歸納的地基——組態由其位帶編碼唯一決定。 -/
theorem stackDecode_stackContent (s : List Γ') :
    stackDecode s.length (stackContent s) = s := by
  apply List.ext_getElem
  · simp [stackDecode]
  · intro n h1 _
    have hn : n < s.length := by simpa [stackDecode] using h1
    simp only [stackDecode, List.getElem_ofFn]
    rw [show ((⟨n, by simpa [stackDecode] using h1⟩ : Fin s.length) : ℤ) = (n : ℤ) from rfl,
      stackContent_get s n hn, Equiv.symm_apply_apply]

/-! ## 單堆疊-op 的編碼層正確性（(ii) B2a 子塊 2）

M_tr 的堆疊微步（push / pop）在位帶上 = **有界局部編輯 + 標記移一格**。本塊證這個局部編輯
**在編碼層是對的**：push 只寫頂位、下層原封不動；pop（`dropLast`）留住下層；且 decode 忠實
還原 push/pop 後的堆疊。這是「編輯**該**產生什麼」的規格——BitTM 走位+位編輯的機械（子塊 3）
以此為正確性目標。 -/

open Turing.PartrecToTM2 in
/-- **push 下層不變**：`j < len` 的格不受 append 影響（push 只動頂位 `len`，見
`stackContent_push_top`）。 -/
theorem stackContent_push_lower (s : List Γ') (x : Γ') {j : ℤ} (h : j.toNat < s.length) :
    stackContent (s ++ [x]) j = stackContent s j := by
  simp only [stackContent]
  rw [List.getD_append s [x] Γ'.consₗ j.toNat h]

open Turing.PartrecToTM2 in
/-- **pop 留住下層**：`dropLast` 對 `j < len-1` 的格與原堆疊同（pop 只砍頂符號 + 移標記）。 -/
theorem stackContent_dropLast_eq (s : List Γ') {j : ℤ} (h : j.toNat < s.length - 1) :
    stackContent s.dropLast j = stackContent s j := by
  simp only [stackContent]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_dropLast]
  simp [h]

open Turing.PartrecToTM2 in
/-- **push 後解碼忠實**：長度 `len+1` + push 後的內容軌 → 唯一還原 `s ++ [x]`。 -/
theorem stackDecode_push (s : List Γ') (x : Γ') :
    stackDecode (s.length + 1) (stackContent (s ++ [x])) = s ++ [x] := by
  have := stackDecode_stackContent (s ++ [x])
  simpa using this

open Turing.PartrecToTM2 in
/-- **pop 後解碼忠實**：長度 `len-1` + pop 後的內容軌 → 唯一還原 `s.dropLast`。 -/
theorem stackDecode_pop (s : List Γ') :
    stackDecode (s.length - 1) (stackContent s.dropLast) = s.dropLast := by
  have := stackDecode_stackContent s.dropLast
  rwa [List.length_dropLast] at this

end FluidTuring
