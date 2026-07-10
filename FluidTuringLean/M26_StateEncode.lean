import FluidTuringLean.M25_TapeBridge

/-!
# Module 26 — TM0(Bool) → 我們 BitTM 橋之二：狀態編碼（M_tr 本體 4b-4b）

mathlib `TM0` 的組態控制 `q : Option Λ`（`none` = 停機、`some q` = 標籤），`Λ` 是無限型但
**有限可達**（`tr_supports` 給 `Finset` `S`）。我們 BitTM 的狀態 = `Fin m → Bool`（有限位向量）。
本塊把「停機 + 可達標籤」編進位向量：

- `ctrlType S := Option ↥S`（停機槽 `none` + 可達標籤子型 `↥S`）——有限型（`Fintype`）。
- **one-hot 編碼**：`m := card (ctrlType S)`，控制 `c` → 位向量「只在 `ctrlEquivFin c` 位為 1」。
  單射（`encCtrl_injective`）。
- **解碼** `decCtrl := Function.invFun encCtrl`：單射 ⟹ 左逆免費（`Function.leftInverse_invFun`），
  垃圾位向量解到某控制（不影響正確性，M_tr 只碰可達狀態）。round-trip `decCtrl_encCtrl`。

⟹ TM0 控制（含停機）忠實塞進 `Fin m → Bool` = M_tr 的狀態地基。halt sentinel = `encCtrl none`。
（沿用 M18/M21 的有限性→`Fin` 手法，但改 one-hot + `invFun` 免 dite/castLE。）
-/

namespace FluidTuring

/-- M_tr 控制的有限型：停機槽 `none` + 可達 TM0 標籤子型 `↥S`。（`abbrev` 使 `Option ↥S`
與 `ctrlType S` 可約互通，免型別失配。） -/
abbrev ctrlType {Λ : Type*} (S : Finset Λ) : Type _ := Option ↥S

instance {Λ : Type*} (S : Finset Λ) : Fintype (ctrlType S) := by
  unfold ctrlType; infer_instance

instance {Λ : Type*} (S : Finset Λ) : Inhabited (ctrlType S) := ⟨none⟩

/-- 控制型的元素數（= `|S| + 1`）。 -/
def ctrlCard {Λ : Type*} (S : Finset Λ) : ℕ := Fintype.card (ctrlType S)

/-- 控制 ≃ `Fin card`（one-hot 的索引）。 -/
noncomputable def ctrlEquivFin {Λ : Type*} (S : Finset Λ) : ctrlType S ≃ Fin (ctrlCard S) :=
  Fintype.equivFin _

/-- **one-hot 狀態編碼**：控制 `c` → 位向量，只在 `ctrlEquivFin c` 位為 `true`。 -/
noncomputable def encCtrl {Λ : Type*} (S : Finset Λ) (c : ctrlType S) : Fin (ctrlCard S) → Bool :=
  fun j ↦ decide (ctrlEquivFin S c = j)

/-- **單射**：不同控制 → 不同 one-hot 位向量。 -/
theorem encCtrl_injective {Λ : Type*} (S : Finset Λ) : Function.Injective (encCtrl S) := by
  intro c c' h
  have hj := congrFun h (ctrlEquivFin S c)
  simp only [encCtrl] at hj
  rw [decide_eq_decide] at hj
  exact (ctrlEquivFin S).injective (hj.mp trivial).symm

/-- **狀態解碼**（`invFun`）：單射 ⟹ 左逆免費。垃圾位向量解到某控制（不影響正確性）。 -/
noncomputable def decCtrl {Λ : Type*} (S : Finset Λ) : (Fin (ctrlCard S) → Bool) → ctrlType S :=
  Function.invFun (encCtrl S)

/-- **round-trip**：解碼還原編碼（`Function.leftInverse_invFun`）。 -/
theorem decCtrl_encCtrl {Λ : Type*} (S : Finset Λ) (c : ctrlType S) :
    decCtrl S (encCtrl S c) = c :=
  Function.leftInverse_invFun (encCtrl_injective S) c

/-- **halt sentinel**：停機控制 `none` 的位向量 = M_tr 的停機狀態。 -/
noncomputable def encHalt {Λ : Type*} (S : Finset Λ) : Fin (ctrlCard S) → Bool :=
  encCtrl S none

end FluidTuring
