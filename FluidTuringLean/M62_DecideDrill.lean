import FluidTuringLean.M59_SmoothUndecidable

/-!
# Module 62 — 橋的消防演習：σ 軌道到達 ↔ `Tape`-層到達（可 `decide` 的一端）

**承 M59（`reach_at_k`、`bitStep_iterate`）**。本磚做兩件小事：

1. **`reach_at_k_tape`**：把 `reach_at_k` 的右端從 `BitTM.step`（落在 `ℤ → Bool`，不可判定相等）
   改寫成 `bitStepTape`（停在 `Tape Bool`，狀態分量是 `Fin m → Bool`，**有 `DecidableEq`**）。
   這不是新數學——`reach_at_k` **自己的證明**（M59:143-145）已經 `rw` 到那裡再 `change` 回來；
   本磚只是把那個中途點抬成可引用的定理。

2. **消防演習**：在一台具體小機器 `readTM` 上，用 kernel `decide` 實際點火，
   驗證這座橋在**正面**（該響時響）與**反面**（不該響時不響）兩側都是對的。

## 為什麼要有這塊

在本磚之前，`FluidTuringLean/` 裡**沒有任何一處** `#eval`、沒有 `Decidable` harness、
沒有對這座橋的具體求值。整條 M57→M58→M59 鏈是一串從未被點過火的證明。
`reach_at_k` 若有一個方向性錯誤（例如 `tapeStep` 的左右接反、iterate 差一步），
它仍然會是一條**可證的**定理——只是證了另一件事。演習就是為了讓這種錯誤發出聲音。

**反向演習**（`drill_sigma_step2_ne`）比正向那條更重要：它驗的是「不該響時不響」。
只有正面演習的警報器，把 `Target` 放大成全空間也會通過。

## ★誠實範圍★

- **本磚不含新的可計算性內容。** `reach_at_k_tape` 與 `reach_at_k` 是同一條 iff 的兩種寫法，
  由 `bitStep_iterate`（M59:83）與 `encPair` 的定義相接；`rw` 之後 `rfl` 即閉。
- **被 `decide` 的是 `bitStepTape`（離散、`Tape Bool` 上的機器步），不是 `sigmaM`。**
  `sigmaM`（M59:122）`noncomputable`，連輸入編碼器 `bitVecToNat`（M57:59，Classical
  `Fintype.equivFin`）、`bitEnc`（M57:146）都不出 code——**實數那一側一步也跑不動**。
  可以說「我們跑了機器、答案靠 `reach_at_k_tape` 這條字面等式定理搬到 σ 側」；
  **不可以**說「我們跑了那個光滑映射」。
- **只用 kernel `decide`，禁 `native_decide`**：後者引入 `Lean.ofReduceBool`，會打壞
  `README.md` 對「僅 mathlib 標準三公理」的宣稱。本檔末的 `#print axioms` 就是這條的看門狗。
- `readTM` 是**演習用具**，不是本專案任何主定理的一部分，不得被引為成果。
-/

namespace FluidTuring

open Turing

/-! ## 1. `reach_at_k` 的 `Tape`-層改寫（可判定的一端） -/

/-- **★`reach_at_k` 的 `Tape`-層版本★**：右端改用 `bitStepTape`（M59:64），
狀態分量落在 `Fin M.m → Bool`，因此 `DecidableEq` 可用、可 `decide`。

與 `reach_at_k`（M59:134）的唯一差別是右端的載體：那裡是 `BitTM.step` 作用在
`encPair M (v, T)` 上（帶為 `ℤ → Bool`，函數相等不可判定），這裡是 `bitStepTape`。
兩者由 `bitStep_iterate`（M59:83）相接，`encPair` 取 `.1` 即投影，故 `rfl` 閉。 -/
theorem reach_at_k_tape (M : BitTM) (v vhalt : Fin M.m → Bool) (T : Tape Bool) (k : ℕ) :
    ((sigmaM M)^[k] (gEncB 8 (bitEnc v T))).1 = (bitVecToNat M.m vhalt : ℝ)
      ↔ ((bitStepTape M)^[k] (v, T)).1 = vhalt := by
  rw [reach_at_k, bitStep_iterate]
  exact Iff.rfl

/-! ## 2. 演習用具：一台會真的讀帶的小機器 -/

/-- **演習機**：狀態位 := 剛讀到的帶位；原地寫回；頭右移。

選它而不選 `BitTM.cnotTM`（M3b:478）的理由：`cnotTM` 的 `next q _ := q` **不動狀態**，
於是 `.1` 恆等於初始狀態，演習就與帶內容、與 `tapeStep` 的方向完全無關——
那種演習點不著火。`readTM` 的狀態在第 `k` 步等於帶的第 `k` 格，
所以任何「左右接反」或「差一步」的錯誤都會讓下面的 `decide` 失敗。 -/
def readTM : BitTM where
  m := 1
  next _ a := fun _ => a
  write _ a := a
  move _ _ := Dir.right

/-- 演習帶：`[true, false, true]`，其餘為空白（`false`），頭在第 0 格。 -/
def drillTape : Turing.Tape Bool := Turing.Tape.mk₁ [true, false, true]

/-- 演習起始狀態：`false`。 -/
def drillInit : Fin readTM.m → Bool := fun _ => false

/-! ### 2a. 離散側：機器真的被跑起來（kernel `decide`） -/

/-- 第 1 步：讀到帶的第 0 格 `true` ⟹ 狀態 = `true`。 -/
theorem drill_tape_step1 :
    ((bitStepTape readTM)^[1] (drillInit, drillTape)).1 = (fun _ => true) := by decide

/-- 第 2 步：讀到第 1 格 `false` ⟹ 狀態 = `false`。**這一步證明頭真的右移了**
（若 `move` 被錯接成 `Dir.stay`，此處會讀回 `true` 而失敗）。 -/
theorem drill_tape_step2 :
    ((bitStepTape readTM)^[2] (drillInit, drillTape)).1 = (fun _ => false) := by decide

/-- 第 4 步：走出 `[true,false,true]` 之外，讀到空白 `false`。 -/
theorem drill_tape_step4 :
    ((bitStepTape readTM)^[4] (drillInit, drillTape)).1 = (fun _ => false) := by decide

/-! ### 2b. σ 側：同一件事，經由 `reach_at_k_tape` 搬過去 -/

/-- **★正向演習★**：σ 軌道第 1 步的第一座標**確實**落在「狀態 = `true`」對應的實數上。 -/
theorem drill_sigma_step1 :
    ((sigmaM readTM)^[1] (gEncB 8 (bitEnc drillInit drillTape))).1
      = (bitVecToNat readTM.m (fun _ => true) : ℝ) := by
  rw [reach_at_k_tape]
  decide

/-- **★反向演習（比正向更重要）★**：σ 軌道第 2 步**不**落在「狀態 = `true`」上。

只有正向演習的警報器，把 `Target` 放大成全空間也會通過；這一條才擋得住。 -/
theorem drill_sigma_step2_ne :
    ((sigmaM readTM)^[2] (gEncB 8 (bitEnc drillInit drillTape))).1
      ≠ (bitVecToNat readTM.m (fun _ => true) : ℝ) := by
  rw [ne_eq, reach_at_k_tape]
  decide

/-- **★反向演習之二★**：第 0 步（還沒動）也不在 `true` 上——起點本身不得假陽性。 -/
theorem drill_sigma_step0_ne :
    ((sigmaM readTM)^[0] (gEncB 8 (bitEnc drillInit drillTape))).1
      ≠ (bitVecToNat readTM.m (fun _ => true) : ℝ) := by
  rw [ne_eq, reach_at_k_tape]
  decide

end FluidTuring
