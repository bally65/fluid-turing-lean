import FluidTuringLean.M26_StateEncode

/-!
# Module 27 — TM0(Bool) → 我們 BitTM 橋之三：定 `M_tr` + 一步模擬（M_tr 本體 4b-4c）

route β 核心 payload：把帶橋（M25）+ 狀態編碼（M26）焊成真正的 `M_tr : BitTM`，並證它一步一步
跟著 mathlib `TM0.step` 走。

mathlib `TM0.Cfg Bool Λ = ⟨q : Λ, Tape⟩`（`q` 是 `Λ`、無 `Option`；停機 = `M q head = none` ⟹
`step` 傳 `none`）；`step ⟨q,T⟩ = (M q T.head).map fun (q',a) ↦ ⟨q', act a T⟩`。

`M_tr` 設計（`stepData` 由讀 `(狀態位向量, 讀位)` 算出「下一控制、寫位、方向」）：
- 解碼狀態 → `ctrlType S`（M26）：`none`（停機）→ 自環（不動）；`some q` → 查 `M q b`：
  - `none`（TM0 停機）→ 去 `encHalt`、不動；
  - `some (q', 寫 a)` → 控制 `q'`、寫 `a`、`stay`；
  - `some (q', 移 d)` → 控制 `q'`、寫回讀位（恆等）、方向 `d`（我們 3 態 `Dir`）。
`q' ∈ S` 由 `Supports` 前向封閉保證（`dite`，else 死枝 → 停機）。**一個 BitTM 步 = 一個 TM0 步**。

**本塊交付（4b-4c）**：`Mtr`（機器）+ `encTM0`（組態編碼器）+ `Mtr_step_halt`（`encHalt` 自環
= 停機吸收，供 `hHclosed`）。非停機一步追蹤 `Mtr_step_run` = 4b-4c-ii。
-/

namespace FluidTuring

/-- mathlib 2 態 `Dir` → 我們 3 態 `Dir`。 -/
def dirOfDir : Turing.Dir → Dir
  | .left => .left
  | .right => .right

open Classical in
/-- 由 `(狀態位向量, 讀位)` 算出下一步資料：`(下一控制, 寫位, 方向)`。 -/
noncomputable def stepData {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) (s : Fin (ctrlCard S) → Bool) (b : Bool) : ctrlType S × Bool × Dir :=
  match decCtrl S s with
  | none => (none, b, Dir.stay)
  | some q =>
    match M (↑q) b with
    | none => (none, b, Dir.stay)
    | some (q', act) =>
      let nc : ctrlType S := if h : q' ∈ S then some ⟨q', h⟩ else none
      match act with
      | Turing.TM0.Stmt.write a => (nc, a, Dir.stay)
      | Turing.TM0.Stmt.move d => (nc, b, dirOfDir d)

/-- **`M_tr : BitTM`**：狀態 = `Fin (ctrlCard S) → Bool`（M26）、帶 = `ℤ → Bool`（M25）；
`next/write/move` 由 `stepData` 投影 = 模擬 mathlib `TM0.step`。 -/
noncomputable def Mtr {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) : BitTM where
  m := ctrlCard S
  next s b := encCtrl S (stepData M S s b).1
  write s b := (stepData M S s b).2.1
  move s b := (stepData M S s b).2.2

open Classical in
/-- TM0 標籤 → M_tr 控制（可達則 `some`、否則 `none`=停機槽）。 -/
noncomputable def ctrlOfLabel {Λ : Type*} (S : Finset Λ) (q : Λ) : ctrlType S :=
  if h : q ∈ S then some ⟨q, h⟩ else none

/-- **組態編碼器**：TM0 組態 `⟨q, T⟩` → M_tr 組態 `(狀態位向量, 帶 nth 視圖)`。 -/
noncomputable def encTM0 {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) (c : Turing.TM0.Cfg Bool Λ) : (Mtr M S).Cfg :=
  (encCtrl S (ctrlOfLabel S c.q), fun i ↦ c.Tape.nth i)

/-- **停機自環**：`encHalt`（控制 `none`）狀態不動——停機吸收（供 `hHclosed`）。 -/
theorem Mtr_step_halt {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ)
    (S : Finset Λ) (t : ℤ → Bool) :
    (Mtr M S).step (encHalt S, t) = (encHalt S, t) := by
  have hdec : decCtrl S (encHalt S) = none := decCtrl_encCtrl S none
  rw [BitTM.step_eval]
  simp only [Mtr, stepData, hdec, Dir.toInt, add_zero]
  refine Prod.ext rfl ?_
  funext n
  by_cases hn : n = 0 <;> simp [hn]

/-- TM0 動作套用到帶（= `TM0.step` 的帶結果）。 -/
def actApply (act : Turing.TM0.Stmt Bool) (T : Turing.Tape Bool) : Turing.Tape Bool :=
  match act with
  | Turing.TM0.Stmt.move d => T.move d
  | Turing.TM0.Stmt.write a => T.write a

/-- BitTM 帶更新（作用於 `nth` 視圖）= `tapeStep` 後的 `nth` 視圖（橋接 M25）。 -/
theorem bittm_tape_eq (w : Bool) (d : Dir) (T : Turing.Tape Bool) :
    (fun n : ℤ ↦ if n + d.toInt = 0 then w else (fun i ↦ T.nth i) (n + d.toInt))
      = fun i ↦ (tapeStep w d T).nth i := by
  funext n; rw [tapeStep_nth]

/-- **★非停機一步追蹤★**：若 `M q head = some (q', act)`（TM0 不停機、`q,q' ∈ S`），則 M_tr 一步
= 編碼後的 TM0 一步結果。= route β 的一步模擬（帶用 M25 `tapeStep_nth`、狀態用 M26 `decCtrl_encCtrl`）。 -/
theorem Mtr_step_run {Λ : Type*} [Inhabited Λ] (M : Turing.TM0.Machine Bool Λ) (S : Finset Λ)
    {q q' : Λ} {act : Turing.TM0.Stmt Bool} {T : Turing.Tape Bool}
    (hq : q ∈ S) (hq' : q' ∈ S) (hact : M q T.head = some (q', act)) :
    (Mtr M S).step (encTM0 M S ⟨q, T⟩) = encTM0 M S ⟨q', actApply act T⟩ := by
  have hcq' : ctrlOfLabel S q' = some ⟨q', hq'⟩ := by simp [ctrlOfLabel, hq']
  have hdec : decCtrl S (encCtrl S (ctrlOfLabel S q)) = some ⟨q, hq⟩ := by
    rw [decCtrl_encCtrl]; simp [ctrlOfLabel, hq]
  simp only [encTM0]
  rw [BitTM.step_eval]
  simp only [Turing.Tape.nth_zero]
  cases act with
  | write a =>
    have hsd : stepData M S (encCtrl S (ctrlOfLabel S q)) T.head
        = ((some ⟨q', hq'⟩ : ctrlType S), a, Dir.stay) := by
      simp only [stepData, hdec, hact, dif_pos hq']
    simp only [Mtr, hsd, hcq', Dir.toInt, add_zero]
    refine Prod.ext rfl ?_
    funext n
    simp only [actApply, Turing.Tape.write_nth]
  | move d =>
    have hsd : stepData M S (encCtrl S (ctrlOfLabel S q)) T.head
        = ((some ⟨q', hq'⟩ : ctrlType S), T.head, dirOfDir d) := by
      simp only [stepData, hdec, hact, dif_pos hq']
    simp only [Mtr, hsd, hcq']
    refine Prod.ext rfl ?_
    rw [bittm_tape_eq]
    simp only [tapeStep, Turing.Tape.write_self, actApply]
    cases d <;> rfl

end FluidTuring
