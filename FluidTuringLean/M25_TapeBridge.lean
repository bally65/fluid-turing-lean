import FluidTuringLean.M24_TM1to0
import FluidTuringLean.M3b_ReversibleTM

/-!
# Module 25 — TM0(Bool) → 我們 BitTM 橋之一：帶表示轉換（M_tr 本體 4b-4a）

4b-4 = 把 mathlib `TM0`（Bool 字母）橋到我們的 `BitTM`。三個表示差異：帶、狀態、步型。本塊做
**帶**：mathlib `Turing.Tape Bool`（head-centered、`Tape.move` 動頭）↔ 我們 BitTM 的 `ℤ → Bool`
（moving-tape、頭固定在 0、`step` 讀 `t 0`、寫、依 `move` 平移）。

**關鍵吻合**：mathlib `Tape.nth : Tape Γ → ℤ → Γ` 就是 `ℤ → Bool` 視圖（`nth 0 = head`）。而我們
BitTM 的一步帶更新 `fun n ↦ if n + d.toInt = 0 then w else t (n + d.toInt)`（M3b `step_eval`）**恰好**
= 對 mathlib 帶「先寫 `w`、再依 `d` 移」後取 `nth`：
- 我們 `Dir` 有 3 態 `{left, stay, right}`（`toInt = -1/0/1`，含 **stay**，不同於 mathlib 2 態 `Turing.Dir`）。
- `stay`（`toInt=0`）= 純寫不移；`left/right` = mathlib `Tape.move`。

⟹ **一個 BitTM 步 = 一個 TM0 步**（stay 模擬 TM0 寫、left/right 模擬 TM0 移；寫回讀值即恆等寫）。

**本塊交付**：`dirMove`（我們 3 態 `Dir` → mathlib 帶移）+ `dirMove_nth`（`nth` 平移 `d.toInt`）+
`tapeStep`（寫後移）+ **`tapeStep_nth`**（= 我們 BitTM 的帶更新公式）。
-/

namespace FluidTuring

/-- 我們的 3 態 `Dir` → mathlib 帶移：`stay` = 不動、`left/right` = mathlib `Tape.move`。 -/
def dirMove (d : Dir) (T : Turing.Tape Bool) : Turing.Tape Bool :=
  match d with
  | .left => T.move Turing.Dir.left
  | .stay => T
  | .right => T.move Turing.Dir.right

/-- `dirMove` 對 `nth` 恰好平移 `d.toInt`（`left=-1`、`stay=0`、`right=+1`）。 -/
theorem dirMove_nth (d : Dir) (T : Turing.Tape Bool) (n : ℤ) :
    (dirMove d T).nth n = T.nth (n + d.toInt) := by
  cases d
  · rw [dirMove, Turing.Tape.move_left_nth]; congr 1
  · rw [dirMove]; simp [Dir.toInt]
  · rw [dirMove, Turing.Tape.move_right_nth]; congr 1

/-- 一步帶操作：先在頭寫 `w`、再依 `d` 移（= 我們 BitTM 一步的帶部分）。 -/
def tapeStep (w : Bool) (d : Dir) (T : Turing.Tape Bool) : Turing.Tape Bool := dirMove d (T.write w)

/-- **★帶橋★**：`tapeStep` 的 `nth` = 我們 BitTM 的帶更新公式
`fun n ↦ if n + d.toInt = 0 then w else t (n + d.toInt)`（M3b `step_eval`）。⟹ mathlib 帶動力學
與我們 BitTM 的 `ℤ→Bool` 帶動力學在 `nth` 對應下逐格吻合。 -/
theorem tapeStep_nth (w : Bool) (d : Dir) (T : Turing.Tape Bool) (n : ℤ) :
    (tapeStep w d T).nth n = if n + d.toInt = 0 then w else T.nth (n + d.toInt) := by
  rw [tapeStep, dirMove_nth, Turing.Tape.write_nth]

/-- 讀頭 = `nth 0`（mathlib `Tape.nth_zero`）：我們 BitTM 讀 `t 0` = mathlib `T.head`。 -/
theorem tape_head_nth (T : Turing.Tape Bool) : T.nth 0 = T.head := Turing.Tape.nth_zero T

end FluidTuring
