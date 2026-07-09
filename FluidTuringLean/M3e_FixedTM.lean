import FluidTuringLean.M3b_ReversibleTM

/-!
# Module 3e — 固定頭圖靈機（方案 C 地基，C-α，2026-07-08）

**方案 C 兩流 crux 的鑰匙**：`bennettTM`（moving-tape BitTM）一條帶要同時裝
「M 模擬帶（每步平移）」+「垃圾尾跡（該靜止）」= 兩獨立平移行為（同 M3d
里程碑 C 無界版與方案 B 撞的牆）。**改用固定頭 TM 化解**：帶靜止、頭是一個
可移動標記，於是 M 帶不平移、垃圾靜止不打架，字面機只需**可逆走位**
（`walk_reversible`/`walk_roundtrip_closes` 已在 M3d 驗證）訪頭標記與垃圾 frontier。

本檔（C-α）：定義固定頭 TM `FixedTM`（狀態位向量 + 靜止帶 `ℤ → Bool` + 頭位置 `ℤ`），
單步 `step`（讀頭格、寫、換態、移頭），及與 moving-tape `BitTM` 的橋接方向。

後續（見 `docs/M3D_C_DECOMPOSITION_PLAN.md` 方案 C 4 相位）：C-β 靜止帶佈局 +
走位 macrostep、C-γ 雙標記走位 in-degree-1、C-δ 宏步正確 + 接 M6。本檔零 sorry。
-/

namespace FluidTuring

/-- **固定頭圖靈機**：`m` 個狀態位元、字母 `Bool`、**帶靜止、頭在 `ℤ` 上移動**。
與 moving-tape `BitTM`（M3b）的唯一差別＝頭位置顯式（`ℤ`）、帶不平移 ——
這正是讓垃圾能靜止堆疊、化解兩流 crux 的關鍵。 -/
structure FixedTM where
  /-- 狀態位元數。 -/
  m : ℕ
  /-- 轉移：新狀態（讀「當前狀態, 頭下帶格」）。 -/
  next : (Fin m → Bool) → Bool → (Fin m → Bool)
  /-- 轉移：寫入頭下帶格。 -/
  write : (Fin m → Bool) → Bool → Bool
  /-- 轉移：頭移動方向。 -/
  move : (Fin m → Bool) → Bool → Dir

namespace FixedTM

variable (M : FixedTM)

/-- 組態：狀態 × 靜止帶 × 頭位置。 -/
abbrev Cfg : Type := (Fin M.m → Bool) × (ℤ → Bool) × ℤ

/-- 單步：讀頭下格 `t h`、寫回該格、換態、頭依方向移動（**帶不平移，只有頭動**）。 -/
def step (c : M.Cfg) : M.Cfg :=
  let q := c.1
  let t := c.2.1
  let h := c.2.2
  let a := t h
  (M.next q a,
   fun i ↦ if i = h then M.write q a else t i,
   h + (M.move q a).toInt)

@[simp] theorem step_state (c : M.Cfg) : (M.step c).1 = M.next c.1 (c.2.1 c.2.2) := rfl

@[simp] theorem step_head (c : M.Cfg) :
    (M.step c).2.2 = c.2.2 + (M.move c.1 (c.2.1 c.2.2)).toInt := rfl

/-- 頭格寫入正確：單步後頭「原位置」的帶格 = 寫入位。 -/
theorem step_tape_at_head (c : M.Cfg) :
    (M.step c).2.1 c.2.2 = M.write c.1 (c.2.1 c.2.2) := by
  simp [step]

/-- 頭格外不動：單步後非頭位置的帶格不變。 -/
theorem step_tape_off_head (c : M.Cfg) {i : ℤ} (hi : i ≠ c.2.2) :
    (M.step c).2.1 i = c.2.1 i := by
  simp [step, hi]

/-- **與 moving-tape `BitTM` 的對照**（C-α 橋接方向、記錄非證明）：
`BitTM`（M3b）頭固定讀帶位 0、`step` 平移整條帶；`FixedTM` 帶靜止、頭在 `ℤ` 移動。
兩模型計算等價（標準 TM 理論），差別純在「誰動」——moving-tape 讓帶平移吃掉
垃圾靜止性，fixed-head 讓帶靜止使垃圾可堆疊。方案 C 用 fixed-head 當被模擬機器，
字面 Bennett 機（本身仍是 moving-tape `BitTM`）以**淨零平移走位**在其靜止帶上
訪頭標記與垃圾 frontier。完整橋接（`BitTM ≃ FixedTM` 動力學）留 C-β/後續。 -/
theorem fixedTM_vs_bitTM_note : True := trivial

end FixedTM

end FluidTuring
