import Mathlib
import FluidTuringLean.M3b_ReversibleTM
import FluidTuringLean.M25_TapeBridge
import FluidTuringLean.M55_BlankTape

/-!
# Module 57 — G6 splice啟動：BitTM ↔ 玩具 σ 步對步結構橋（★CRUX★）

**承 M55（GPAC 玩具 CPU、`GCfgB`/`gStepRLB`、ℕ 字母、無限帶、已去 `bothNonempty`）+ M3b/M25/M27/M28
（`BitTM`/`Mtr`、主線不可判定鏈的機器層，已無條件證 `Mtr_halts_iff`）**。設計 scope workflow（6
researcher + synth）裁決 G6 = **ACHIEVABLE_MULTI_ROUND**（非牆，~4 session）；本模組落地 M55 文件
自己點名的缺口：「另一結構橋（BitTM↔兩堆疊、≈M25+M26+M27 級、後續 G6 splice）」——**現在建了**。

## 一句話

`BitTM.step`（狀態=位元向量 `Fin m→Bool`、帶=`Turing.Tape Bool`、3 態 `Dir` 含 stay）與
`gStepRL3`（`GCfgB` 的 3 態推廣、狀態=ℕ、帶=兩個 `ListBlank ℕ`）**在編碼 `bitEnc` 下步對步相等**——
純 mathlib `Tape.mk'`/`ListBlank.map` 組裝、**零新數學洞見**、**零 sorry**。

## 交付（全顯式、字面相等、標準三公理）

- **狀態橋**：`bitVecToNat`（`Fintype.equivFin` 給的位元向量→ℕ，`< 2^m`）。
- **字母橋**：`boolToNatPM`/`blMap`（mathlib 現成 `ListBlank.map`，`digitsLtB 2` 對任意 `l` 無條件成立）。
- **帶橋（★原疑最高風險、驗證後零障礙★）**：GCfgB 的「R.head=當前讀符」慣例**就是** mathlib 自己的
  `Tape.mk' L R := {head:=R.head, left:=L, right:=R.tail}`——**不需新結構**。三條 `tapeStep_mk'_*`
  逐一驗過 `tapeStep`（M25，= `BitTM.step` 帶公式）在 `Tape.mk'` 下的 L/R 更新，**與 `gStepRL3` 的三臂
  逐項相同、無方向翻轉、無 off-by-one**。
- `bitEnc {m} (v : Fin m→Bool) (T : Tape Bool) : GCfgB`：位元向量+mathlib 帶 → `GCfgB`。
- `gStepRL3`（`GCfgB` 的 3 態離散步、`Dir` 直接重用 M3b）。
- **`gStepRL3_simulates_BitTM`（★CRUX★）**：`gStepRL3 (δqOf M)(δwOf M)(moveOf M) (bitEnc v T)
  = bitEnc (M.next v T.head) (tapeStep (M.write v T.head)(M.move v T.head) T)`——**字面相等**、
  `cases M.move v T.head`、純 `Tape.mk'`/`ListBlank` 代數，**無 sorry**。

## ★誠實範圍（禁 overclaim）★

- **這是一個結構橋，不是不可判定結果**——本模組**不**接 `Mtr_halts_iff`、**不**得出任何
  `¬ComputablePred` 結論。真的 G6 splice（把 `Mtr_halts_iff` + 通用碼機械composed 到
  `sigmaRL3` 軌道可達性不可判定）是後續模組（M58 起：σ-level 3-way smooth lift `sigmaRL3` +
  wf 保持 + N 步版本 + 最終 splice）。
- **`bitEnc` 只對 `Turing.Tape Bool`-形狀的組態定義**——**不**對任意 `BitTM.Cfg = (Fin m→Bool)×(ℤ→Bool)`
  定義（基數論證：`ListBlank` 只可數、`ℤ→Bool` 不可數，**不存在**對任意 `ℤ→Bool` 忠實的雙 `ListBlank`
  編碼）。**這不構成 G6 的障礙**：`Mtr M S`（M27）透過 `encTM0` 產生的組態**恆為** `Tape`-形狀
  （`encTM0 M S c := (…, fun i ↦ c.Tape.nth i)`），G6 splice 從未需要對任意 `ℤ→Bool` 定義 `bitEnc`。
- **仍是離散映射目標，非連續流**：G6 志在「顯式 C^∞ 映射 `sigmaRL3` 的軌道可達性不可判定」，**不**是
  連續 ODE 流的 undecidability（那個連續流升級 = 已證死牆，見 `M56_G5Wall.lean` 的 `K>1` 讀增益、
  `pop_not_contractive`）。G6 的路線嚴格比 M29/M33 的 Bennett-reversibilize+懸浮流路線**簡單**：
  `sigmaRL3` 已是裸 ℝ³ 自映射，只需 `Function.iterate`，不需緊空間/連續流/`ContinuousFlowOn` 機器。
- **邊際價值**：完工後的 G6 headline 是主線 M33（連續流、無條件）的**離散映射姊妹結果**——不同數學
  物件（映射 vs 流）、皆源自同一 `Mtr_halts_iff` 機器層，**不冗餘、非取代**。
-/

namespace FluidTuring

open Turing

/-! ## 狀態橋：位元向量 `Fin m → Bool` ↔ ℕ -/

/-- **位元向量→ℕ**（`Fintype.equivFin` 現成，非新構造）。 -/
noncomputable def bitVecToNat (m : ℕ) (v : Fin m → Bool) : ℕ :=
  (Fintype.equivFin (Fin m → Bool) v : ℕ)

theorem bitVecToNat_injective (m : ℕ) : Function.Injective (bitVecToNat m) := by
  intro a b h
  exact (Fintype.equivFin (Fin m → Bool)).injective (Fin.val_injective h)

/-- **界**：`bitVecToNat m v < 2^m`（給下游 `Q := 2^m`）。 -/
theorem bitVecToNat_lt (m : ℕ) (v : Fin m → Bool) : bitVecToNat m v < 2 ^ m := by
  have h : Fintype.card (Fin m → Bool) = 2 ^ m := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  unfold bitVecToNat
  rw [← h]
  exact (Fintype.equivFin (Fin m → Bool) v).isLt

/-- ℕ→位元向量解碼（`invFun`）+ 圓滿往返。 -/
noncomputable def natToBitVec (m : ℕ) : ℕ → (Fin m → Bool) := Function.invFun (bitVecToNat m)

theorem natToBitVec_bitVecToNat (m : ℕ) (v : Fin m → Bool) :
    natToBitVec m (bitVecToNat m v) = v :=
  Function.leftInverse_invFun (bitVecToNat_injective m) v

/-! ## 字母橋：`Bool ↔ {0,1} ⊂ ℕ`（mathlib `ListBlank.map` 現成） -/

/-- `Bool → ℕ` 的 pointed map（blank `false ↦ 0`）。 -/
noncomputable def boolToNatPM : Turing.PointedMap Bool ℕ := ⟨fun b => if b then 1 else 0, rfl⟩

/-- Bool 半帶 → ℕ 半帶（mathlib 現成 `ListBlank.map`，非新構造）。 -/
noncomputable def blMap (l : ListBlank Bool) : ListBlank ℕ := ListBlank.map boolToNatPM l

theorem blMap_head (l : ListBlank Bool) : (blMap l).head = boolToNatPM.f l.head :=
  ListBlank.head_map _ l
theorem blMap_tail (l : ListBlank Bool) : (blMap l).tail = blMap l.tail :=
  ListBlank.tail_map _ l
theorem blMap_cons (d : Bool) (l : ListBlank Bool) :
    blMap (l.cons d) = (blMap l).cons (boolToNatPM.f d) :=
  ListBlank.map_cons _ l d

/-- head/tail 重組（`ListBlank.cons_head_tail` 經 `blMap` 推）。 -/
theorem blMap_head_tail (l : ListBlank Bool) :
    blMap l = (blMap l.tail).cons (boolToNatPM.f l.head) := by
  conv_lhs => rw [← ListBlank.cons_head_tail l]
  rw [blMap_cons]

/-- **★字母界無條件成立★**：`blMap` 的像恆 `digitsLtB 2`（Bool 只有兩值）——G4e/M55 的 wf 前提
對 Bool 字母**免費**。 -/
theorem digitsLtB_two_map (l : ListBlank Bool) : digitsLtB 2 (blMap l) := by
  intro i
  induction i generalizing l with
  | zero =>
    rw [ListBlank.nth_zero, blMap_head]
    unfold boolToNatPM; cases l.head <;> simp
  | succ n ih =>
    rw [ListBlank.nth_succ, blMap_tail]
    exact ih l.tail

/-- 解碼 ℕ → Bool（`n ≠ 0` 判活）+ 與 `boolToNatPM` 圓滿往返。 -/
def natToBool (n : ℕ) : Bool := decide (n ≠ 0)

theorem natToBool_boolToNatPM (b : Bool) : natToBool (boolToNatPM.f b) = b := by
  unfold natToBool boolToNatPM; cases b <;> simp

/-! ## 帶橋（★原疑最高風險、驗過零障礙★）：`GCfgB` 的 `R.head` 慣例 = mathlib `Tape.mk'` -/

/-- 右移：`tapeStep` 在 `Tape.mk' L R` 上的更新 = `gStepRL3` 右臂逐項（`Tape.mk'_left/_right/_head`
+ `Tape.write`/`Tape.move` 純展開）。 -/
theorem tapeStep_mk'_right (L R : ListBlank Bool) (w : Bool) :
    tapeStep w Dir.right (Tape.mk' L R) = Tape.mk' (L.cons w) R.tail := by
  unfold tapeStep dirMove Tape.mk'
  simp only [Tape.write, Tape.move]

/-- 左移：同上、左臂。 -/
theorem tapeStep_mk'_left (L R : ListBlank Bool) (w : Bool) :
    tapeStep w Dir.left (Tape.mk' L R) = Tape.mk' L.tail ((R.tail.cons w).cons L.head) := by
  unfold tapeStep dirMove Tape.mk'
  simp only [Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons]

/-- 停留（BitTM 3 態、`gStepRLB`(M55) 沒有的第三臂）：純寫不移。 -/
theorem tapeStep_mk'_stay (L R : ListBlank Bool) (w : Bool) :
    tapeStep w Dir.stay (Tape.mk' L R) = Tape.mk' L (R.tail.cons w) := by
  unfold tapeStep dirMove Tape.mk'
  simp only [Tape.write, ListBlank.head_cons, ListBlank.tail_cons]

/-! ## 組態編碼 + 3 態離散步 -/

/-- **位元向量+mathlib 帶 → `GCfgB`**：`R := T.right.cons T.head`（`Tape.mk'` 逆向、R.head=當前
讀符，與 `GCfgB` 既有慣例一致）。**只對 `Tape Bool`-形狀組態定義**（誠實範圍見檔頭）。 -/
noncomputable def bitEnc {m : ℕ} (v : Fin m → Bool) (T : Tape Bool) : GCfgB :=
  ⟨bitVecToNat m v, blMap T.left, blMap (T.right.cons T.head)⟩

theorem bitEnc_R_head {m} (v : Fin m → Bool) (T : Tape Bool) :
    (bitEnc v T).R.head = boolToNatPM.f T.head := by
  change (blMap (T.right.cons T.head)).head = _
  rw [blMap_head, ListBlank.head_cons]

/-- **`GCfgB` 的 3 態離散步**（`gStepRLB`(M55) 的推廣、`Dir` 直接重用 M3b、無 fallback）。 -/
def gStepRL3 (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Dir) (c : GCfgB) : GCfgB :=
  match move c.q c.R.head with
  | .right => ⟨δq c.q c.R.head, c.L.cons (δw c.q c.R.head), c.R.tail⟩
  | .left => ⟨δq c.q c.R.head, c.L.tail, (c.R.tail.cons (δw c.q c.R.head)).cons c.L.head⟩
  | .stay => ⟨δq c.q c.R.head, c.L, c.R.tail.cons (δw c.q c.R.head)⟩

/-- 從 `BitTM` 解碼-套用-編碼出的轉移表（`gStepRL3` 吃的 `δq/δw/move : ℕ→ℕ→_` 形狀）。 -/
noncomputable def δqOf (M : BitTM) : ℕ → ℕ → ℕ :=
  fun s r => bitVecToNat M.m (M.next (natToBitVec M.m s) (natToBool r))
noncomputable def δwOf (M : BitTM) : ℕ → ℕ → ℕ :=
  fun s r => boolToNatPM.f (M.write (natToBitVec M.m s) (natToBool r))
noncomputable def moveOf (M : BitTM) : ℕ → ℕ → Dir :=
  fun s r => M.move (natToBitVec M.m s) (natToBool r)

/-! ## ★CRUX：步對步結構橋★ -/

/-- **★CRUX★**：`BitTM`（經 `bitEnc`）一步 = `gStepRL3`（經解碼表）一步，**字面相等**。純
`Tape.mk'`/`ListBlank` 代數，`cases M.move v T.head`（三分支）。這是 M55 文件點名待建的
「BitTM↔兩堆疊結構橋（≈M25+M26+M27 級）」。 -/
theorem gStepRL3_simulates_BitTM (M : BitTM) (v : Fin M.m → Bool) (T : Tape Bool) :
    gStepRL3 (δqOf M) (δwOf M) (moveOf M) (bitEnc v T)
      = bitEnc (M.next v T.head) (tapeStep (M.write v T.head) (M.move v T.head) T) := by
  have hr : (bitEnc v T).R.head = boolToNatPM.f T.head := bitEnc_R_head v T
  have hdecS : natToBitVec M.m (bitEnc v T).q = v := by
    change natToBitVec M.m (bitVecToNat M.m v) = v
    rw [natToBitVec_bitVecToNat]
  have hdecR : natToBool (bitEnc v T).R.head = T.head := by rw [hr, natToBool_boolToNatPM]
  have hmove : moveOf M (bitEnc v T).q (bitEnc v T).R.head = M.move v T.head := by
    unfold moveOf; rw [hdecS, hdecR]
  have hTeq : T = Tape.mk' T.left (T.right.cons T.head) := by
    cases T with
    | mk head left right => simp [Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]
  have hδq : δqOf M (bitEnc v T).q (bitEnc v T).R.head = bitVecToNat M.m (M.next v T.head) := by
    unfold δqOf; rw [hdecS, hdecR]
  have hδw : δwOf M (bitEnc v T).q (bitEnc v T).R.head = boolToNatPM.f (M.write v T.head) := by
    unfold δwOf; rw [hdecS, hdecR]
  have hL0 : (bitEnc v T).L = blMap T.left := rfl
  have hR0 : (bitEnc v T).R = blMap (T.right.cons T.head) := rfl
  unfold gStepRL3
  rw [hmove]
  rcases hmv : M.move v T.head with _ | _ | _ <;> dsimp only <;>
    rw [hδq, hδw, hL0, hR0] <;>
    conv_rhs => rw [hTeq]
  · rw [tapeStep_mk'_left]
    unfold bitEnc
    simp only [Tape.mk'_left, Tape.mk'_right, Tape.mk'_head, blMap_tail, blMap_head,
      blMap_cons, ListBlank.tail_cons, ListBlank.head_cons]
  · rw [tapeStep_mk'_stay]
    unfold bitEnc
    simp only [Tape.mk'_left, Tape.mk'_right, Tape.mk'_head,
      blMap_cons, ListBlank.tail_cons, ListBlank.head_cons]
  · rw [tapeStep_mk'_right]
    unfold bitEnc
    simp only [Tape.mk'_left, Tape.mk'_right, Tape.mk'_head, blMap_cons,
      ListBlank.tail_cons, ListBlank.head_cons]
    rw [blMap_head_tail T.right]

end FluidTuring
