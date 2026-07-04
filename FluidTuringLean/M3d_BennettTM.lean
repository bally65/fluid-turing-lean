import FluidTuringLean.M3c_Bennett

/-!
# Module 3d — 機器級 shuttle Bennett：`bennettTM : BitTM → BitTM`

把 M3c 的動力學層 Bennett 構造下沉為**字面的位元機**：歷史寫進帶本身，
可逆性由 M3b `ofPerm` 引擎免費（README「後續工作：機器級 shuttle Bennett」
5 步攻擊計畫）。

## 佈局決策（milestone A 定案；B/C 可修但先入檔不歸零）

* **狀態打包**：`m' = M.m + ((M.m + 1) + 3)` ——
  M-狀態 `m` 位 × 緩衝 `m+1` 位（= M3c `HistRec`：舊狀態 + 舊讀位）×
  相位 3 位（8 相位）。**無獨立計數器暫存器**：掃描以帶上標記終止
  （README 步驟 4「所有掃描以標記邊界終止」），緩衝內走位用循環旋轉
  `rotBuf`（swap 頭位 → 旋轉一格，`m+1` 次後自動歸位）。
* **帶佈局**：4-軌區塊 —— 模擬帶格 `k` ↦ 帶位 `4k..4k+3` =
  （工作位、垃圾資料位、垃圾標記位、home 標記位）。
* **`L` 的架構**：`Equiv.prodShear phasePerm (fun ph ↦ σ_ph)` 共軛回滿位向量
  —— 相位置換 × 相位別資料子置換，每段都是顯式 `Equiv`，複合用
  `Equiv.trans`，Lean 逐段驗證。子置換原語：
  `feistelCore`（M3c `bufferedStep` 的狀態側版本：新狀態 = `next ⊕ r`、
  寫入位 = `write ⊕ b`、緩衝出 = `(q, a)`）、`swapHead`（緩衝位 0 ↔ 帶位，
  對合）、`rotBuf`（緩衝循環旋轉）、`condPhaseSwap`（帶位條件相位對換）。
* **`μ` 只讀新狀態的相位位** —— `ofPerm` 約束（方向只能依賴更新後狀態）。
* **非法/未用狀態**：`L` 在未 dispatch 的相位走恆等。全空間置換照樣成立，
  模擬引理（milestone C）只對可達的乾淨組態負責。

## 待決清單（milestone B/C，先成文不解）

1. **相位 FSM 可逆分支**：`prodShear` 形狀只給「資料無關的相位置換」；
   讀標記決定走向的分支要用 `condPhaseSwap`（帶位條件相位對換）複合、
   或 `Prod.comm` 共軛的反向 shear。具體轉移圖未定。
2. **垃圾堆疊拖曳排程**：撿底放頂旋轉一格、堆疊與 home 相鄰不變量；
   記錄 `m+1` 位「一位一區塊」跨 `m+1` 個垃圾區塊（傾向）vs 單區塊多位。
3. **乾淨組態謂詞**：標記連續區段 + 未標記格全 0 + 頭在 home 工作位 +
   相位 = 0 + 緩衝 = 空白。
4. **宏步引理歸納結構**：相位 × 區段不變量；爆量時先證單一相位段部分引理。
5. **`encode : M.Cfg → (bennettTM M).Cfg`**：工作帶 4-步幅嵌入 + 垃圾軌全空 +
   home 標記在原點區塊。
6. **M-step 時頭必須在工作位**（`feistelCore` 讀的帶位 = home 區塊 `4k+0`）：
   走位相位的責任，宏步不變量之一。
7. **相位表（草案，8 相位）**：0 = M-step（Feistel）→ 1..5 = 垃圾記錄逐位
   swap-out + 堆疊旋轉走位 → 6 = 回 home → 7 = 未用（恆等）。
   milestone A 的 `phasePerm` 先取單一 8-循環占位，C 再校正。

本檔 milestone A：構造 + 可逆性（零 sorry）。模擬語意**尚未主張** ——
`L` 的微步程式在 B/C 校正時可改，`(bennettTM M).Reversible` 對任何
置換 `L` 都成立，不受影響。
-/

namespace FluidTuring

noncomputable section

/-! ## Bool xor 對合小引理（M3c 的 private 複本） -/

private theorem xor_xor_cancel_right (a b : Bool) : xor (xor a b) a = b := by
  cases a <;> cases b <;> rfl

private theorem xor_xor_cancel_left (a b : Bool) : xor a (xor b a) = b := by
  cases a <;> cases b <;> rfl

/-! ## 位向量打包原語 -/

/-- 位向量拆分：`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`。 -/
def bitsSplit (a b : ℕ) : (Fin (a + b) → Bool) ≃ ((Fin a → Bool) × (Fin b → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- 緩衝拆分：`m+1` 位 ↔（舊狀態 `m` 位, 舊讀位）—— M3c `HistRec` 的位向量版。 -/
def bufSplit (m : ℕ) : (Fin (m + 1) → Bool) ≃ ((Fin m → Bool) × Bool) :=
  (bitsSplit m 1).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) Bool))

/-! ## 相位暫存器 -/

/-- shuttle 機相位暫存器：3 位（8 相位）。 -/
abbrev ShuttlePhase : Type := Fin 3 → Bool

/-- 相位 0（M-step：Feistel 輪）。 -/
def ph0 : ShuttlePhase := fun _ ↦ false

/-- 相位 1（垃圾走位：swap + 旋轉）。 -/
def ph1 : ShuttlePhase := fun j ↦ decide (j = 0)

/-- 相位遞增底層函數（3 位二進位 +1，mod 8）。 -/
private def phaseIncFun (p : ShuttlePhase) : ShuttlePhase := fun j ↦
  if j = 0 then !(p 0)
  else if j = 1 then xor (p 1) (p 0)
  else xor (p 2) (p 0 && p 1)

/-- 相位遞增置換（mod 8 循環）；逆 = 迭代 7 次，有限域 `decide` 驗證
（固定 8 元素，非參數化——與 `bennettTM` 可逆性的參數化證明不同層）。 -/
def phaseInc : ShuttlePhase ≃ ShuttlePhase where
  toFun := phaseIncFun
  invFun := phaseIncFun^[7]
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

/-! ## 微步子置換原語 -/

/-- 緩衝位 0 ↔ 帶位交換的底層函數（對合）。 -/
private def swapHeadFun (m : ℕ) (p : (Fin (m + 1) → Bool) × Bool) :
    (Fin (m + 1) → Bool) × Bool :=
  (fun j ↦ if j = 0 then p.2 else p.1 j, p.1 0)

private theorem swapHeadFun_invol (m : ℕ) (p : (Fin (m + 1) → Bool) × Bool) :
    swapHeadFun m (swapHeadFun m p) = p := by
  obtain ⟨v, a⟩ := p
  simp only [swapHeadFun]
  refine Prod.ext (funext fun j ↦ ?_) ?_
  · rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [if_neg hj]
  · simp

/-- 緩衝位 0 ↔ 帶位交換（對合置換）。 -/
def swapHead (m : ℕ) : ((Fin (m + 1) → Bool) × Bool) ≃ ((Fin (m + 1) → Bool) × Bool) where
  toFun := swapHeadFun m
  invFun := swapHeadFun m
  left_inv := swapHeadFun_invol m
  right_inv := swapHeadFun_invol m

/-- 緩衝循環旋轉一格（`m+1` 次復位；配合 `swapHead` 實現記錄逐位搬運）。 -/
def rotBuf (m : ℕ) : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) :=
  Equiv.arrowCongr (finRotate (m + 1)) (Equiv.refl Bool)

/-- 相位分派：相位 = `ph` 時對資料作用 `σ`，否則恆等；相位分量不動
（`Equiv.prodShear`——每相位纖維各自雙射 ⟹ 整體置換）。 -/
def phaseDispatch {α : Type*} (ph : ShuttlePhase) (σ : α ≃ α) :
    (ShuttlePhase × α) ≃ (ShuttlePhase × α) :=
  Equiv.prodShear (Equiv.refl ShuttlePhase) (fun p ↦ if p = ph then σ else Equiv.refl α)

/-- 垃圾走位子置換（占位排程）：緩衝頭位 ↔ 帶位交換，然後緩衝旋轉一格。
`m+1` 次後緩衝復位 —— 記錄逐位搬上帶的原語形狀。 -/
def garbagePiece (m : ℕ) : (((Fin m → Bool) × (Fin (m + 1) → Bool)) × Bool) ≃
    (((Fin m → Bool) × (Fin (m + 1) → Bool)) × Bool) :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _)
      ((swapHead m).trans (Equiv.prodCongr (rotBuf m) (Equiv.refl Bool)))).trans
      (Equiv.prodAssoc _ _ _).symm)

/-- 重排：`(狀態 × (緩衝 × 相位)) × 帶位 ≃ 相位 × ((狀態 × 緩衝) × 帶位)`
（顯式重括號，結構 eta 使兩側 `rfl`）。 -/
private def reorderAux {α β γ : Type*} : ((α × (β × γ)) × Bool) ≃ (γ × ((α × β) × Bool)) where
  toFun x := (x.1.2.2, ((x.1.1, x.1.2.1), x.2))
  invFun y := ((y.2.1.1, (y.2.1.2, y.1)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 機器級構造 -/

namespace BitTM

variable (M : BitTM)

/-- shuttle 機狀態位數：M-狀態 `m` 位 + 緩衝 `m+1` 位 + 相位 3 位。 -/
abbrev shuttleBits : ℕ := M.m + ((M.m + 1) + 3)

/-- 狀態打包：滿位向量 ↔（M-狀態, 緩衝, 相位）。 -/
def shuttleUnpack : (Fin M.shuttleBits → Bool) ≃
    ((Fin M.m → Bool) × ((Fin (M.m + 1) → Bool) × ShuttlePhase)) :=
  (bitsSplit M.m ((M.m + 1) + 3)).trans
    (Equiv.prodCongr (Equiv.refl _) (bitsSplit (M.m + 1) 3))

/-- **Feistel M-step 核心**（M3c `bufferedStep` 的狀態側版本）：
輸入 `((q, (r, b)), a)` ↦ `((next q a ⊕ r, (q, a)), write q a ⊕ b)` ——
新狀態 = `next ⊕ r`（逐位）、緩衝出 = 被丟棄的 `(q, a)`、寫入位 = `write ⊕ b`。
顯式雙射：一切可由緩衝出的 `(q, a)` 重建。 -/
def feistelCore : (((Fin M.m → Bool) × ((Fin M.m → Bool) × Bool)) × Bool) ≃
    (((Fin M.m → Bool) × ((Fin M.m → Bool) × Bool)) × Bool) where
  toFun p := ((fun j ↦ xor (M.next p.1.1 p.2 j) (p.1.2.1 j), (p.1.1, p.2)),
    xor (M.write p.1.1 p.2) p.1.2.2)
  invFun p := ((p.1.2.1,
    (fun j ↦ xor (p.1.1 j) (M.next p.1.2.1 p.1.2.2 j), xor p.2 (M.write p.1.2.1 p.1.2.2))),
    p.1.2.2)
  left_inv := by
    rintro ⟨⟨q, r, b⟩, a⟩
    refine Prod.ext (Prod.ext rfl (Prod.ext (funext fun j ↦ ?_) ?_)) rfl
    · exact xor_xor_cancel_right _ _
    · exact xor_xor_cancel_right _ _
  right_inv := by
    rintro ⟨⟨p, q, a⟩, c⟩
    refine Prod.ext (Prod.ext (funext fun j ↦ ?_) rfl) ?_
    · exact xor_xor_cancel_left _ _
    · exact xor_xor_cancel_left _ _

/-- Feistel 核心搬到（M-狀態 × 緩衝）× 帶位（緩衝經 `bufSplit` 拆成
舊狀態槽 + 舊讀位槽）。 -/
def feistelPiece : (((Fin M.m → Bool) × (Fin (M.m + 1) → Bool)) × Bool) ≃
    (((Fin M.m → Bool) × (Fin (M.m + 1) → Bool)) × Bool) :=
  (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (bufSplit M.m)) (Equiv.refl Bool)).trans
    (M.feistelCore.trans
      (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (bufSplit M.m).symm) (Equiv.refl Bool)))

/-- 相位分派核心（**占位排程**：相位 0 = Feistel M-step、相位 1 = 垃圾走位、
其餘恆等；每微步後相位 +1）。milestone C 換成標記驅動的可逆分支排程
（待決清單 1、7）—— 換排程不影響本檔的可逆性定理。 -/
def shuttleCore :
    (ShuttlePhase × (((Fin M.m → Bool) × (Fin (M.m + 1) → Bool)) × Bool)) ≃
    (ShuttlePhase × (((Fin M.m → Bool) × (Fin (M.m + 1) → Bool)) × Bool)) :=
  (phaseDispatch ph0 M.feistelPiece).trans
    ((phaseDispatch ph1 (garbagePiece M.m)).trans
      (Equiv.prodCongr phaseInc (Equiv.refl _)))

/-- **局部更新置換 `L`**（README 步驟 1、3）：打包共軛的相位分派核心。
全空間置換 —— 非法/未用相位走恆等。 -/
def shuttleL : ((Fin M.shuttleBits → Bool) × Bool) ≃ ((Fin M.shuttleBits → Bool) × Bool) :=
  ((Equiv.prodCongr M.shuttleUnpack (Equiv.refl Bool)).trans reorderAux).trans
    (M.shuttleCore.trans
      (reorderAux.symm.trans (Equiv.prodCongr M.shuttleUnpack.symm (Equiv.refl Bool))))

/-- **方向表 `μ`**：只讀新狀態的相位位（`ofPerm` 約束：方向只能依賴更新後
狀態）。占位：垃圾走位相位向左、其餘停 —— milestone C 校正。 -/
def shuttleDir (s : Fin M.shuttleBits → Bool) : Dir :=
  if (M.shuttleUnpack s).2.2 = ph1 then Dir.left else Dir.stay

/-- **機器級 Bennett 構造**（README 步驟 1–3 骨架）：`ofPerm` 打包。
milestone A 只主張構造存在 + 可逆；模擬語意 = 待決清單（見檔頭）。 -/
def bennettTM : BitTM := BitTM.ofPerm M.shuttleBits M.shuttleL M.shuttleDir

/-- **可逆性免費**：`ofPerm` 引擎一次付清（README 步驟 1）——
對任何置換 `L` 成立，不依賴微步排程的語意正確性。 -/
theorem bennettTM_reversible : M.bennettTM.Reversible :=
  ofPerm_reversible M.shuttleBits M.shuttleL M.shuttleDir

@[simp] theorem bennettTM_m : M.bennettTM.m = M.shuttleBits := rfl

theorem bennettTM_next (s : Fin M.shuttleBits → Bool) (a : Bool) :
    M.bennettTM.next s a = (M.shuttleL (s, a)).1 := rfl

theorem bennettTM_write (s : Fin M.shuttleBits → Bool) (a : Bool) :
    M.bennettTM.write s a = (M.shuttleL (s, a)).2 := rfl

theorem bennettTM_move (s : Fin M.shuttleBits → Bool) (a : Bool) :
    M.bennettTM.move s a = M.shuttleDir (M.shuttleL (s, a)).1 := rfl

/-! ## Milestone B（部分）：帶佈局、編碼與乾淨組態謂詞

4-軌帶佈局（README 步驟 2 帶側）：模擬帶格 `k` ↦ shuttle 帶位 `4k..4k+3` =
（工作位 `4k`、垃圾資料位 `4k+1`、垃圾標記位 `4k+2`、home 標記位 `4k+3`）。

**誠實界線**：本節只給排程無關的部分 —— 編碼、乾淨組態謂詞、
「編碼產出乾淨組態」。每類微步保不變量的單步引理**綁定微步排程**，
而現行排程是占位（見 `shuttleCore` docstring），故與 milestone C 的
標記驅動排程一起做，避免對將被替換的排程證死引理。 -/

/-- 空白緩衝。 -/
def blankBuf : Fin (M.m + 1) → Bool := fun _ ↦ false

/-- 打包 shuttle 狀態（`shuttleUnpack` 的逆）。 -/
def shuttlePack (q : Fin M.m → Bool) (buf : Fin (M.m + 1) → Bool) (p : ShuttlePhase) :
    Fin M.shuttleBits → Bool :=
  M.shuttleUnpack.symm (q, (buf, p))

@[simp] theorem shuttleUnpack_shuttlePack (q : Fin M.m → Bool)
    (buf : Fin (M.m + 1) → Bool) (p : ShuttlePhase) :
    M.shuttleUnpack (M.shuttlePack q buf p) = (q, (buf, p)) :=
  M.shuttleUnpack.apply_symm_apply _

/-- 編碼帶：工作軌載模擬帶、垃圾兩軌全空、home 標記唯一在區塊 0。 -/
def shuttleEncodeTape (t : ℤ → Bool) : ℤ → Bool := fun i ↦
  if i % 4 = 0 then t (i / 4)
  else if i = 3 then true
  else false

/-- **編碼**：模擬組態 → shuttle 機組態（相位 0、緩衝空白、垃圾空、
head 在 home 區塊工作位）。 -/
def shuttleEncode (c : M.Cfg) : M.bennettTM.Cfg :=
  (M.shuttlePack c.1 M.blankBuf ph0, shuttleEncodeTape c.2)

/-- **乾淨組態謂詞**（垃圾堆疊長 `L`；垃圾內容自由 —— 宏步引理中
以存在量詞外顯，語意比照 M3c `bennettAut_iterate`）：
相位 0、緩衝空白、工作軌 = 模擬帶、home 標記唯一在區塊 0、
垃圾標記恰為區塊 `[-L, 0)` 的連續區段（與 home 相鄰）、未標記垃圾格 = 0。 -/
def IsClean (L : ℕ) (c : M.bennettTM.Cfg) (q : Fin M.m → Bool) (t : ℤ → Bool) : Prop :=
  M.shuttleUnpack c.1 = (q, (M.blankBuf, ph0)) ∧
  (∀ k : ℤ, c.2 (4 * k) = t k) ∧
  (∀ k : ℤ, c.2 (4 * k + 3) = decide (k = 0)) ∧
  (∀ k : ℤ, c.2 (4 * k + 2) = decide (-(L : ℤ) ≤ k ∧ k < 0)) ∧
  (∀ k : ℤ, c.2 (4 * k + 2) = false → c.2 (4 * k + 1) = false)

/-- **編碼產出乾淨組態**（垃圾堆疊長 0）。 -/
theorem shuttleEncode_isClean (c : M.Cfg) :
    M.IsClean 0 (M.shuttleEncode c) c.1 c.2 := by
  refine ⟨M.shuttleUnpack_shuttlePack _ _ _, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · change shuttleEncodeTape c.2 (4 * k) = c.2 k
    simp only [shuttleEncodeTape]
    rw [if_pos (by omega : (4 * k) % 4 = 0),
      Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)]
  · change shuttleEncodeTape c.2 (4 * k + 3) = decide (k = 0)
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(4 * k + 3) % 4 = 0)]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos (by omega : (4 * (0 : ℤ) + 3) = 3), eq_comm]
      exact decide_eq_true rfl
    · rw [if_neg (by omega : ¬(4 * k + 3) = 3), eq_comm]
      exact decide_eq_false hk
  · change shuttleEncodeTape c.2 (4 * k + 2) = decide (-(0 : ℤ) ≤ k ∧ k < 0)
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(4 * k + 2) % 4 = 0), if_neg (by omega : ¬(4 * k + 2) = 3),
      eq_comm]
    exact decide_eq_false (by omega)
  · intro _
    change shuttleEncodeTape c.2 (4 * k + 1) = false
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(4 * k + 1) % 4 = 0), if_neg (by omega : ¬(4 * k + 1) = 3)]

end BitTM

end

end FluidTuring
