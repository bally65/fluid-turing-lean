import FluidTuringLean.M3_Encoding

/-!
# Module 3b — 可逆位元圖靈機 → generalized shift（定理鏈離散端）

把定理鏈的離散端缺口「TM → 可逆 generalized shift」補上：

* `BitTM`：自足的雙向無限帶圖靈機模型（moving-tape 慣例，頭永遠在帶位 0），
  狀態空間取**滿位向量** `Fin m → Bool`。
* `BitTM.encCfg`：組態空間 `(Fin m → Bool) × (ℤ → Bool)` 與 `(ℤ → Bool)` 的
  **顯式雙射**打包（狀態塊插在 `[0, m)`、帶右半平移讓位）。
* `GenShift.ofLocal`：由「平移量局部、落點在視窗外=純平移、落點在視窗內=只看視窗」
  三條件直接打包出 `GenShift`。
* `BitTM.toGenShift`：機器單步在編碼下實現為 generalized shift（視窗
  `[-1, m]`），且 `M.step` 雙射 ⟹ `toGenShift.Reversible` —— 可直接餵
  M6 的 `genShift_suspension_simulates`。
* `BitTM.LocalReversible`：**局部可判定**（有限檢查）的可逆充分條件，
  蘊含 `M.step` 雙射；實例 `cnotTM`（受控反閘機）以 `decide` 驗證。
* `BitTM.ofPerm`：**置換機打包器** —— 局部更新 `(q,a) ↦ (next, write)` 是
  `(狀態 × 位元)` 上的置換且 `move` 只依賴新狀態 ⟹ `LocalReversible`
  （`ofPerm_localReversible`，參數化證明、不能 `decide`）。
  機器級可逆完備化的可逆性引擎：設計者給置換，鋪磚一次付清。

## 模型取捨（為何不用 mathlib `Turing.TM0`）

mathlib 的 `Turing.TM0` 帶是 `Turing.Tape`（`ListBlank` 商型別，
「最終常值」序列的商），組態不含整條 `ℤ → Γ` 帶；對接 `(ℤ → Bool)`
乘積空間要先跨過商型別與最終常值子空間兩道牆，且其 step 是
`Option`-值（含停機）。本檔自定義模型直接住在目標空間旁：

* 狀態空間取滿位向量 `Fin m → Bool`（`2^m` 個狀態）而非抽象有限型別 ——
  這使 `encCfg` 是**雙射**而非僅單射，可逆性（雙射）能整包共軛搬到編碼側；
  抽象 `Q` 的非滿編碼會在 `(ℤ → Bool)` 留下「非法組態」破壞滿射性。
  任意有限狀態集都可補位嵌入位向量，不失一般性。
* moving-tape 慣例（頭固定在 0、帶反向平移）正是 generalized shift 的
  「平移 + 視窗改寫」形狀；moving-head 慣例反而要先共軛一次。

## 可逆性的兩層

* `BitTM.Reversible`：全域定義 —— `step` 在組態空間上**雙射**。
  注意單射不夠：`GenShift.Reversible` 需要雙射，而單射 TM 步進不必滿
 （Moore–Myhill 花園伊甸園式論證不在本檔範圍）。
* `BitTM.LocalReversible`：局部有限檢查 —— 每個「目標狀態 × 三方向寫入位
  指定」恰有一個（舊狀態, 讀入位）轉移到它（`2^m·8` 個槽被 `2^{m+1}` 條
  轉移各覆蓋 4 槽的精確鋪磚）。`LocalReversible.reversible` 證明它蘊含雙射。

## 里程碑 B（部分）：Bennett 1973 可逆化

`bennett f`：history-keeping 構造（丟棄的資訊全押進歷史欄）。已證：
單射（`bennett_injective`）、n 步模擬（`bennett_iterate_fst`）。
**誠實缺口**：`bennett_not_surjective` 證明此抽象構造**永不滿射**
（`(x₀, [])` 無前像），故不能直接給出 `GenShift.Reversible` 所需的雙射。
此缺口已在 **M3c**（history conveyor：歷史容器換成雙向無限流 `ℤ → V`，
「空歷史」角點不存在）於**動力學層**封死；字面的機器級
`bennettTM : BitTM → BitTM`（歷史寫進帶）仍是後續工作，其可逆性那半
可由本檔 `ofPerm` 引擎付清。

本檔零 sorry。
-/

namespace FluidTuring

noncomputable section

/-! ## 讀寫頭方向 -/

/-- 讀寫頭移動方向。 -/
inductive Dir : Type
  | left
  | stay
  | right
deriving DecidableEq, Fintype

/-- 方向對應的帶平移量（moving-tape：頭右移 = 帶左移一格 = 平移 `+1`）。 -/
def Dir.toInt : Dir → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem Dir.toInt_cases (d : Dir) : d.toInt = -1 ∨ d.toInt = 0 ∨ d.toInt = 1 := by
  cases d <;> simp [Dir.toInt]

/-! ## 由局部資料打包 generalized shift -/

namespace GenShift

/-- 由「局部資料」直接打包 generalized shift：給定視窗 `W`、只依賴視窗的
平移量 `F`、全域映射 `Φ`，只要 `Φ` 在「落點在視窗外」的座標上是純平移、
在「落點在視窗內」的座標上只依賴視窗，就得到 `GenShift` 且其作用恰為 `Φ`
（`ofLocal_apply`）。改寫函數取 `G s i = Φ s (i - F s)`。 -/
def ofLocal (W : Finset ℤ) (F : (ℤ → Bool) → ℤ) (Φ : (ℤ → Bool) → (ℤ → Bool))
    (hF : ∀ {s s' : ℤ → Bool}, (∀ i ∈ W, s i = s' i) → F s = F s')
    (hoff : ∀ (s : ℤ → Bool) (n : ℤ), n + F s ∉ W → Φ s n = s (n + F s))
    (hloc : ∀ {s s' : ℤ → Bool}, (∀ i ∈ W, s i = s' i) →
      ∀ n : ℤ, n + F s ∈ W → Φ s n = Φ s' n) : GenShift where
  window := W
  shiftAmt := F
  rewrite s i := Φ s (i - F s)
  shiftAmt_local := hF
  rewrite_local := by
    intro s s' hss' i hi
    have hFs : F s = F s' := hF hss'
    rw [← hFs]
    exact hloc hss' (i - F s) (by rw [sub_add_cancel]; exact hi)
  rewrite_off := by
    intro s i hiW
    have h1 : i - F s + F s = i := by ring
    rw [hoff s (i - F s) (by rw [h1]; exact hiW), h1]

@[simp] theorem ofLocal_apply (W : Finset ℤ) (F : (ℤ → Bool) → ℤ)
    (Φ : (ℤ → Bool) → (ℤ → Bool)) (hF hoff hloc) :
    (ofLocal W F Φ hF hoff hloc).apply = Φ := by
  funext s n
  have h1 : n + F s - F s = n := by ring
  change Φ s (n + F s - F s) = Φ s n
  rw [h1]

end GenShift

/-! ## 位元圖靈機模型 -/

/-- 自足的雙向無限帶圖靈機（moving-tape 慣例）：`m` 個狀態位元
（狀態空間 = 滿位向量 `Fin m → Bool`）、帶字母 `Bool`、讀寫頭固定讀帶位 `0`。
單步 = 讀 `(狀態, 帶位 0)` → 寫回帶位 0、換態、帶反向平移一格。 -/
structure BitTM where
  /-- 狀態位元數；狀態空間 = `Fin m → Bool`（`2^m` 個狀態）。 -/
  m : ℕ
  /-- 轉移：新狀態。 -/
  next : (Fin m → Bool) → Bool → (Fin m → Bool)
  /-- 轉移：寫入位。 -/
  write : (Fin m → Bool) → Bool → Bool
  /-- 轉移：頭移動方向。 -/
  move : (Fin m → Bool) → Bool → Dir

namespace BitTM

variable (M : BitTM)

/-- 組態空間：狀態 × 雙向無限帶（頭在帶位 0）。 -/
abbrev Cfg : Type := (Fin M.m → Bool) × (ℤ → Bool)

/-- 單步轉移：讀 `c.2 0`，寫、換態、依方向平移帶
（moving-tape：`t' n = t_w (n + d)`，`t_w` = 寫入後的帶）。 -/
def step (c : M.Cfg) : M.Cfg :=
  (M.next c.1 (c.2 0),
   fun n ↦ if n + (M.move c.1 (c.2 0)).toInt = 0 then M.write c.1 (c.2 0)
           else c.2 (n + (M.move c.1 (c.2 0)).toInt))

theorem step_eval (q : Fin M.m → Bool) (t : ℤ → Bool) :
    M.step (q, t) =
      (M.next q (t 0),
       fun n ↦ if n + (M.move q (t 0)).toInt = 0 then M.write q (t 0)
               else t (n + (M.move q (t 0)).toInt)) := rfl

/-- 可逆性（全域）：單步轉移在組態空間上雙射。 -/
def Reversible : Prop := Function.Bijective M.step

/-! ### 組態 ↔ `(ℤ → Bool)` 的雙射打包

狀態塊佔 `[0, m)`，帶右半（`t 0` 起，含讀寫頭讀的格）平移到 `[m, ∞)`，
帶左半留在 `(-∞, 0)`。讀寫頭讀的 `t 0` 落在編碼位 `m`。 -/

/-- 打包：`[0,m)` = 狀態位、`[m,∞)` = 帶右半（`s i = t (i - m)`）、
`(-∞,0)` = 帶左半。 -/
def pack (c : M.Cfg) : ℤ → Bool := fun i ↦
  if h : 0 ≤ i ∧ i < (M.m : ℤ) then c.1 ⟨i.toNat, by omega⟩
  else if 0 ≤ i then c.2 (i - M.m) else c.2 i

/-- 解包：狀態位。 -/
def stateOf (s : ℤ → Bool) : Fin M.m → Bool := fun j ↦ s ((j : ℕ) : ℤ)

/-- 解包：讀寫頭正讀的帶位（帶位 0 = 編碼位 `m`）。 -/
def symbolOf (s : ℤ → Bool) : Bool := s (M.m : ℤ)

/-- 解包：整條帶。 -/
def unpackTape (s : ℤ → Bool) : ℤ → Bool := fun n ↦ if 0 ≤ n then s (n + M.m) else s n

/-- 解包：組態。 -/
def unpack (s : ℤ → Bool) : M.Cfg := (M.stateOf s, M.unpackTape s)

theorem pack_state (q : Fin M.m → Bool) (t : ℤ → Bool) {i : ℤ}
    (h0 : 0 ≤ i) (hm : i < (M.m : ℤ)) :
    M.pack (q, t) i = q ⟨i.toNat, by omega⟩ := by
  simp only [pack]
  rw [dif_pos ⟨h0, hm⟩]

theorem pack_right (q : Fin M.m → Bool) (t : ℤ → Bool) {i : ℤ} (h : (M.m : ℤ) ≤ i) :
    M.pack (q, t) i = t (i - M.m) := by
  simp only [pack]
  rw [dif_neg (by omega), if_pos (by omega)]

theorem pack_left (q : Fin M.m → Bool) (t : ℤ → Bool) {i : ℤ} (h : i < 0) :
    M.pack (q, t) i = t i := by
  simp only [pack]
  rw [dif_neg (by omega), if_neg (by omega)]

theorem unpackTape_nonneg (s : ℤ → Bool) {k : ℤ} (h : 0 ≤ k) :
    M.unpackTape s k = s (k + M.m) := by
  simp only [unpackTape]
  rw [if_pos h]

theorem unpackTape_neg (s : ℤ → Bool) {k : ℤ} (h : k < 0) : M.unpackTape s k = s k := by
  simp only [unpackTape]
  rw [if_neg (by omega)]

theorem unpackTape_zero (s : ℤ → Bool) : M.unpackTape s 0 = M.symbolOf s := by
  have h := M.unpackTape_nonneg s (k := 0) le_rfl
  rw [zero_add] at h
  exact h

theorem unpack_pack (c : M.Cfg) : M.unpack (M.pack c) = c := by
  obtain ⟨q, t⟩ := c
  refine Prod.ext ?_ ?_
  · funext j
    exact (M.pack_state q t (i := ((j : ℕ) : ℤ)) (by omega)
      (by have := j.isLt; omega)).trans rfl
  · funext n
    rcases lt_or_ge n 0 with hneg | h0
    · calc (M.unpack (M.pack (q, t))).2 n
          = M.pack (q, t) n := M.unpackTape_neg _ hneg
        _ = t n := M.pack_left q t hneg
    · calc (M.unpack (M.pack (q, t))).2 n
          = M.pack (q, t) (n + M.m) := M.unpackTape_nonneg _ h0
        _ = t (n + M.m - M.m) := M.pack_right q t (by omega)
        _ = t n := by congr 1; ring

theorem pack_unpack (s : ℤ → Bool) : M.pack (M.unpack s) = s := by
  funext i
  rcases lt_or_ge i 0 with hneg | h0
  · calc M.pack (M.unpack s) i
        = M.unpackTape s i := M.pack_left _ _ hneg
      _ = s i := M.unpackTape_neg _ hneg
  · rcases lt_or_ge i (M.m : ℤ) with hm | hm
    · calc M.pack (M.unpack s) i
          = M.stateOf s ⟨i.toNat, by omega⟩ := M.pack_state _ _ h0 hm
        _ = s ((i.toNat : ℕ) : ℤ) := rfl
        _ = s i := by congr 1; omega
    · calc M.pack (M.unpack s) i
          = M.unpackTape s (i - M.m) := M.pack_right _ _ hm
        _ = s (i - M.m + M.m) := M.unpackTape_nonneg _ (by omega)
        _ = s i := by congr 1; ring

/-- **組態空間 ≃ `(ℤ → Bool)`**：打包是雙射（同胚級 —— 兩側都是逐座標讀取，
但本檔只需要雙射；連續性由 `GenShift.continuous_apply` 在編碼側整包免費）。 -/
def encCfg : M.Cfg ≃ (ℤ → Bool) where
  toFun := M.pack
  invFun := M.unpack
  left_inv := M.unpack_pack
  right_inv := M.pack_unpack

/-! ### 編碼側單步 = generalized shift -/

/-- 依賴視窗：`[-1, m]`（狀態塊 `[0,m)`、讀入位 `m`、左移時要讀的 `-1`）。 -/
def window : Finset ℤ := Finset.Icc (-1) (M.m : ℤ)

/-- 平移量：由（狀態, 讀入位）查方向。 -/
def shiftOf (s : ℤ → Bool) : ℤ := (M.move (M.stateOf s) (M.symbolOf s)).toInt

theorem shiftOf_cases (s : ℤ → Bool) :
    M.shiftOf s = -1 ∨ M.shiftOf s = 0 ∨ M.shiftOf s = 1 :=
  Dir.toInt_cases _

/-- 編碼側單步：`(ℤ → Bool)` 上與 `M.step` 共軛的映射。 -/
def encStep (s : ℤ → Bool) : ℤ → Bool := M.pack (M.step (M.unpack s))

/-- 編碼側單步的顯式形狀：`pack (新狀態, 寫入後平移的帶)`。 -/
theorem encStep_eval (s : ℤ → Bool) :
    M.encStep s = M.pack
      (M.next (M.stateOf s) (M.symbolOf s),
       fun k ↦ if k + M.shiftOf s = 0 then M.write (M.stateOf s) (M.symbolOf s)
               else M.unpackTape s (k + M.shiftOf s)) := by
  simp only [encStep, step, unpack, unpackTape_zero, shiftOf]

theorem stateOf_congr {s s' : ℤ → Bool} (h : ∀ i ∈ M.window, s i = s' i) :
    M.stateOf s = M.stateOf s' := by
  funext j
  refine h _ (Finset.mem_Icc.mpr ?_)
  have := j.isLt
  omega

theorem symbolOf_congr {s s' : ℤ → Bool} (h : ∀ i ∈ M.window, s i = s' i) :
    M.symbolOf s = M.symbolOf s' :=
  h _ (Finset.mem_Icc.mpr (by omega))

theorem shiftOf_congr {s s' : ℤ → Bool} (h : ∀ i ∈ M.window, s i = s' i) :
    M.shiftOf s = M.shiftOf s' := by
  simp only [shiftOf]
  rw [M.stateOf_congr h, M.symbolOf_congr h]

/-- 落點在視窗外 ⟹ 編碼側單步是純平移。 -/
theorem encStep_off (s : ℤ → Bool) (n : ℤ) (hn : n + M.shiftOf s ∉ M.window) :
    M.encStep s n = s (n + M.shiftOf s) := by
  have hd := M.shiftOf_cases s
  have hn' : n + M.shiftOf s < -1 ∨ (M.m : ℤ) < n + M.shiftOf s := by
    rcases lt_or_ge (n + M.shiftOf s) (-1) with h1 | h1
    · exact Or.inl h1
    · rcases lt_or_ge (M.m : ℤ) (n + M.shiftOf s) with h2 | h2
      · exact Or.inr h2
      · exact absurd (Finset.mem_Icc.mpr ⟨h1, h2⟩) hn
  rw [M.encStep_eval s]
  rcases lt_or_ge n 0 with hneg | h0
  · rw [M.pack_left _ _ hneg]
    rw [if_neg (by omega), M.unpackTape_neg _ (by omega)]
  · rcases lt_or_ge n (M.m : ℤ) with hm | hm
    · exfalso
      omega
    · rw [M.pack_right _ _ hm]
      rw [if_neg (by omega), M.unpackTape_nonneg _ (by omega)]
      congr 1
      ring

/-- 落點在視窗內 ⟹ 編碼側單步只依賴視窗。 -/
theorem encStep_local {s s' : ℤ → Bool} (hss' : ∀ i ∈ M.window, s i = s' i)
    (n : ℤ) (hn : n + M.shiftOf s ∈ M.window) : M.encStep s n = M.encStep s' n := by
  have hd := M.shiftOf_cases s
  have hn' : -1 ≤ n + M.shiftOf s ∧ n + M.shiftOf s ≤ (M.m : ℤ) := Finset.mem_Icc.mp hn
  have hstate := M.stateOf_congr hss'
  have hsym := M.symbolOf_congr hss'
  have hshift := M.shiftOf_congr hss'
  rw [M.encStep_eval s, M.encStep_eval s', ← hstate, ← hsym, ← hshift]
  rcases lt_or_ge n 0 with hneg | h0
  · rw [M.pack_left _ _ hneg, M.pack_left _ _ hneg]
    rcases eq_or_ne (n + M.shiftOf s) 0 with hz | hz
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz, M.unpackTape_neg _ (by omega), M.unpackTape_neg _ (by omega)]
      exact hss' _ (Finset.mem_Icc.mpr (by omega))
  · rcases lt_or_ge n (M.m : ℤ) with hm | hm
    · rw [M.pack_state _ _ h0 hm, M.pack_state _ _ h0 hm]
    · rw [M.pack_right _ _ hm, M.pack_right _ _ hm]
      rcases eq_or_ne (n - M.m + M.shiftOf s) 0 with hz | hz
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz, M.unpackTape_neg _ (by omega), M.unpackTape_neg _ (by omega)]
        exact hss' _ (Finset.mem_Icc.mpr (by omega))

/-- **機器單步實現為 generalized shift**：視窗 `[-1, m]`、平移量 `shiftOf`、
作用 = 編碼側單步。 -/
def toGenShift : GenShift :=
  GenShift.ofLocal M.window M.shiftOf M.encStep
    (fun h ↦ M.shiftOf_congr h) M.encStep_off (fun h ↦ M.encStep_local h)

@[simp] theorem toGenShift_apply : M.toGenShift.apply = M.encStep :=
  GenShift.ofLocal_apply _ _ _ _ _ _

/-- **可逆性搬運**：機器可逆（`step` 雙射）⟹ 其 generalized shift 可逆。
證明 = 沿雙射 `encCfg` 共軛。 -/
theorem Reversible.toGenShift (h : M.Reversible) : M.toGenShift.Reversible := by
  have he : M.encStep = ⇑M.encCfg ∘ M.step ∘ ⇑M.encCfg.symm := rfl
  unfold GenShift.Reversible
  rw [M.toGenShift_apply, he]
  exact M.encCfg.bijective.comp (h.comp M.encCfg.symm.bijective)

/-! ### 局部可判定的可逆條件

`step` 的前像分析：組態 `(p, u)` 的前像由（舊狀態 `q`, 讀入位 `a`）決定 ——
帶除頭位外由 `u` 反平移唯一重建，頭位 = `a`，而寫入位必須吻合
`u (-(方向))`。故雙射 ⟺ 每個「目標狀態 × 各方向寫入位指定 `β`」恰有一個
`(q, a)`。這是 `2^m · 2^3` 個槽對 `2^{m+1}` 條轉移（各覆蓋 4 槽）的
精確鋪磚 —— **有限可判定**（實例可 `decide`）。 -/

/-- 局部可逆條件：每個（目標狀態 `p`, 方向別寫入位指定 `β`）恰有一個
（舊狀態, 讀入位）轉移到它。 -/
def LocalReversible : Prop :=
  ∀ (p : Fin M.m → Bool) (β : Dir → Bool),
    ∃! qa : (Fin M.m → Bool) × Bool,
      M.next qa.1 qa.2 = p ∧ M.write qa.1 qa.2 = β (M.move qa.1 qa.2)

/-- 局部可逆 ⟹ 全域可逆（`step` 雙射）。 -/
theorem LocalReversible.reversible (h : M.LocalReversible) : M.Reversible := by
  constructor
  · -- 單射：兩前像的（狀態, 讀入位）命中同一 (p, β) 槽，由唯一性重合；帶由像重建。
    rintro ⟨q, t⟩ ⟨q', t'⟩ heq
    have hfst : M.next q (t 0) = M.next q' (t' 0) := congrArg Prod.fst heq
    have hsnd : ∀ n, (M.step (q, t)).2 n = (M.step (q', t')).2 n :=
      fun n ↦ congrFun (congrArg Prod.snd heq) n
    set d := (M.move q (t 0)).toInt with hd
    set d' := (M.move q' (t' 0)).toInt with hd'
    have hw : (M.step (q, t)).2 (-d) = M.write q (t 0) := by
      rw [M.step_eval q t]
      dsimp only
      rw [if_pos (by omega)]
    have hw' : (M.step (q', t')).2 (-d') = M.write q' (t' 0) := by
      rw [M.step_eval q' t']
      dsimp only
      rw [if_pos (by omega)]
    obtain ⟨qa₀, -, huniq⟩ := h (M.next q (t 0)) (fun dir ↦ (M.step (q, t)).2 (-(dir.toInt)))
    have h1 : ((q, t 0) : (Fin M.m → Bool) × Bool) = qa₀ := by
      refine huniq _ ⟨rfl, ?_⟩
      dsimp only
      rw [← hd]
      exact hw.symm
    have h2 : ((q', t' 0) : (Fin M.m → Bool) × Bool) = qa₀ := by
      refine huniq _ ⟨hfst.symm, ?_⟩
      dsimp only
      rw [← hd', hsnd (-d')]
      exact hw'.symm
    have hqa : ((q, t 0) : (Fin M.m → Bool) × Bool) = (q', t' 0) := h1.trans h2.symm
    have hq : q = q' := congrArg Prod.fst hqa
    have ha : t 0 = t' 0 := congrArg Prod.snd hqa
    have hdd : d = d' := by rw [hd, hd', hq, ha]
    refine Prod.ext hq (funext fun k ↦ ?_)
    rcases eq_or_ne k 0 with rfl | hk
    · exact ha
    · have hs := hsnd (k - d)
      rw [M.step_eval q t, M.step_eval q' t'] at hs
      dsimp only at hs
      rw [← hd, ← hd', ← hdd] at hs
      rw [if_neg (by omega), if_neg (by omega)] at hs
      have hkd : k - d + d = k := by ring
      rwa [hkd] at hs
  · -- 滿射：由槽 (p, β) 的存在性取 (q, a)，帶由目標反平移重建。
    rintro ⟨p, u⟩
    obtain ⟨⟨q, a⟩, ⟨hnext, hwrite⟩, -⟩ := h p (fun dir ↦ u (-(dir.toInt)))
    have hnext' : M.next q a = p := hnext
    have hwrite' : M.write q a = u (-(M.move q a).toInt) := hwrite
    refine ⟨(q, fun k ↦ if k = 0 then a else u (k - (M.move q a).toInt)), ?_⟩
    have ht0 : (if (0 : ℤ) = 0 then a else u (0 - (M.move q a).toInt)) = a := if_pos rfl
    rw [M.step_eval, ht0]
    refine Prod.ext hnext' (funext fun n ↦ ?_)
    dsimp only
    rcases eq_or_ne (n + (M.move q a).toInt) 0 with hz | hz
    · rw [if_pos hz, hwrite']
      congr 1
      omega
    · rw [if_neg hz, if_neg hz]
      congr 1
      ring

/-! ### 置換機：機器級可逆完備化引擎

`LocalReversible` 的鋪磚條件有個乾淨的充分形式：**局部更新
`(q, a) ↦ (next q a, write q a)` 是 `(狀態 × 位元)` 上的置換，且移動方向只依賴
更新後的新狀態**。此時目標槽 `(p, β)` 的唯一前像就是 `L.symm (p, β (μ p))` ——
鋪磚精確成立。`ofPerm` 把任何置換 `L` 與方向表 `μ` 打包成位元機，
`ofPerm_localReversible` 給出**參數化**證明（狀態空間隨參數而變，不能
`decide`）。任何依此紀律設計的機器自動可逆；可逆計算的標準微步
（swap、受控寫入、Feistel 輪）全是這個形狀。這是 Bennett 機器級構造的
可逆性引擎：構造只需給出置換，鋪磚檢查一次付清。 -/

/-- 由「局部更新置換 `L` + 方向表 `μ`」打包位元機：`next`/`write` 取 `L` 的
兩個分量、`move` 由更新後的新狀態查 `μ`。 -/
def ofPerm (m : ℕ) (L : ((Fin m → Bool) × Bool) ≃ ((Fin m → Bool) × Bool))
    (μ : (Fin m → Bool) → Dir) : BitTM where
  m := m
  next q a := (L (q, a)).1
  write q a := (L (q, a)).2
  move q a := μ (L (q, a)).1

/-- **置換機自動局部可逆**（參數化鋪磚證明）：槽 `(p, β)` 的唯一前像是
`L.symm (p, β (μ p))`。 -/
theorem ofPerm_localReversible (m : ℕ)
    (L : ((Fin m → Bool) × Bool) ≃ ((Fin m → Bool) × Bool))
    (μ : (Fin m → Bool) → Dir) : (ofPerm m L μ).LocalReversible := by
  intro p β
  refine ⟨L.symm (p, β (μ p)), ⟨?_, ?_⟩, fun qa hqa ↦ ?_⟩
  · show (L (L.symm (p, β (μ p)))).1 = p
    rw [Equiv.apply_symm_apply]
  · show (L (L.symm (p, β (μ p)))).2 = β (μ (L (L.symm (p, β (μ p)))).1)
    rw [Equiv.apply_symm_apply]
  · obtain ⟨hnext, hwrite⟩ := hqa
    have hnext' : (L (qa.1, qa.2)).1 = p := hnext
    have hwrite' : (L (qa.1, qa.2)).2 = β (μ (L (qa.1, qa.2)).1) := hwrite
    have hL : L (qa.1, qa.2) = (p, β (μ p)) := by
      refine Prod.ext hnext' ?_
      rw [hwrite', hnext']
    exact L.eq_symm_apply.mpr hL

/-- 置換機可逆（`step` 雙射）。 -/
theorem ofPerm_reversible (m : ℕ)
    (L : ((Fin m → Bool) × Bool) ≃ ((Fin m → Bool) × Bool))
    (μ : (Fin m → Bool) → Dir) : (ofPerm m L μ).Reversible :=
  (ofPerm_localReversible m L μ).reversible

/-! ### 實例：受控反閘（CNOT）機 -/

/-- 受控反閘機：1 個狀態位元；狀態位為 `true` 時翻轉讀到的位，狀態不變、
頭不動。可逆（自身即逆）—— 可逆計算的經典原子閘。 -/
def cnotTM : BitTM where
  m := 1
  next q _ := q
  write q a := xor (q 0) a
  move _ _ := Dir.stay

theorem cnotTM_localReversible : cnotTM.LocalReversible := by
  unfold LocalReversible ExistsUnique
  decide

theorem cnotTM_reversible : cnotTM.Reversible :=
  cnotTM_localReversible.reversible

end BitTM

/-! ## 里程碑 B（部分）：Bennett 1973 可逆化 — 構造 + 模擬引理

任意（不必可逆的）動力系統 `f : X → X` 升級成**單射**的 history-keeping
映射：每步把當前點押進歷史欄，被 `f` 丟棄的資訊全數保留。

**已證**：單射（`bennett_injective`）、n 步軌道模擬（`bennett_iterate_fst`）。

**誠實缺口（非 paper-blocked）**：此抽象構造**不滿射**
（`bennett_not_surjective`：`(x₀, [])` 無前像，因為 `List.cons` 永不產生 `[]`），
故不能直接餵 `GenShift.Reversible`（需雙射）。**動力學層已在 M3c 封死**：
歷史容器換成雙向無限記錄流（history conveyor），滿射由顯式逆映射成立，
且任意位元機經此升級後被連續流模擬（M6 `bitTM_suspension_simulates`）。
仍開放的是字面機器級構造 —— 歷史寫進帶、再編碼回 `BitTM` ——
工程量大，屬後續工作；本節不佯稱完成。 -/

/-- Bennett history-keeping 構造（抽象層）：`(x, 歷史) ↦ (f x, x :: 歷史)`。 -/
def bennett {X : Type*} (f : X → X) (p : X × List X) : X × List X :=
  (f p.1, p.1 :: p.2)

/-- Bennett 構造單射：歷史欄保留了被 `f` 丟棄的資訊。 -/
theorem bennett_injective {X : Type*} (f : X → X) : Function.Injective (bennett f) := by
  rintro ⟨x, hist⟩ ⟨y, hist'⟩ heq
  have h2 : x :: hist = y :: hist' := congrArg Prod.snd heq
  injection h2 with hxy hh
  subst hxy
  subst hh
  rfl

@[simp] theorem bennett_fst {X : Type*} (f : X → X) (p : X × List X) :
    (bennett f p).1 = f p.1 := rfl

/-- n 步模擬：投影 `fst` 把 Bennett 軌道壓回 `f` 軌道
（半共軛 `fst ∘ bennett f = f ∘ fst` 的迭代版）。 -/
theorem bennett_iterate_fst {X : Type*} (f : X → X) (x : X) (hist : List X) (n : ℕ) :
    ((bennett f)^[n] (x, hist)).1 = f^[n] x := by
  induction n generalizing x hist with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (f x) (x :: hist)

/-- **誠實缺口**：Bennett 抽象構造永不滿射（`(x₀, [])` 無前像），
故其本身不給出 `GenShift.Reversible` 所需的雙射；見模組 docstring。 -/
theorem bennett_not_surjective {X : Type*} (f : X → X) (x₀ : X) :
    ¬ Function.Surjective (bennett f) := by
  intro hsurj
  obtain ⟨⟨y, hist⟩, heq⟩ := hsurj (x₀, [])
  have h2 : y :: hist = ([] : List X) := congrArg Prod.snd heq
  exact List.cons_ne_nil y hist h2

end

end FluidTuring
