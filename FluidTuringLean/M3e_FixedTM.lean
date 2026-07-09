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

/-! ### C-β 地基：靜止帶 + 頭標記的單射編碼

字面 Bennett 機把 FixedTM 的（靜止帶, 頭位置）裝進一條帶：**雙軌交錯**——
偶位 `2k` = FixedTM 帶格 `k`，奇位 `2k+1` = 「頭在 `k`?」標記（唯一在 `h`）。
垃圾軌之後再加（本 brick 只做帶+頭的編碼與單射，垃圾/走位屬 C-β 續與 C-γ）。 -/

/-- 頭標記軌：唯一 `true` 在頭位置 `h`。 -/
def headMark (h : ℤ) : ℤ → Bool := fun k ↦ decide (k = h)

/-- 帶+頭雙軌編碼：偶位載帶、奇位載頭標記。 -/
def fixedEncTape (t : ℤ → Bool) (h : ℤ) : ℤ → Bool :=
  fun i ↦ if i % 2 = 0 then t (i / 2) else headMark h ((i - 1) / 2)

/-- 偶位取回帶格。 -/
theorem fixedEncTape_even (t : ℤ → Bool) (h : ℤ) (k : ℤ) :
    fixedEncTape t h (2 * k) = t k := by
  simp only [fixedEncTape]
  rw [if_pos (by omega : (2 * k) % 2 = 0),
    Int.mul_ediv_cancel_left k (by norm_num : (2 : ℤ) ≠ 0)]

/-- 奇位取回頭標記。 -/
theorem fixedEncTape_odd (t : ℤ → Bool) (h : ℤ) (k : ℤ) :
    fixedEncTape t h (2 * k + 1) = decide (k = h) := by
  simp only [fixedEncTape, headMark]
  rw [if_neg (by omega : ¬(2 * k + 1) % 2 = 0),
    show 2 * k + 1 - 1 = 2 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (2 : ℤ) ≠ 0)]

/-- **編碼單射**：不同的（帶, 頭）給不同的編碼帶 —— 字面構造的地基
（垃圾能靜止堆疊、頭標記唯一可尋，皆賴此）。 -/
theorem fixedEncTape_injective {t t' : ℤ → Bool} {h h' : ℤ}
    (heq : fixedEncTape t h = fixedEncTape t' h') : t = t' ∧ h = h' := by
  have htape : t = t' := by
    funext k
    have := congrFun heq (2 * k)
    rwa [fixedEncTape_even, fixedEncTape_even] at this
  refine ⟨htape, ?_⟩
  have hodd := congrFun heq (2 * h + 1)
  rw [fixedEncTape_odd, fixedEncTape_odd, decide_eq_true (rfl : h = h)] at hodd
  exact of_decide_eq_true hodd.symm

/-! ### 方案 C 焦點 session：整體架構設計基線（2026-07-08，先設計後實作）

**互鎖硬核紀律**：C-β 續(垃圾軌)/C-γ(走位表)/C-δ(宏步)互咬,單塊拆會設計出接不起來
的碎片(rev.1-4 教訓)。故先把整體架構定案,再逐塊實作、每塊 decide/build 驗。

**架構**:
- 被模擬機器 = `FixedTM M`(狀態 q、靜止帶 t、頭 h)。
- 字面機 `bennettFixed : BitTM`(moving-tape、頭固定 0、帶平移=走位)。
- bennettFixed 帶佈局(每 FixedTM 格 k ↔ BitTM 位 3k/3k+1/3k+2 三軌):
  軌 0=t k(M 帶)、軌 1=頭標記(唯一 1 在 h)、軌 2=垃圾(連續新鮮、初始空)。
- bennettFixed 狀態 = M-狀態 q(m 位)+走位相位+緩衝(裝被丟棄的 (q,a))。
- **一個 macrostep(=一 M-step)的微步序列**:
  1. 從 home(BitTM 位 0=格 0 軌 0)出發。
  2. **走到頭標記**(軌 1=1):帶平移到頭標記在位 0 下(net 平移=3h)。
  3. **M-step**:讀軌 0、Feistel(算 next q、寫位、緩衝 (q,a))、頭標記 ±1(M 的 move)。
  4. **走到垃圾 frontier**(軌 2 連續區底):帶平移到 frontier。
  5. **傾倒**:緩衝 (q,a) 寫進新鮮垃圾格、frontier 延伸一格。
  6. **走回 home**(淨零:總平移歸零,`walk_roundtrip_closes` 已驗此性質)。
- 每個走位=標記終止、可逆(ofPerm 免費);macrostep 淨零、可逆;垃圾連續新鮮
  (frontier 確定、無跳過=rev.1-3 障礙不現、`walk_reversible` 已驗核心)。

**實作順序(逐塊 verified)**:
- C-β 續:3 軌乾淨編碼 `fixedEnc3`(帶/頭/垃圾)+單射(擴上方 2 軌技術)。
- C-γ:走位設計成 ofPerm-BitTM(讀標記軌、非標記移動、標記轉相位)→可逆免費
  (ofPerm_reversible);語意=走到正確標記(decide 局部驗)。
- C-δ:macrostep 正確(乾淨組態→∃n 微步→下一乾淨組態、算 M.step、垃圾外顯)
  鏡射 `bennettAut_iterate`;+接 M6 `reversibleTM_suspension_simulates`。

**誠實**:主線不需要(M3c 已閉)=字面機錦上添花;多日、但架構定案後碎片會接得起來。 -/
theorem fixedC_architecture_note : True := trivial

/-- **3 軌乾淨編碼**（C-β 續）：FixedTM 格 `k` ↔ BitTM 位 `3k`(帶)/`3k+1`(頭標記)/
`3k+2`(垃圾)。字面機的完整帶編碼（初始垃圾 `g` 全 false）。 -/
def fixedEnc3 (t : ℤ → Bool) (h : ℤ) (g : ℤ → Bool) : ℤ → Bool :=
  fun i ↦ if i % 3 = 0 then t (i / 3)
    else if i % 3 = 1 then decide ((i - 1) / 3 = h)
    else g ((i - 2) / 3)

theorem fixedEnc3_zero (t : ℤ → Bool) (h : ℤ) (g : ℤ → Bool) (k : ℤ) :
    fixedEnc3 t h g (3 * k) = t k := by
  simp only [fixedEnc3]
  rw [if_pos (by omega : (3 * k) % 3 = 0),
    Int.mul_ediv_cancel_left k (by norm_num : (3 : ℤ) ≠ 0)]

theorem fixedEnc3_one (t : ℤ → Bool) (h : ℤ) (g : ℤ → Bool) (k : ℤ) :
    fixedEnc3 t h g (3 * k + 1) = decide (k = h) := by
  simp only [fixedEnc3]
  rw [if_neg (by omega : ¬(3 * k + 1) % 3 = 0), if_pos (by omega : (3 * k + 1) % 3 = 1),
    show 3 * k + 1 - 1 = 3 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (3 : ℤ) ≠ 0)]

theorem fixedEnc3_two (t : ℤ → Bool) (h : ℤ) (g : ℤ → Bool) (k : ℤ) :
    fixedEnc3 t h g (3 * k + 2) = g k := by
  simp only [fixedEnc3]
  rw [if_neg (by omega : ¬(3 * k + 2) % 3 = 0), if_neg (by omega : ¬(3 * k + 2) % 3 = 1),
    show 3 * k + 2 - 2 = 3 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (3 : ℤ) ≠ 0)]

/-- **3 軌編碼單射**：三軌各自取回 → (帶,頭,垃圾) 由編碼帶唯一決定。 -/
theorem fixedEnc3_injective {t t' g g' : ℤ → Bool} {h h' : ℤ}
    (heq : fixedEnc3 t h g = fixedEnc3 t' h' g') : t = t' ∧ h = h' ∧ g = g' := by
  refine ⟨funext fun k ↦ ?_, ?_, funext fun k ↦ ?_⟩
  · have := congrFun heq (3 * k); rwa [fixedEnc3_zero, fixedEnc3_zero] at this
  · have hh := congrFun heq (3 * h + 1)
    rw [fixedEnc3_one, fixedEnc3_one, decide_eq_true (rfl : h = h)] at hh
    exact of_decide_eq_true hh.symm
  · have := congrFun heq (3 * k + 2); rwa [fixedEnc3_two, fixedEnc3_two] at this

/-! ### C-δ sentinel 修法（4 軌，2026-07-09，對抗艦隊 wf_481a605d-b94 裁決後）

**對抗裁決**：6 視角艦隊（12 agents）判 3 軌 `fixedEnc3` 的「frontier=連續垃圾區
遠端邊緣」設計撞**唯一確認真牆（frontier-find）**：`ofPerm` 免費可逆走位**無法可逆
穿越一段相同標記的 run**（CNOT bounce 在第一個 `1` 就反向；穿越需 self-loop
`(scan,1)→(scan,1)`，鴿籠吃掉唯一前像槽 → 非有限置換 → ofPerm 不適用）。5/6 視角
判無結構死牆（真開放多日）。**兩獨立複驗者收斂修法=frontier 改用專屬軌的一位元
sentinel**：格 `k` ↔ 位 `4k`(帶)/`4k+1`(頭標記)/`4k+2`(垃圾內容)/`4k+3`(frontier
sentinel)。**頭標記軌與 sentinel 軌皆唯一-1 標記軌 → 兩段走位都復用已證的 `walkTM`**
（bounce 到唯一標記、不穿越垃圾內容 run）→ frontier-find 真牆在原語層閃過。
仍待（多日、有界非牆）：記錄寬 m+1 打包+有界複製相位、deposit in-degree、宏步歸納。 -/

/-- **4 軌乾淨編碼**（frontier sentinel 修法）。 -/
def fixedEnc4 (t : ℤ → Bool) (h : ℤ) (g : ℤ → Bool) (f : ℤ) : ℤ → Bool :=
  fun i ↦ if i % 4 = 0 then t (i / 4)
    else if i % 4 = 1 then decide ((i - 1) / 4 = h)
    else if i % 4 = 2 then g ((i - 2) / 4)
    else decide ((i - 3) / 4 = f)

theorem fixedEnc4_zero (t g : ℤ → Bool) (h f k : ℤ) : fixedEnc4 t h g f (4 * k) = t k := by
  simp only [fixedEnc4]
  rw [if_pos (by omega : (4 * k) % 4 = 0),
    Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)]

theorem fixedEnc4_one (t g : ℤ → Bool) (h f k : ℤ) :
    fixedEnc4 t h g f (4 * k + 1) = decide (k = h) := by
  simp only [fixedEnc4]
  rw [if_neg (by omega : ¬(4 * k + 1) % 4 = 0), if_pos (by omega : (4 * k + 1) % 4 = 1),
    show 4 * k + 1 - 1 = 4 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)]

theorem fixedEnc4_two (t g : ℤ → Bool) (h f k : ℤ) : fixedEnc4 t h g f (4 * k + 2) = g k := by
  simp only [fixedEnc4]
  rw [if_neg (by omega : ¬(4 * k + 2) % 4 = 0), if_neg (by omega : ¬(4 * k + 2) % 4 = 1),
    if_pos (by omega : (4 * k + 2) % 4 = 2),
    show 4 * k + 2 - 2 = 4 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)]

theorem fixedEnc4_three (t g : ℤ → Bool) (h f k : ℤ) :
    fixedEnc4 t h g f (4 * k + 3) = decide (k = f) := by
  simp only [fixedEnc4]
  rw [if_neg (by omega : ¬(4 * k + 3) % 4 = 0), if_neg (by omega : ¬(4 * k + 3) % 4 = 1),
    if_neg (by omega : ¬(4 * k + 3) % 4 = 2),
    show 4 * k + 3 - 3 = 4 * k from by ring,
    Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)]

/-- **4 軌編碼單射**：四軌各自取回 → (帶,頭,垃圾,frontier) 由編碼帶唯一決定。 -/
theorem fixedEnc4_injective {t t' g g' : ℤ → Bool} {h h' f f' : ℤ}
    (heq : fixedEnc4 t h g f = fixedEnc4 t' h' g' f') :
    t = t' ∧ h = h' ∧ g = g' ∧ f = f' := by
  refine ⟨funext fun k ↦ ?_, ?_, funext fun k ↦ ?_, ?_⟩
  · have := congrFun heq (4 * k); rwa [fixedEnc4_zero, fixedEnc4_zero] at this
  · have hh := congrFun heq (4 * h + 1)
    rw [fixedEnc4_one, fixedEnc4_one, decide_eq_true (rfl : h = h)] at hh
    exact of_decide_eq_true hh.symm
  · have := congrFun heq (4 * k + 2); rwa [fixedEnc4_two, fixedEnc4_two] at this
  · have hf := congrFun heq (4 * f + 3)
    rw [fixedEnc4_three, fixedEnc4_three, decide_eq_true (rfl : f = f)] at hf
    exact of_decide_eq_true hf.symm

/-- 頭標記軌 = `headMark h`（唯一 1）。 -/
theorem fixedEnc4_head_track (t g : ℤ → Bool) (h f k : ℤ) :
    fixedEnc4 t h g f (4 * k + 1) = headMark h k := by
  rw [fixedEnc4_one]; rfl

/-- **frontier sentinel 軌 = `headMark f`（唯一 1）** → 走到 frontier 的走位與走到頭
標記的走位**同結構**（皆 bounce 到唯一-1 標記），復用已證的 `walkTM`、不穿越垃圾內容
run。此即對抗艦隊 frontier-find 真牆的原語層閃過。 -/
theorem fixedEnc4_frontier_track (t g : ℤ → Bool) (h f k : ℤ) :
    fixedEnc4 t h g f (4 * k + 3) = headMark f k := by
  rw [fixedEnc4_three]; rfl

end FixedTM

/-! ### C-γ：可逆雙標記彈跳走位（ofPerm-BitTM，可逆免費）

方案 C 走位可逆性的核心。走位在 ℤ 上距離**資料相依**（無界，頭 `h` 可任意遠），
但可逆性不是無界軌跡問題、而是**有限的局部置換檢查**。設計成 `ofPerm`-BitTM，
`ofPerm_reversible`（M3b 已證）就**一次付清**整條無界走位的可逆性。

**雙標記彈跳**：相位 = 1 位（`false`=向右 goR / `true`=向左 goL）。讀標記軌位 `a`：
空白格（`a=false`）續走同向、標記格（`a=true`）反向。局部更新
`walkStep (p,a) = (fun i ↦ xor (p i) a, a)`——受 `a` 控制翻轉相位、位不變
（CNOT 式**對合**），故是 `(相位 × 位)` 的置換 ⟹ `walkTM` 可逆。方向 `μ` 查新相位。

這是 C-γ 的可獨立驗證地基：**無界走位的可逆性=免費**（結構=有限置換，不需歸納
無界軌跡）。走位的語意正確（走到正確標記、垃圾 frontier）= C-δ 宏步層的事。 -/

/-- 走位局部更新：讀位 `a` 控制翻轉相位（位不變）。CNOT 式對合。 -/
def walkStep (pa : (Fin 1 → Bool) × Bool) : (Fin 1 → Bool) × Bool :=
  (fun i ↦ xor (pa.1 i) pa.2, pa.2)

theorem walkStep_involutive : Function.Involutive walkStep := by
  rintro ⟨p, a⟩
  simp only [walkStep]
  refine Prod.ext ?_ rfl
  funext i
  cases a <;> simp

/-- 走位局部置換（由對合建）。 -/
def walkPerm : ((Fin 1 → Bool) × Bool) ≃ ((Fin 1 → Bool) × Bool) :=
  walkStep_involutive.toPerm

/-- 走位方向表：goL(`true`)→左、goR(`false`)→右。 -/
def walkMu : (Fin 1 → Bool) → Dir := fun p ↦ if p 0 then Dir.left else Dir.right

/-- **彈跳走位 BitTM**（方案 C 走位引擎）。 -/
def walkTM : BitTM := BitTM.ofPerm 1 walkPerm walkMu

/-- **走位可逆（免費）**：`ofPerm` 任意置換即可逆 ⟹ 無界走位的可逆性一次付清，
不需對無界軌跡歸納。此即 C-γ 消解「兩流 crux 可逆性」的關鍵。 -/
theorem walkTM_reversible : walkTM.Reversible :=
  BitTM.ofPerm_reversible 1 walkPerm walkMu

/-- goR 相位（向右）。 -/
def goR : Fin 1 → Bool := fun _ ↦ false
/-- goL 相位（向左）。 -/
def goL : Fin 1 → Bool := fun _ ↦ true

/-- **語意①**：空白格（`a=false`）續走同向——goR 保持 goR、向右移。 -/
theorem walkTM_blank_goR : walkTM.next goR false = goR ∧ walkTM.move goR false = Dir.right := by
  constructor <;> decide

/-- **語意②**：標記格（`a=true`）反向——goR 翻成 goL、改向左移。 -/
theorem walkTM_marker_goR : walkTM.next goR true = goL ∧ walkTM.move goR true = Dir.left := by
  constructor <;> decide

/-- **語意③**：對稱地，goL 在空白續向左、在標記翻回 goR 向右。 -/
theorem walkTM_goL_cases :
    walkTM.next goL false = goL ∧ walkTM.move goL false = Dir.left ∧
    walkTM.next goL true = goR ∧ walkTM.move goL true = Dir.right := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end FluidTuring
