import FluidTuringLean.M3b_ReversibleTM
import FluidTuringLean.M3d_BennettTM

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

/-! ### C-δ：軌選擇彈跳走位控制表（4 軌上，decide 裁 frontier-find 真牆）

對抗艦隊（wf_481a605d-b94）唯一確認真牆 frontier-find 的**前提是 memoryless 走位**：
穿越一段相同標記的 run 需 self-loop `(scan,1)→(scan,1)`，鴿籠吃掉唯一前像槽 → 非置換。

**化解**：走位帶一個 **offset-mod-4 計數器**（= 帶位址 mod 4 = 4 軌 `fixedEnc4` 的軌別）。
於是「穿越非目標軌的 1」變成 `(dir, off, a) → (dir, off±1, a)` 的 **offset 遞增雙射更新**
（**非 self-loop → 鴿籠消失**）。目標=唯一 sentinel 標記（`fixedEnc4_frontier_track`），
用 `(offset = 目標軌 t ∧ a = true)` 偵測，**不需 run-length**。此設計正是艦隊 deposit/
completeness 複驗者收斂的 sentinel 修法之走位側。**是不是真置換由 `decide` 客觀裁**
（記憶教訓：控制表 + decide 反例迭代 = 正確工作迴路，紙上推不完）。

控制狀態 `Bool × Fin 4 × Bool` = 方向(false=R/true=L) × offset(軌別) × 讀位。 -/

/-- 軌選擇走位前向：偵測唯一標記（`off = t ∧ a`）則 bounce（翻向）、否則 cross
（續走、offset 隨新方向 ±1、位不變）。offset 移動綁新方向使穿越保持雙射。 -/
def trackWalkFwd (t : Fin 4) (s : Bool × Fin 4 × Bool) : Bool × Fin 4 × Bool :=
  let dir := s.1; let off := s.2.1; let a := s.2.2
  let bounce := a && decide (off = t)
  let ndir := xor dir bounce
  let noff := bif ndir then off - 1 else off + 1
  (ndir, noff, a)

/-- 軌選擇走位逆向（手寫逆、供 `decide` 裁互逆）。 -/
def trackWalkBwd (t : Fin 4) (s : Bool × Fin 4 × Bool) : Bool × Fin 4 × Bool :=
  let ndir := s.1; let noff := s.2.1; let a := s.2.2
  let off := bif ndir then noff + 1 else noff - 1
  let bounce := a && decide (off = t)
  let dir := xor ndir bounce
  (dir, off, a)

/-- **軌選擇彈跳走位是置換（decide 裁，全 4 目標軌 × 16 控制 = 64 例）**：`trackWalkFwd`
與 `trackWalkBwd` 互逆 ⟹ in-degree-1。**此即機器級證明：offset 計數器把穿越 run
變雙射、化解對抗艦隊 frontier-find 真牆的鴿籠**（該牆對 memoryless 走位成立，對此
offset-augmented 走位不成立）。 -/
theorem trackWalk_reversible :
    ∀ (t : Fin 4) (s : Bool × Fin 4 × Bool),
      trackWalkBwd t (trackWalkFwd t s) = s ∧ trackWalkFwd t (trackWalkBwd t s) = s := by
  decide

/-- 軌選擇走位打包成置換。 -/
def trackWalkEquiv (t : Fin 4) : (Bool × Fin 4 × Bool) ≃ (Bool × Fin 4 × Bool) :=
  ⟨trackWalkFwd t, trackWalkBwd t,
    fun s ↦ (trackWalk_reversible t s).1, fun s ↦ (trackWalk_reversible t s).2⟩

/-- **語意（wall-dodge 顯式化）**：非目標軌（`off ≠ t`）上，**無論讀位 `a`**（含
`a=true`，即穿越垃圾/資料軌的 `1`）都 cross——保持方向、offset 隨方向 ±1、位不變。
這正是對抗艦隊 frontier-find 真牆的反面：穿越一段相同標記的 run 是 offset 遞增的
**directional cross（非 self-loop）**。 -/
theorem trackWalk_cross (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool) (h : off ≠ t) :
    trackWalkFwd t (dir, off, a) = (dir, bif dir then off - 1 else off + 1, a) := by
  simp only [trackWalkFwd, decide_eq_false h, Bool.and_false, Bool.xor_false]

/-- **語意**：目標軌唯一標記（`off = t ∧ a = true`）→ bounce（翻方向）。 -/
theorem trackWalk_bounce (t : Fin 4) (dir : Bool) :
    trackWalkFwd t (dir, t, true) = (!dir, bif !dir then t - 1 else t + 1, true) := by
  cases dir <;> simp [trackWalkFwd]

/-- **統一非標記 cross**（可達性迭代真正需要的）：只要不是「目標軌的唯一標記」
（`¬(off = t ∧ a = true)`）就 cross——含目標軌上的空白格（`off = t, a = false`）。
因 offset 週期會經過目標軌，但只有帶著標記位的那一格才 bounce。 -/
theorem trackWalk_step_nonmarker (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool)
    (h : ¬(off = t ∧ a = true)) :
    trackWalkFwd t (dir, off, a) = (dir, bif dir then off - 1 else off + 1, a) := by
  have hb : (a && decide (off = t)) = false := by
    cases a with
    | false => rfl
    | true => exact (Bool.and_eq_false_iff).mpr <| Or.inr <|
        decide_eq_false (fun hoff ↦ h ⟨hoff, rfl⟩)
  simp only [trackWalkFwd, hb, Bool.xor_false]

/-! #### 軌選擇走位 → 真可逆 BitTM（ofPerm feed）

控制 `Bool × Fin 4`（方向×軌別）編碼成 3 位元 `Fin 3 → Bool`，共軛 `trackWalkEquiv`
餵 `ofPerm` → 真 BitTM，`ofPerm_reversible` 免費給可逆性。方向表 μ 讀方向位。 -/

/-- 控制打包：(方向, 軌別) → 3 位元（位 0=方向、位 1/2=軌別二進位）。 -/
def packCtrl (s : Bool × Fin 4) : Fin 3 → Bool :=
  ![s.1, decide (s.2 = 1 ∨ s.2 = 3), decide (s.2 = 2 ∨ s.2 = 3)]

/-- 控制解包（手寫逆）。 -/
def unpackCtrl (f : Fin 3 → Bool) : Bool × Fin 4 :=
  (f 0, (bif f 1 then 1 else 0) + (bif f 2 then 2 else 0))

theorem pack_unpack :
    (∀ s, unpackCtrl (packCtrl s) = s) ∧ (∀ f, packCtrl (unpackCtrl f) = f) := by
  constructor <;> decide

/-- 控制 `Bool × Fin 4` ≃ 3 位元。 -/
def ctrlBits : (Bool × Fin 4) ≃ (Fin 3 → Bool) :=
  ⟨packCtrl, unpackCtrl, pack_unpack.1, pack_unpack.2⟩

/-- 軌選擇走位的 ofPerm 控制置換（3 位元狀態）。 -/
def trackWalkL (t : Fin 4) : ((Fin 3 → Bool) × Bool) ≃ ((Fin 3 → Bool) × Bool) :=
  (Equiv.prodCongr ctrlBits.symm (Equiv.refl Bool)).trans
    ((Equiv.prodAssoc Bool (Fin 4) Bool).trans
      ((trackWalkEquiv t).trans
        ((Equiv.prodAssoc Bool (Fin 4) Bool).symm.trans
          (Equiv.prodCongr ctrlBits (Equiv.refl Bool)))))

/-- **橋接（可達性地基）**：`trackWalkL`（機器控制置換、3 位元）作用在 `ctrlBits`-打包的
控制 = 控制層 `trackWalkFwd` 的結果再打包。連接機器層與已 decide 驗的控制層語意
（`trackWalk_cross`/`_bounce`），所有走位可達性推理的基礎。 -/
theorem trackWalkL_pack (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool) :
    trackWalkL t (ctrlBits (dir, off), a) =
      (ctrlBits ((trackWalkFwd t (dir, off, a)).1, (trackWalkFwd t (dir, off, a)).2.1),
        (trackWalkFwd t (dir, off, a)).2.2) := by
  simp only [trackWalkL, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply, Prod.map_apply, id_eq,
    Equiv.symm_apply_apply, trackWalkEquiv, Equiv.coe_fn_mk]

/-- 方向表：方向位（位 0）true=左、false=右。 -/
def trackWalkMu : (Fin 3 → Bool) → Dir := fun bits ↦ bif bits 0 then Dir.left else Dir.right

/-- **軌選擇彈跳走位 = 真可逆 BitTM**（4 軌 `fixedEnc4` 上兩段 macrostep 走位的引擎、
`t=1` 走頭標記、`t=3` 走 frontier sentinel）。 -/
def trackWalkTM (t : Fin 4) : BitTM := BitTM.ofPerm 3 (trackWalkL t) trackWalkMu

/-- **可逆（免費）**：`ofPerm_reversible` 給任意控制置換的可逆性 ⟹ 軌選擇走位
（含穿越 run，已 `trackWalk_reversible` decide 裁為置換）的無界軌跡可逆性一次付清。 -/
theorem trackWalkTM_reversible (t : Fin 4) : (trackWalkTM t).Reversible :=
  BitTM.ofPerm_reversible 3 (trackWalkL t) trackWalkMu

/-- **機器層 cross**（可達性步進）：讀非目標軌（`off ≠ t`）、任意讀位 `a`，機器狀態
更新 = 保持方向、offset 隨方向 ±1（打包）。直接由橋接 + `trackWalk_cross`。 -/
theorem trackWalkTM_next_cross (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool) (h : off ≠ t) :
    (trackWalkTM t).next (ctrlBits (dir, off)) a
      = ctrlBits (dir, bif dir then off - 1 else off + 1) := by
  change (trackWalkL t (ctrlBits (dir, off), a)).1 = _
  rw [trackWalkL_pack, trackWalk_cross t dir off a h]

/-- **機器層 bounce**（可達性步進）：讀目標軌唯一標記（`off = t`、`a = true`）→ 翻方向。 -/
theorem trackWalkTM_next_bounce (t : Fin 4) (dir : Bool) :
    (trackWalkTM t).next (ctrlBits (dir, t)) true
      = ctrlBits (!dir, bif !dir then t - 1 else t + 1) := by
  change (trackWalkL t (ctrlBits (dir, t), true)).1 = _
  rw [trackWalkL_pack, trackWalk_bounce t dir]

/-- 打包控制的方向位（位 0）= 方向。 -/
theorem ctrlBits_bit0 (dir : Bool) (off : Fin 4) : (ctrlBits (dir, off)) 0 = dir := rfl

/-- 控制層：走位**不改讀位**（`trackWalkFwd` 的第三分量 = 輸入讀位）。 -/
theorem trackWalkFwd_bit (t : Fin 4) (s : Bool × Fin 4 × Bool) :
    (trackWalkFwd t s).2.2 = s.2.2 := rfl

/-- **機器層：走位不改帶位**（`write = 讀位`）——走位純導航、不寫資料。 -/
theorem trackWalkTM_write (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool) :
    (trackWalkTM t).write (ctrlBits (dir, off)) a = a := by
  change (trackWalkL t (ctrlBits (dir, off), a)).2 = _
  rw [trackWalkL_pack, trackWalkFwd_bit]

/-- **機器層 move（cross）**：讀非目標軌 → 平移方向 = 相位方向（`dir` true=左 / false=右）。 -/
theorem trackWalkTM_move_cross (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool) (h : off ≠ t) :
    (trackWalkTM t).move (ctrlBits (dir, off)) a = bif dir then Dir.left else Dir.right := by
  change trackWalkMu (trackWalkL t (ctrlBits (dir, off), a)).1 = _
  rw [trackWalkL_pack, trackWalk_cross t dir off a h]
  simp only [trackWalkMu, ctrlBits_bit0]

/-- **帶層 cross 步進（可達性迭代 workhorse）**：機器在非目標軌（`off ≠ t`）一步 =
控制保持方向、offset±1（打包），帶依相位方向平移一格（寫回讀位=純導航）。組
`step_eval` + 三元件（next/move/write）。可達性歸納（∃N 步到唯一標記）即迭代此步。 -/
theorem trackWalkTM_step_cross (t : Fin 4) (dir : Bool) (off : Fin 4) (tape : ℤ → Bool)
    (h : off ≠ t) :
    (trackWalkTM t).step (ctrlBits (dir, off), tape)
      = (ctrlBits (dir, bif dir then off - 1 else off + 1),
         fun n ↦ if n + (bif dir then Dir.left else Dir.right).toInt = 0 then tape 0
                 else tape (n + (bif dir then Dir.left else Dir.right).toInt)) := by
  rw [BitTM.step_eval, trackWalkTM_next_cross t dir off (tape 0) h,
    trackWalkTM_move_cross t dir off (tape 0) h, trackWalkTM_write t dir off (tape 0)]
  rfl

/-- 機器層 next（非標記）：讀非唯一標記格 → 保持方向、offset±1（打包）。 -/
theorem trackWalkTM_next_nonmarker (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool)
    (h : ¬(off = t ∧ a = true)) :
    (trackWalkTM t).next (ctrlBits (dir, off)) a
      = ctrlBits (dir, bif dir then off - 1 else off + 1) := by
  change (trackWalkL t (ctrlBits (dir, off), a)).1 = _
  rw [trackWalkL_pack, trackWalk_step_nonmarker t dir off a h]

/-- 機器層 move（非標記）：讀非唯一標記格 → 平移方向 = 相位方向。 -/
theorem trackWalkTM_move_nonmarker (t : Fin 4) (dir : Bool) (off : Fin 4) (a : Bool)
    (h : ¬(off = t ∧ a = true)) :
    (trackWalkTM t).move (ctrlBits (dir, off)) a = bif dir then Dir.left else Dir.right := by
  change trackWalkMu (trackWalkL t (ctrlBits (dir, off), a)).1 = _
  rw [trackWalkL_pack, trackWalk_step_nonmarker t dir off a h]
  simp only [trackWalkMu, ctrlBits_bit0]

/-- **帶層非標記步進（可達性迭代真正 workhorse）**：機器讀任一非唯一標記格一步 =
控制保持方向、offset±1（打包），帶依相位方向平移一格。統一 cross（含目標軌空白格），
故可達性歸納能無條件迭代到唯一標記為止。 -/
theorem trackWalkTM_step_nonmarker (t : Fin 4) (dir : Bool) (off : Fin 4) (tape : ℤ → Bool)
    (h : ¬(off = t ∧ tape 0 = true)) :
    (trackWalkTM t).step (ctrlBits (dir, off), tape)
      = (ctrlBits (dir, bif dir then off - 1 else off + 1),
         fun n ↦ if n + (bif dir then Dir.left else Dir.right).toInt = 0 then tape 0
                 else tape (n + (bif dir then Dir.left else Dir.right).toInt)) := by
  rw [BitTM.step_eval, trackWalkTM_next_nonmarker t dir off (tape 0) h,
    trackWalkTM_move_nonmarker t dir off (tape 0) h, trackWalkTM_write t dir off (tape 0)]
  rfl

/-- offset 前進 `N` 格（每步 `+1`，以 `Function.iterate` 避開 `Fin 4` 的 `NatCast`）。 -/
def offAdvance (N : ℕ) (off : Fin 4) : Fin 4 := (· + 1)^[N] off

theorem offAdvance_zero (off : Fin 4) : offAdvance 0 off = off := rfl

theorem offAdvance_succ (N : ℕ) (off : Fin 4) :
    offAdvance (N + 1) off = offAdvance N off + 1 :=
  Function.iterate_succ_apply' _ _ _

/-- **可達性歸納核心（右移 bulk-cross）**：向右（`dir = false`）走 `N` 步，只要沿途
每格都非唯一標記（用**原帶**表達：第 `i` 步讀 `tape i`、offset = `offAdvance i off`），
則 `N` 步後 offset 前進 `N`、帶前向純移位 `N`（`tape' n = tape (n+N)`，`n ≥ 0`；負位
尾跡不影響走位、以 `∃tape'` 略去）。可達性 = 取 `N` = 到標記距離、下一步即 bounce。 -/
theorem trackWalkTM_iter_right (t : Fin 4) (off : Fin 4) (tape : ℤ → Bool) (N : ℕ)
    (h : ∀ i : ℕ, i < N → ¬(offAdvance i off = t ∧ tape (i : ℤ) = true)) :
    ∃ tape', ((trackWalkTM t).step)^[N] (ctrlBits (false, off), tape)
               = (ctrlBits (false, offAdvance N off), tape')
             ∧ ∀ n : ℤ, 0 ≤ n → tape' n = tape (n + N) := by
  induction N with
  | zero => exact ⟨tape, rfl, fun n _ ↦ by simp⟩
  | succ k ih =>
    obtain ⟨tk, hk, hkf⟩ := ih (fun i hi ↦ h i (Nat.lt_succ_of_lt hi))
    have hread : tk 0 = tape (k : ℤ) := by simpa using hkf 0 (le_refl 0)
    have hnm : ¬(offAdvance k off = t ∧ tk 0 = true) := by
      rw [hread]; exact h k (Nat.lt_succ_self k)
    have hstep : ((trackWalkTM t).step)^[k + 1] (ctrlBits (false, off), tape)
        = (ctrlBits (false, offAdvance (k + 1) off),
           fun n ↦ if n + (bif false then Dir.left else Dir.right).toInt = 0 then tk 0
                   else tk (n + (bif false then Dir.left else Dir.right).toInt)) := by
      rw [Function.iterate_succ_apply', hk, offAdvance_succ]
      exact trackWalkTM_step_nonmarker t false (offAdvance k off) tk hnm
    refine ⟨_, hstep, fun n hn ↦ ?_⟩
    have hd : (bif false then Dir.left else Dir.right).toInt = 1 := rfl
    simp only [hd]
    rw [if_neg (show ¬(n + 1 = 0) by omega), hkf (n + 1) (by omega)]
    congr 1
    push_cast; ring

/-- 機器層 move（bounce）：讀目標軌唯一標記 → 平移方向 = 反相位方向（翻向）。 -/
theorem trackWalkTM_move_bounce (t : Fin 4) (dir : Bool) :
    (trackWalkTM t).move (ctrlBits (dir, t)) true = bif !dir then Dir.left else Dir.right := by
  change trackWalkMu (trackWalkL t (ctrlBits (dir, t), true)).1 = _
  rw [trackWalkL_pack, trackWalk_bounce t dir]
  simp only [trackWalkMu, ctrlBits_bit0]

/-- **帶層 bounce 步進**：機器在目標軌唯一標記（`tape 0 = true`）一步 = 控制翻方向、
offset 反向 ±1，帶依反方向平移一格。可達性收尾的最後一步。 -/
theorem trackWalkTM_step_bounce (t : Fin 4) (dir : Bool) (tape : ℤ → Bool) (ht : tape 0 = true) :
    (trackWalkTM t).step (ctrlBits (dir, t), tape)
      = (ctrlBits (!dir, bif !dir then t - 1 else t + 1),
         fun n ↦ if n + (bif !dir then Dir.left else Dir.right).toInt = 0 then true
                 else tape (n + (bif !dir then Dir.left else Dir.right).toInt)) := by
  rw [BitTM.step_eval, ht, trackWalkTM_next_bounce t dir, trackWalkTM_move_bounce t dir,
    trackWalkTM_write t dir t true]
  rfl

/-- **★走位可達性（收尾）★**：向右走位，沿途每格非唯一標記、offset 於距離 `p` 對齊到
目標軌（`offAdvance p off = t`）、該處是標記（`tape p = true`），則恰 `p + 1` 步後機器
**已抵達標記並彈跳**（方向由 `false`(右) 翻成 `true`(左)）。= iter_right（`p` 步穿越）
接 step_bounce（第 `p+1` 步彈跳）。這是「走到唯一標記於資料相依距離」的完整證明。 -/
theorem trackWalkTM_reaches_marker (t : Fin 4) (off : Fin 4) (tape : ℤ → Bool) (p : ℕ)
    (hpath : ∀ i : ℕ, i < p → ¬(offAdvance i off = t ∧ tape (i : ℤ) = true))
    (halign : offAdvance p off = t) (hmark : tape (p : ℤ) = true) :
    ∃ (off' : Fin 4) (tape' : ℤ → Bool),
      ((trackWalkTM t).step)^[p + 1] (ctrlBits (false, off), tape)
        = (ctrlBits (true, off'), tape') := by
  obtain ⟨tp, hp, hpf⟩ := trackWalkTM_iter_right t off tape p hpath
  have htp0 : tp 0 = true := by rw [hpf 0 (le_refl 0)]; simpa using hmark
  have hfull : ((trackWalkTM t).step)^[p + 1] (ctrlBits (false, off), tape)
      = (ctrlBits (!false, bif !false then t - 1 else t + 1),
         fun n ↦ if n + (bif !false then Dir.left else Dir.right).toInt = 0 then true
                 else tp (n + (bif !false then Dir.left else Dir.right).toInt)) := by
    rw [Function.iterate_succ_apply', hp, halign]
    exact trackWalkTM_step_bounce t false tp htp0
  exact ⟨_, _, hfull⟩

/-! ### C-δ：deposit 迴圈本體（ring-controlled，2026-07-09，對抗設計艦隊 wf_a19b206c 修法）

設計艦隊揪出原「spectator ringAtZero + decide-on-Profile」deposit 機制**錯**（ring 計數器在
data 層、Profile 1-bit 脫鉤→非單射，= M3d:570-573 已 descope 的 C4b 複合單射邊界）。**修法（驗
2）= ring-controlled**：deposit 迴圈本體 = 一次 tick 復用 `garbagePiece` 的原語（`swapHead`
buffer↔帶位交換 + `rotBuf` buffer 旋轉）**加 `finRotate` 推進 ring**，全是已證 `Equiv` 的複合
⟹ 本體自動是 `Equiv` ⟹ **可逆免費**（無 decide-on-Profile、無脫鉤覆寫）。ring(m+1) 驅動終止
（滿一圈回 home）當上層 `prodShear` gate（下階）。狀態 = `((ring × buffer) × 帶位)`。 -/

/-- **deposit 迴圈本體**（ring-controlled per-tick `Equiv`）：`finRotate` 推進 ring；
`swapHead`+`rotBuf`（= `garbagePiece` 的原語）把 buffer 首位搬上帶位、buffer 旋轉一格。
複合已證 `Equiv` ⟹ 自身 `Equiv` ⟹ 可逆免費（艦隊修法的核心：ring 真推進、非脫鉤 1-bit）。 -/
def depositTick (m : ℕ) :
    ((Fin (m + 1) × (Fin (m + 1) → Bool)) × Bool) ≃ ((Fin (m + 1) × (Fin (m + 1) → Bool)) × Bool) :=
  (Equiv.prodAssoc (Fin (m + 1)) (Fin (m + 1) → Bool) Bool).trans
    ((Equiv.prodCongr (finRotate (m + 1))
        ((swapHead m).trans (Equiv.prodCongr (rotBuf m) (Equiv.refl Bool)))).trans
      (Equiv.prodAssoc (Fin (m + 1)) (Fin (m + 1) → Bool) Bool).symm)

/-- **語意**：ring 分量每 tick 由 `finRotate` 推進（真推進、非脫鉤旗標）——這是艦隊修法
相對「spectator ringAtZero」的關鍵差異。 -/
theorem depositTick_ring (m : ℕ) (r : Fin (m + 1)) (buf : Fin (m + 1) → Bool) (a : Bool) :
    (depositTick m ((r, buf), a)).1.1 = finRotate (m + 1) r := rfl

/-- **語意**：帶位分量取回 buffer 首位（`garbagePiece` 的搬運：`swapHead` 令帶位 ← buffer[0]）
——一 tick 搬一位記錄上帶。 -/
theorem depositTick_tape (m : ℕ) (r : Fin (m + 1)) (buf : Fin (m + 1) → Bool) (a : Bool) :
    (depositTick m ((r, buf), a)).2 = buf 0 := rfl

/-- deposit 迴圈本體可逆（免費，`Equiv` 自帶逆 `symm`）——無界 deposit 深度的可逆性一次付清。 -/
theorem depositTick_symm_apply (m : ℕ) (x) :
    (depositTick m).symm (depositTick m x) = x := (depositTick m).symm_apply_apply x

end FluidTuring
