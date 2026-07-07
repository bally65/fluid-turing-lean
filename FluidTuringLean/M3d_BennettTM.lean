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

## Milestone C 排程設計定案（rev.2，2026-07-04；取代 rev.1 與原待決 1、2、5、6、7）

**rev.1 → rev.2 修訂原因（兩個設計洞）**：(a) 回程「走右遇到的第一個
causeway 位」在 `h < 0` 時是 home、`h ≥ 0` 時是原點，兩者僅靠 causeway/
垃圾軌不可區分；(b) 用垃圾資料位當原點哨兵會被垃圾內容假冒（causeway
回縮後區塊可收垃圾、再延伸時哨兵可偽）。修法：**區塊加寬到 5 格**，
第 5 軌 = 原點哨兵（只有絕對區塊 0 為 1，任何協定只讀不寫 —— 不變量
平凡）；**傾倒跳過 causeway 區塊**（先讀 off3 再讀 off2），使區塊 0
永不收垃圾、回程首個 causeway 位的哨兵讀取無假冒。

**幾何**：帶佈局 = 5 格區塊：模擬帶格 `k` ↦ 帶位 `5k..5k+4` =
（off0 工作、off1 垃圾資料、off2 垃圾標記、off3 home/causeway、
off4 原點哨兵）。垃圾**散置**（不再要求連續堆疊）：傾倒 = 從 home 向左
第一個「非 causeway 且未標記」的區塊起逐塊向左；causeway =
`[min(0,h), max(0,h)]` 的 off3 全 1（`h` = home 絕對區塊號）；`h = 0` 時
= 單點原點標記 = milestone B 佈局。所有掃描以標記/offset 邊界終止。

**暫存器（rev.2）**：M-狀態 `m` 位 × 緩衝 `m+1` 位 × 相位 5 位（32 槽、
FSM 用 17）× offset 3 位（mod-5 塊內定位，與走位方向鎖步，遞增 = 置換）。

**相位表（17 相位；「dir」= 進入該相位時的移動方向；guard 只在指定
offset 的格子讀帶位，其餘格照走）**：

| 相位 | dir | 位置/guard | 動作與轉移 |
|---|---|---|---|
| P0 ready | S | home off0 | Feistel（`(q,a)`進緩衝）；d=L→P1'、d=R→P2a、d=S→P5a |
| P1' probeCL | L | 至 off3（左鄰 causeway，2 步） | 讀 a：0→翻位(延伸@h-1)→WL0dep；1→P4'（回縮） |
| P4' retrL | R | 至 off3（own causeway，5 步） | 翻位 1→0 →P4'a |
| P4'a | L | 至 off3（左鄰，5 步） | 過站→WL0dep |
| P2a hopR1 | R | 至 off3（own，3 步） | 過站→P2b |
| P2b probeCR | R | 至 off3（右鄰 +8） | 讀 a：0→翻位(延伸@h+1)→P3'；1→P4（回縮） |
| P4 retrR | L | 至 off3（own，5 步） | 翻位 1→0 →P3' |
| P3' | R | 至 off0（新 home） | 過站→P5a |
| WL0dep | L | 至 off0 | 過站→P5a（傾倒入口） |
| P5a descend | L | 至 off3 | 讀 a：1→留 P5a（跳過 causeway 塊）；0→P5b |
| P5b | L | 至 off2 | 讀 a：1→P5a（跳過垃圾塊）；0→翻位 0→1→P6 |
| P6 deposit | L | 至 off1 | swap 緩衝[0]↔垃圾資料、rotBuf；緩衝全零→P7；否則→P5a |
| P7 return | R | 至 off3 | 讀 a：0→留 P7；1→P8（首個 causeway 塊） |
| P8 sentinel | R | 至 off4 | 讀 a：1→原點→P9；0→home→WL0fin |
| P9 cwR | R | 至 off3 | 讀 a：1→留 P9（沿 causeway 右行）；0→P11a（過站一塊） |
| P11a | L | 至 off3（5 步） | 過站→WL0fin |
| WL0fin | L | 至 off0 | 過站→P0（回到乾淨組態） |

**設計不變量（宏步歸納用，milestone C 後半）**：offset 暫存器 ≡ 頭絕對
位置 mod 5（`μ = dirOf ∘ 新相位`、`L` 內 offset 依新相位方向鎖步更新）；
翻位前值可預言（延伸翻 0→1、回縮翻 1→0、垃圾標記翻 0→1）；緩衝在
home 遷移期間完整保存 `(q,a)`（d 可重算）、傾倒期間單調清零；
回彈（條件對換反向誤觸）由「可達組態的 (相位, offset, 帶位) 剖面互斥」
排除。

**可逆分支紀律（rev.3 修訂）**：rev.2 原案「條件相位對換複合」在展開時
發現兩類真問題，記錄如下（設計日誌，防止重蹈）：

1. **穿越碰撞**：`swap(X@offω, Y)` 會誤傷「恰好路過 `(offω, 同位值)` 的
   `Y`」——長掃描相位（傾倒/回程/沿 causeway）每 5 格重訪所有 offset，
   躲不掉。條件對換的複合順序可解部分、解不了全部。
2. **控制空間合流 ⟹ L 不單射**：extendL（P1' 翻位進 WL0dep）與
   retractL（P4'a 過站進 WL0dep）兩路徑在進入步的 `(狀態, 帶位)` 像
   **完全相同**（緩衝、相位、offset、位全同）——但 `ofPerm` 要求 `L`
   是全空間置換，合流 = 非單射 = 構造直接不成立。此合流不能用相位
   分身解（兩路徑後續步數相同、奇偶也相同）。

**修法（rev.3）**：
- **緩衝加 1 位路徑位 π**（緩衝 = `m+2` 位 = 記錄 `(q, a)` + π）：
  回縮路徑在翻自家 causeway 位的同一步把 π 翻成 1（狀態位的條件翻位 =
  置換）。兩路徑從此狀態可分 —— π 隨記錄一起倒進垃圾（垃圾內容自由），
  正是 Bennett「丟不掉就外顯」的原教旨手法。
- **控制表架構**：不再複合條件對換。控制空間
  `C := 帶位 × 相位 × offset`（`2 × 32 × 8 = 512`），緩衝抽象成剖面
  `Profile := (d(buf), 緩衝全零?)`（6 值）。整個 FSM 寫成**一張顯式
  正向表** `ctrlFwd : Profile → C → C`（可讀、逐行對相位表）+
  **手寫反向表** `ctrlBwd`（箭頭反轉），互逆用 `decide` 驗
  （每剖面 512 格線性驗證，固定大小、非參數化）。穿越碰撞/合流
  = 表不雙射 = `decide` 當場抓 —— 機器當設計檢查器用。
  長掃描相位如需奇偶分身（twin）在表裡直接加，`decide` 收斂為準。
- `L = (資料段) ∘ (控制段)`：資料段 = P0@off0 的 Feistel +
  P6@off1 的傾倒 swap（條件讀 `(相位, offset)`、動 `(q, 緩衝, 帶位)`）；
  控制段 = 對每個緩衝值查剖面套 `ctrlFwd` 的置換（緩衝不動 ⟹
  shear 合法）。`μ = dirOf ∘ 新相位`；offset 在控制表內與方向鎖步。

## rev.3 展開時撞到的第三層障礙（2026-07-04 設計日誌；**本輪停損點**）

控制表逐行展開時發現，比穿越碰撞更深一層的 L-單射性障礙：

1. **走位相位的過境合流**：`(X@ω+1, b) ↦ (X@ω, b)`（過境列，任意 b）與
   「餵入者把控制送進 `(X@ω, b')`」（入口列）在表層面相撞 —— 5-循環
   offset 使長掃描相位（傾倒/回程）繞滿全部 offset，入口躲不開過境。
   Bennett 式紀律 = **過境相位入度必須為 1**（入口只能落在 guard 正後方，
   且 guard 對兩個位值都離場、杜絕繞圈回灌）⟹ 長掃描相位必須拆成
   「每 guard 一離場」的 twin 交替鏈（descend/descend2 + checkG/checkG2
   + 每個外部餵入點一個入口分身）。
2. **twin 奇偶 = 帶相依歷史 ⟹ 末端合流不可逆**：傾倒迴圈的跳塊數
   （多少塊被垃圾標記/causeway 佔據而跳過）由**帶內容**決定，不由記錄
   `(q,a,π)` 決定 ⟹ twin 交替的末端奇偶無法由狀態重建 ⟹ 兩條 twin 流
   在合流回 `ready` 的那一步 `(狀態, 位)` 像相同 ⟹ **L 不單射，無法用
   有限個相位分身修復**（π 位那招救不了這個：π 救的是「路徑選擇」1 位，
   這裡是「無界的帶相依計數」的奇偶）。
3. 附帶發現：原「緩衝全零 = 傾倒終止」也有同型問題（傾倒塊數 =
   記錄尾零數的函數 —— 這個倒還是記錄可重建的，但為了統一，改
   **固定計數**較穩）：加一個 `m+2` 位 one-hot 環形計數器與緩衝同步旋轉、
   「標記回到位 0」= 打滿 `m+2` 塊 —— 計數與帶無關、無歷史。

**下一步攻擊方向（Bennett 1973 的原始解法，需重設計、本輪不硬塞）**：
BitTM 每步強制「寫 + 移」；Bennett 的 quadruple 形式把**讀寫步與移動步
分離**，可逆性條件變成有限表的局部檢查。我們的機器有 `Dir.stay` ——
可用「stay 步讀寫、隔步移動」模擬 quadruple 紀律：guard 相位以 stay 步
讀格並轉相位（不移），移動相位純移動不讀寫（入度 1 可安排）。這使
「入口落點」與「過境」在**相位層**分離，twin 鏈不再需要；帶相依計數的
奇偶問題也隨之消失（合流點的前驅由「當前格內容 + 相位」局部決定，
正是 quadruple 可逆條件）。代價：微步數約 ×2、相位表重排。
評估：路線清晰、工程量中等，值得做，但屬新一輪工作。

## 仍待決（milestone C 續攻時定案）

- quadruple 式相位表（stay-讀寫步 / 移動步分離）逐行落檔 +
  `decide`/`#eval` 反例迭代（架構：抽象 `SPhase` inductive × `Fin 5`
  offset 的顯式正反表，緩衝抽象成剖面 `(d, 計數歸位?, π)`）。
- one-hot 環形計數器暫存器（`m+2` 位）併入狀態打包。
- 宏步引理歸納結構：相位 × 區段不變量；爆量時先證單一相位段部分引理。
- `IsClean` 的 `h ≠ 0`/散置垃圾一般化（現版 = `h = 0`、垃圾連續特例）。

本檔現況：milestone A（構造 + 可逆）+ B 排程無關半邊（編碼 + `IsClean`）
全證零 sorry；C = rev.2 幾何定案（5 格區塊 + 原點哨兵）+ rev.3 架構
（π 位已入緩衝）+ 上述設計日誌；`shuttleCore` 仍為占位排程 ——
標記驅動排程的正確實作路線已收斂到 quadruple 式，見上。
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

/-- 全緩衝拆分（rev.3）：`m+2` 位 ↔（（舊狀態, 舊讀位）, 路徑位 π）。 -/
def bufSplitPi (m : ℕ) : (Fin (m + 1 + 1) → Bool) ≃ (((Fin m → Bool) × Bool) × Bool) :=
  (bitsSplit (m + 1) 1).trans
    (Equiv.prodCongr (bufSplit m) (Equiv.funUnique (Fin 1) Bool))

/-! ## 相位與 offset 暫存器 -/

/-- shuttle 機相位暫存器：5 位（32 槽；C rev.2 FSM 用 17 個）。 -/
abbrev ShuttlePhase : Type := Fin 5 → Bool

/-- 塊內 offset 暫存器：3 位（mod-5 定位；與走位方向鎖步更新）。 -/
abbrev ShuttleOffset : Type := Fin 3 → Bool

/-- 相位 0（M-step：Feistel 輪）。 -/
def ph0 : ShuttlePhase := fun _ ↦ false

/-- 相位 1（垃圾走位：swap + 旋轉）。 -/
def ph1 : ShuttlePhase := fun j ↦ decide (j = 0)

/-- offset 0（home 工作位）。 -/
def off0 : ShuttleOffset := fun _ ↦ false

/-- 相位遞增底層函數（5 位二進位 +1，mod 32）。 -/
private def phaseIncFun (p : ShuttlePhase) : ShuttlePhase := fun j ↦
  if j = 0 then !(p 0)
  else if j = 1 then xor (p 1) (p 0)
  else if j = 2 then xor (p 2) (p 0 && p 1)
  else if j = 3 then xor (p 3) (p 0 && p 1 && p 2)
  else xor (p 4) (p 0 && p 1 && p 2 && p 3)

/-- 相位遞減底層函數（5 位二進位 −1，mod 32；借位鏈）。 -/
private def phaseDecFun (p : ShuttlePhase) : ShuttlePhase := fun j ↦
  if j = 0 then !(p 0)
  else if j = 1 then xor (p 1) (!(p 0))
  else if j = 2 then xor (p 2) (!(p 0) && !(p 1))
  else if j = 3 then xor (p 3) (!(p 0) && !(p 1) && !(p 2))
  else xor (p 4) (!(p 0) && !(p 1) && !(p 2) && !(p 3))

/-- 相位遞增置換（mod 32 循環）；逆 = 顯式遞減，有限域 `decide` 驗證
（固定 32 元素，非參數化——與 `bennettTM` 可逆性的參數化證明不同層）。 -/
def phaseInc : ShuttlePhase ≃ ShuttlePhase where
  toFun := phaseIncFun
  invFun := phaseDecFun
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

/-- offset 遞增底層函數：3 位暫存器上的 mod-5 循環
`0→1→2→3→4→0`（值 5、6、7 不動 —— 不可達，任意處置皆可）。
編碼：`(b0,b1,b2)` = 低位在前二進位。 -/
private def offIncFun (o : ShuttleOffset) : ShuttleOffset :=
  -- 4 = (false,false,true) → 0；其餘 < 5 走二進位 +1；5..7 不動
  if (!(o 0) && !(o 1) && o 2) then (fun _ ↦ false)
  else if o 2 then o
  else fun j ↦ if j = 0 then !(o 0) else if j = 1 then xor (o 1) (o 0)
    else xor (o 2) (o 0 && o 1)

/-- offset 遞增置換（mod-5 循環，5-循環的逆 = 迭代 4 次；`decide` 驗證）。 -/
def offInc : ShuttleOffset ≃ ShuttleOffset where
  toFun := offIncFun
  invFun := offIncFun^[4]
  left_inv := by intro o; revert o; decide
  right_inv := by intro o; revert o; decide

/-- offset 遞減置換（`offInc` 的逆）。 -/
def offDec : ShuttleOffset ≃ ShuttleOffset := offInc.symm

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
緩衝 = `b+1` 位環（rev.3 傳 `b := m+1` 得 `m+2` 位含 π），旋轉滿圈復位
—— 記錄逐位搬上帶的原語形狀。 -/
def garbagePiece (a b : ℕ) : (((Fin a → Bool) × (Fin (b + 1) → Bool)) × Bool) ≃
    (((Fin a → Bool) × (Fin (b + 1) → Bool)) × Bool) :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _)
      ((swapHead b).trans (Equiv.prodCongr (rotBuf b) (Equiv.refl Bool)))).trans
      (Equiv.prodAssoc _ _ _).symm)

/-- 重排：`(狀態 × (緩衝 × (相位 × offset))) × 帶位 ≃
相位 × ((狀態 × (緩衝 × offset)) × 帶位)`（顯式重括號，結構 eta 使兩側 `rfl`）。 -/
private def reorderAux {α β γ δ : Type*} :
    ((α × (β × (γ × δ))) × Bool) ≃ (γ × ((α × (β × δ)) × Bool)) where
  toFun x := (x.1.2.2.1, ((x.1.1, (x.1.2.1, x.1.2.2.2)), x.2))
  invFun y := ((y.2.1.1, (y.2.1.2.1, (y.1, y.2.1.2.2))), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- offset 靠邊停車：`(狀態 × (緩衝 × offset)) × 帶位 ≃
((狀態 × 緩衝) × 帶位) × offset` —— 讓不碰 offset 的子置換直接複用。 -/
private def parkOff {α β δ : Type*} :
    ((α × (β × δ)) × Bool) ≃ (((α × β) × Bool) × δ) where
  toFun x := (((x.1.1, x.1.2.1), x.2), x.1.2.2)
  invFun y := ((y.1.1.1, (y.1.1.2, y.2)), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- 把不碰 offset 的子置換抬升到帶 offset 的資料空間。 -/
def withOff {α β δ : Type*} (σ : ((α × β) × Bool) ≃ ((α × β) × Bool)) :
    ((α × (β × δ)) × Bool) ≃ ((α × (β × δ)) × Bool) :=
  parkOff.trans ((Equiv.prodCongr σ (Equiv.refl δ)).trans parkOff.symm)

/-! ## Milestone C0 — 介面凍結：控制表剖面 `Profile`（C1pre 裁決，2026-07-08）

C1pre 對抗艦隊裁決 = `SOUND_with_extra_bounded_fields`：控制表 `ctrlFwd/ctrlBwd`
只 case 這 4 個布林剖面（`|Profile| = 16`、O(1) 與 `m` 無關），緩衝/環計數器其餘位
當 spectator 原封帶過（spectator-data 模式，接地 `feistelCore/rotBuf`）。凍結
2026-07-08；`SPhase` 最終大小待 C1b 入度審計，本型別**不含相位**。三向對抗
（環計數器帶相依 / move 入度 / Profile 投影有損）全被擋、無反例。 -/

/-- 控制表剖面：4 個布林，欄位序 `(d, π, ringAtZero, guardBit)`。取乘積型別
以自動獲得 `Fintype`/`DecidableEq`（Bool^4）。 -/
abbrev Profile : Type := Bool × Bool × Bool × Bool

namespace Profile

/-- 緩衝 shear 方向。 -/
def d (p : Profile) : Bool := p.1
/-- 路徑位 π（extendL/retractL 合流消歧；rev.3 修，quadruple 下仍需）。 -/
def pathBit (p : Profile) : Bool := p.2.1
/-- one-hot 環計數器轉滿一圈旗標（取代冗餘的「緩衝全零?」旗）。 -/
def ringAtZero (p : Profile) : Bool := p.2.2.1
/-- guard-step 讀的單一帶位（讓相位分離成立的新成分）。 -/
def guardBit (p : Profile) : Bool := p.2.2.2

/-- `|Profile| = 16`：固定有限、與 `m` 及垃圾深度無關 —— `decide` 隔離可行的前提。 -/
theorem card_eq : Fintype.card Profile = 16 := by decide

end Profile

/-! ## Milestone C1a — 控制表機器（decide 仲裁）+ 相位骨架（2026-07-08 起，增量）

**誠實界線**：完整 quadruple 編舞（~34 相位）需 table→`decide`→反例迭代，
前三輪（rev.1/2/3）皆栽於此、非一次成型。本節先立**可重用機器**＋**相位型別
與 guard/move 可判定分區**＋**種子驗證表**（真 `decide` 過），完整編舞逐相位
增補、每次 `decide` 重驗；move 相位入度 1（C1pre 唯一殘留風險）正由此 `decide`
當場裁。SPhase 構造子集會隨入度審計增減 —— 故 C0 `Profile` 刻意不含相位。 -/

/-- **控制表機器**：`Fintype` 上一對 `decide`-驗互逆的 `(fwd, bwd)` 打包成置換。
這是 C1a→C1b→C2 的介面 —— 換表時只有 `fwd/bwd` 內容變，此打包不變；
`decide` 驗 `bwd∘fwd = id ∧ fwd∘bwd = id` 是「L 在控制層單射」的有限仲裁。 -/
def ctrlEquivOfInverse {C : Type*} (fwd bwd : C → C)
    (hl : ∀ c, bwd (fwd c) = c) (hr : ∀ c, fwd (bwd c) = c) : C ≃ C :=
  ⟨fwd, bwd, hl, hr⟩

@[simp] theorem ctrlEquivOfInverse_apply {C : Type*} (fwd bwd : C → C) (hl hr) (c : C) :
    ctrlEquivOfInverse fwd bwd hl hr c = fwd c := rfl

/-- Quadruple 相位骨架（**種子**；完整編舞逐相位增補）。quadruple 紀律：
guard 相位 = `Dir.stay` 步讀格並轉相位（不移）；move 相位 = 純平移、入度 1。 -/
inductive SPhase
  /-- M-step 前，讀寫頭在 home 工作格。 -/
  | ready
  /-- Feistel M-step（guard：讀工作位）。 -/
  | mstep
  /-- 垃圾推送 guard（讀垃圾標記，決定續推或停）。 -/
  | pushG
  /-- 垃圾推送 move（前進一格，入度 1）。 -/
  | pushM
  /-- 返家 move（回 home，入度 1）。 -/
  | ret
  deriving DecidableEq, Fintype, Repr

/-- guard/move 可判定分區（quadruple 紀律）：guard = stay 讀寫、move = 純平移。 -/
def SPhase.isGuard : SPhase → Bool
  | .ready => true
  | .mstep => true
  | .pushG => true
  | .pushM => false
  | .ret => false

/-- 種子控制表正向（一 M-step 週期的相位骨架環）：
`ready → mstep → pushG → pushM → ret → ready`。此為純相位循環種子，
demonstrate 機器與環閉合；guard 讀位分支、offset 鎖步、Profile 消歧
是後續逐相位增補的內容。 -/
def seedFwd : SPhase → SPhase
  | .ready => .mstep
  | .mstep => .pushG
  | .pushG => .pushM
  | .pushM => .ret
  | .ret => .ready

/-- 種子控制表反向（環反轉，手寫）。 -/
def seedBwd : SPhase → SPhase
  | .mstep => .ready
  | .pushG => .mstep
  | .pushM => .pushG
  | .ret => .pushM
  | .ready => .ret

/-- **種子表是置換**（`decide` 驗互逆——C1b 式仲裁在種子上跑通）。 -/
def seedCtrl : SPhase ≃ SPhase :=
  ctrlEquivOfInverse seedFwd seedBwd (by decide) (by decide)

/-- 種子相位環無固定點（每相位真前進——環閉合的健全性檢查，`decide`）。 -/
theorem seedFwd_no_fixpoint : ∀ p : SPhase, seedFwd p ≠ p := by decide

/-! ### 真控制空間上的表（offset 鎖步；skew-product 雙射）

**關鍵結構**：控制段**保持帶位**（guard = `Dir.stay` 不寫帶）、緩衝當 spectator，
故控制段是每 (`Profile`, 帶位) 區塊上 (相位, offset) 的置換。相位走骨架環
（`seedFwd` 的 5-循環）、move 相位 `pushM`/`ret` 以 `offInc`/`offDec` 鎖步 offset。
形如 `(p, o) ↦ (σ p, τ_p o)`（σ 相位雙射、每 τ_p offset 雙射）＝ **skew product**、
自動雙射 —— `decide` 驗互逆確認。

**未含（下一輪增補）**：guard 相位對帶位的真分支（帶位在區塊內、每帶值各自
雙射）、`Profile` 剖面對回縮/推送的參數化分派、one-hot 環計數器終止。 -/

/-- 完整控制空間（rev.3）：帶位 × 相位 × offset。 -/
abbrev CtrlSpace : Type := Bool × SPhase × ShuttleOffset

/-- 骨架控制表正向：相位環 + move 相位 offset 鎖步（`pushM` 進、`ret` 退）。 -/
def ctrl0Fwd : CtrlSpace → CtrlSpace
  | (b, .ready, o) => (b, .mstep, o)
  | (b, .mstep, o) => (b, .pushG, o)
  | (b, .pushG, o) => (b, .pushM, o)
  | (b, .pushM, o) => (b, .ret, offInc o)
  | (b, .ret, o)   => (b, .ready, offDec o)

/-- 骨架控制表反向（相位環反轉 + offset 動作反轉，手寫）。 -/
def ctrl0Bwd : CtrlSpace → CtrlSpace
  | (b, .mstep, o) => (b, .ready, o)
  | (b, .pushG, o) => (b, .mstep, o)
  | (b, .pushM, o) => (b, .pushG, o)
  | (b, .ret, o)   => (b, .pushM, offDec o)
  | (b, .ready, o) => (b, .ret, offInc o)

/-- **骨架控制表是置換**（`decide` 驗互逆 —— C1b 式仲裁在真控制空間跑通、
offset 鎖步含在內）。 -/
def ctrl0 : CtrlSpace ≃ CtrlSpace :=
  ctrlEquivOfInverse ctrl0Fwd ctrl0Bwd (by decide) (by decide)

/-- 控制段保持帶位（`Dir.stay` 不寫帶的形式化健全性檢查，`decide`）。 -/
theorem ctrl0Fwd_preserves_bit : ∀ c : CtrlSpace, (ctrl0Fwd c).1 = c.1 := by decide

/-! ### 加 guard 分支：`pushG` 讀帶位分岔（bit-block 各自雙射）

`pushG` 成為真 guard：讀當前帶位分岔 —— 位設（垃圾標記在）→ 續推 `pushM`、
位清 → 返家 `ret`。**關鍵可逆論證**：控制保持帶位，故 (相位,offset) 在
帶位=false 與 =true 兩區塊**各自獨立**；兩區塊可用**不同**相位置換 σ_false/σ_true
（false 塊：`pushG→ret`、`pushM` 停為 fixpoint；true 塊：完整推送環），
只要每塊各自是 (相位,offset) 置換即整體雙射（skew-product 對每 bit-block）。
`decide` 驗互逆確認分支未破壞雙射性 —— 這正是 in-degree-1 紀律的機器裁決。 -/

/-- guard 版控制表正向：`pushG` 依帶位分岔。 -/
def ctrlGFwd : CtrlSpace → CtrlSpace
  | (b, .ready, o) => (b, .mstep, o)
  | (b, .mstep, o) => (b, .pushG, o)
  | (true, .pushG, o) => (true, .pushM, o)
  | (false, .pushG, o) => (false, .ret, o)
  | (true, .pushM, o) => (true, .ret, offInc o)
  | (false, .pushM, o) => (false, .pushM, offInc o)
  | (b, .ret, o) => (b, .ready, offDec o)

/-- guard 版控制表反向（逐 bit-block 反轉，手寫）。 -/
def ctrlGBwd : CtrlSpace → CtrlSpace
  | (b, .mstep, o) => (b, .ready, o)
  | (b, .pushG, o) => (b, .mstep, o)
  | (true, .pushM, o) => (true, .pushG, o)
  | (false, .pushM, o) => (false, .pushM, offDec o)
  | (true, .ret, o) => (true, .pushM, offDec o)
  | (false, .ret, o) => (false, .pushG, o)
  | (b, .ready, o) => (b, .ret, offInc o)

/-- **guard 版控制表是置換**（`decide` 驗互逆 —— 真帶位分支未破壞雙射性）。 -/
def ctrlG : CtrlSpace ≃ CtrlSpace :=
  ctrlEquivOfInverse ctrlGFwd ctrlGBwd (by decide) (by decide)

/-- guard 保持帶位（分支只讀不寫帶）。 -/
theorem ctrlGFwd_preserves_bit : ∀ c : CtrlSpace, (ctrlGFwd c).1 = c.1 := by decide

/-- **`pushG` 真的對帶位分岔**（位設→`pushM` 續推、位清→`ret` 返家）——
guard 語意的健全性檢查，非退化成 bit-無關。 -/
theorem ctrlGFwd_pushG_branches (o : ShuttleOffset) :
    (ctrlGFwd (true, .pushG, o)).2.1 = SPhase.pushM ∧
    (ctrlGFwd (false, .pushG, o)).2.1 = SPhase.ret := ⟨rfl, rfl⟩

/-! ## 機器級構造 -/

namespace BitTM

variable (M : BitTM)

/-- shuttle 機狀態位數：M-狀態 `m` 位 + 緩衝 `m+2` 位（記錄 + 路徑位 π）
+ 相位 5 位 + offset 3 位。 -/
abbrev shuttleBits : ℕ := M.m + ((M.m + 1 + 1) + (5 + 3))

/-- 狀態打包：滿位向量 ↔（M-狀態, 緩衝, 相位, offset）。 -/
def shuttleUnpack : (Fin M.shuttleBits → Bool) ≃
    ((Fin M.m → Bool) × ((Fin (M.m + 1 + 1) → Bool) × (ShuttlePhase × ShuttleOffset))) :=
  (bitsSplit M.m ((M.m + 1 + 1) + (5 + 3))).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((bitsSplit (M.m + 1 + 1) (5 + 3)).trans
        (Equiv.prodCongr (Equiv.refl _) (bitsSplit 5 3))))

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

/-- Feistel 核心搬到（M-狀態 × 全緩衝）× 帶位：緩衝經 `bufSplitPi` 拆成
（（舊狀態槽, 舊讀位槽）, π），π 經 `parkOff` 停車、Feistel 不碰。 -/
def feistelPiece : (((Fin M.m → Bool) × (Fin (M.m + 1 + 1) → Bool)) × Bool) ≃
    (((Fin M.m → Bool) × (Fin (M.m + 1 + 1) → Bool)) × Bool) :=
  (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (bufSplitPi M.m)) (Equiv.refl Bool)).trans
    ((parkOff.trans
      ((Equiv.prodCongr M.feistelCore (Equiv.refl Bool)).trans parkOff.symm)).trans
      (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (bufSplitPi M.m).symm)
        (Equiv.refl Bool)))

/-- shuttle 核心的資料空間：（M-狀態 ×（緩衝 × offset））× 帶位。 -/
abbrev ShuttleData : Type :=
  ((Fin M.m → Bool) × ((Fin (M.m + 1 + 1) → Bool) × ShuttleOffset)) × Bool

/-- 相位分派核心（**占位排程**：相位 0 = Feistel M-step、相位 1 = 垃圾走位、
其餘恆等；每微步後相位 +1）。milestone C 換成標記驅動的可逆分支排程
—— 換排程不影響本檔的可逆性定理。 -/
def shuttleCore : (ShuttlePhase × M.ShuttleData) ≃ (ShuttlePhase × M.ShuttleData) :=
  (phaseDispatch ph0 (withOff M.feistelPiece)).trans
    ((phaseDispatch ph1 (withOff (garbagePiece M.m (M.m + 1)))).trans
      (Equiv.prodCongr phaseInc (Equiv.refl _)))

/-- **局部更新置換 `L`**（README 步驟 1、3）：打包共軛的相位分派核心。
全空間置換 —— 非法/未用相位走恆等。 -/
def shuttleL : ((Fin M.shuttleBits → Bool) × Bool) ≃ ((Fin M.shuttleBits → Bool) × Bool) :=
  ((Equiv.prodCongr M.shuttleUnpack (Equiv.refl Bool)).trans reorderAux).trans
    (M.shuttleCore.trans
      (reorderAux.symm.trans (Equiv.prodCongr M.shuttleUnpack.symm (Equiv.refl Bool))))

/-- **方向表 `μ`**：只讀新狀態（`ofPerm` 約束：方向只能依賴更新後狀態；
可讀相位/緩衝/offset）。占位：垃圾走位相位向左、其餘停 —— C rev.1 排程
落地時逐相位校正。 -/
def shuttleDir (s : Fin M.shuttleBits → Bool) : Dir :=
  if (M.shuttleUnpack s).2.2.1 = ph1 then Dir.left else Dir.stay

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

5 格區塊帶佈局（rev.2 幾何，取代早期 4-軌案）：模擬帶格 `k` ↦
shuttle 帶位 `5k..5k+4` =（off0 工作位、off1 垃圾資料位、off2 垃圾標記位、
off3 home/causeway 標記位、off4 原點哨兵）。

**誠實界線**：本節只給排程無關的部分 —— 編碼、乾淨組態謂詞、
「編碼產出乾淨組態」。每類微步保不變量的單步引理**綁定微步排程**，
而現行排程是占位（見 `shuttleCore` docstring），故與 milestone C 的
標記驅動排程一起做，避免對將被替換的排程證死引理。 -/

/-- 空白緩衝。 -/
def blankBuf : Fin (M.m + 1 + 1) → Bool := fun _ ↦ false

/-- 打包 shuttle 狀態（`shuttleUnpack` 的逆）。 -/
def shuttlePack (q : Fin M.m → Bool) (buf : Fin (M.m + 1 + 1) → Bool)
    (p : ShuttlePhase) (o : ShuttleOffset) : Fin M.shuttleBits → Bool :=
  M.shuttleUnpack.symm (q, (buf, (p, o)))

@[simp] theorem shuttleUnpack_shuttlePack (q : Fin M.m → Bool)
    (buf : Fin (M.m + 1 + 1) → Bool) (p : ShuttlePhase) (o : ShuttleOffset) :
    M.shuttleUnpack (M.shuttlePack q buf p o) = (q, (buf, (p, o))) :=
  M.shuttleUnpack.apply_symm_apply _

/-- 編碼帶：工作軌載模擬帶、垃圾兩軌全空、causeway 標記唯一在區塊 0
（`h = 0` 單點）、原點哨兵在區塊 0（帶位 4，永不被協定改寫）。 -/
def shuttleEncodeTape (t : ℤ → Bool) : ℤ → Bool := fun i ↦
  if i % 5 = 0 then t (i / 5)
  else if i = 3 then true
  else if i = 4 then true
  else false

/-- **編碼**：模擬組態 → shuttle 機組態（相位 0、緩衝空白、垃圾空、
head 在 home 區塊工作位）。 -/
def shuttleEncode (c : M.Cfg) : M.bennettTM.Cfg :=
  (M.shuttlePack c.1 M.blankBuf ph0 off0, shuttleEncodeTape c.2)

/-- **乾淨組態謂詞**（垃圾堆疊長 `L`；垃圾內容自由 —— 宏步引理中
以存在量詞外顯，語意比照 M3c `bennettAut_iterate`）：
相位 0、offset 0、緩衝空白、工作軌 = 模擬帶、causeway 標記唯一在區塊 0、
原點哨兵唯一在區塊 0、垃圾標記恰為區塊 `[-L, 0)` 的連續區段（`h = 0`、
垃圾連續特例；`h ≠ 0` / 散置垃圾的一般化與宏步引理一起加）、
未標記垃圾格 = 0。 -/
def IsClean (L : ℕ) (c : M.bennettTM.Cfg) (q : Fin M.m → Bool) (t : ℤ → Bool) : Prop :=
  M.shuttleUnpack c.1 = (q, (M.blankBuf, (ph0, off0))) ∧
  (∀ k : ℤ, c.2 (5 * k) = t k) ∧
  (∀ k : ℤ, c.2 (5 * k + 3) = decide (k = 0)) ∧
  (∀ k : ℤ, c.2 (5 * k + 4) = decide (k = 0)) ∧
  (∀ k : ℤ, c.2 (5 * k + 2) = decide (-(L : ℤ) ≤ k ∧ k < 0)) ∧
  (∀ k : ℤ, c.2 (5 * k + 2) = false → c.2 (5 * k + 1) = false)

/-- **編碼產出乾淨組態**（垃圾堆疊長 0）。 -/
theorem shuttleEncode_isClean (c : M.Cfg) :
    M.IsClean 0 (M.shuttleEncode c) c.1 c.2 := by
  refine ⟨M.shuttleUnpack_shuttlePack _ _ _ _, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_,
    fun k ↦ ?_, fun k ↦ ?_⟩
  · change shuttleEncodeTape c.2 (5 * k) = c.2 k
    simp only [shuttleEncodeTape]
    rw [if_pos (by omega : (5 * k) % 5 = 0),
      Int.mul_ediv_cancel_left k (by norm_num : (5 : ℤ) ≠ 0)]
  · change shuttleEncodeTape c.2 (5 * k + 3) = decide (k = 0)
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(5 * k + 3) % 5 = 0)]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos (by omega : (5 * (0 : ℤ) + 3) = 3), eq_comm]
      exact decide_eq_true rfl
    · rw [if_neg (by omega : ¬(5 * k + 3) = 3), if_neg (by omega : ¬(5 * k + 3) = 4),
        eq_comm]
      exact decide_eq_false hk
  · change shuttleEncodeTape c.2 (5 * k + 4) = decide (k = 0)
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(5 * k + 4) % 5 = 0), if_neg (by omega : ¬(5 * k + 4) = 3)]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos (by omega : (5 * (0 : ℤ) + 4) = 4), eq_comm]
      exact decide_eq_true rfl
    · rw [if_neg (by omega : ¬(5 * k + 4) = 4), eq_comm]
      exact decide_eq_false hk
  · change shuttleEncodeTape c.2 (5 * k + 2) = decide (-(0 : ℤ) ≤ k ∧ k < 0)
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(5 * k + 2) % 5 = 0), if_neg (by omega : ¬(5 * k + 2) = 3),
      if_neg (by omega : ¬(5 * k + 2) = 4), eq_comm]
    exact decide_eq_false (by omega)
  · intro _
    change shuttleEncodeTape c.2 (5 * k + 1) = false
    simp only [shuttleEncodeTape]
    rw [if_neg (by omega : ¬(5 * k + 1) % 5 = 0), if_neg (by omega : ¬(5 * k + 1) = 3),
      if_neg (by omega : ¬(5 * k + 1) = 4)]

/-! ## Milestone C3c — `IsCleanQuad`：垃圾散置一般化（2026-07-08）

現行 `IsClean` 把垃圾標記寫死成**連續**區段 `[-L, 0)`（`decide (-L ≤ k < 0)`）。
quadruple guard 相位掃的正是任意可達帶幾何，故需把垃圾標記一般化成**任意**
函數 `g : ℤ → Bool`（散置垃圾）。此節**排程無關、day-1 可起**（不依賴 C1/C2 的
控制表內容），是承諾範圍 C0→C3 最早能銀行的成果。

證：(1) 連續特例 `IsClean L ⟹ IsCleanQuad`（實例化 `g = 區段指示`）；
(2) 編碼產出 `IsCleanQuad`（`g = 全 false`，垃圾空）。「未標記格 ⟹ 資料 0」
不變量在一般 `g` 下逐字保留。 -/

/-- **乾淨組態謂詞（散置垃圾一般化）**：垃圾標記軌 = 任意 `g : ℤ → Bool`，
其餘（相位/緩衝/工作軌/causeway/哨兵、及「未標記 ⟹ 資料 0」）同 `IsClean`。 -/
def IsCleanQuad (c : M.bennettTM.Cfg) (q : Fin M.m → Bool) (t : ℤ → Bool)
    (g : ℤ → Bool) : Prop :=
  M.shuttleUnpack c.1 = (q, (M.blankBuf, (ph0, off0))) ∧
  (∀ k : ℤ, c.2 (5 * k) = t k) ∧
  (∀ k : ℤ, c.2 (5 * k + 3) = decide (k = 0)) ∧
  (∀ k : ℤ, c.2 (5 * k + 4) = decide (k = 0)) ∧
  (∀ k : ℤ, c.2 (5 * k + 2) = g k) ∧
  (∀ k : ℤ, g k = false → c.2 (5 * k + 1) = false)

/-- **連續垃圾是散置的特例**：`IsClean L` 蘊含 `IsCleanQuad`，
垃圾函數實例化為區段指示 `k ↦ decide (-L ≤ k < 0)`。 -/
theorem IsClean_toQuad {L : ℕ} {c : M.bennettTM.Cfg} {q : Fin M.m → Bool} {t : ℤ → Bool}
    (h : M.IsClean L c q t) :
    M.IsCleanQuad c q t (fun k ↦ decide (-(L : ℤ) ≤ k ∧ k < 0)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun k hk ↦ h6 k (h5 k ▸ hk)⟩

/-- **編碼產出乾淨組態（散置版）**：垃圾標記軌全 `false`（垃圾空）。 -/
theorem shuttleEncode_isCleanQuad (c : M.Cfg) :
    M.IsCleanQuad (M.shuttleEncode c) c.1 c.2 (fun _ ↦ false) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := M.shuttleEncode_isClean c
  refine ⟨h1, h2, h3, h4, fun k ↦ ?_, fun k _ ↦ h6 k ?_⟩ <;>
    · rw [h5 k]; exact decide_eq_false (by omega)

end BitTM

end

end FluidTuring
