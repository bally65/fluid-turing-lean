# GPAC σ 構造路線圖 — unblock 線三 Brick 6（真·光滑 analog 流不可判定）

> 2026-07-10 起手。目標 = 造出 Brick 6 決策文件（`BRICK6_DECISION.md`）§6 所需的**光滑** `σ : ℝ→ℝ`，
> 使線三從「條件式/σ 抽象」升級為**真·光滑 ODE 流逐步模擬 TM ⟹ 到達性不可判定**（超越主線 M33 的
> 拓撲懸掛流）。**這是多月 mathlib-from-zero research**；本文是**主控推理的分解**（待 8:10pm 額度回、
> 對抗設計 workflow 驗證後可能調整）。誠實：只有做出全部 G-brick，Brick 6 (B) 版假設才可實例化。

## 目標 σ 的四性質（= Brick 6 三牆的正面版）

`σ : ℝ→ℝ` 需同時：
1. **光滑**（C^∞）——ODE 場需要；
2. **格點 = TM step**：`σ(enc c) = enc(step c)`；
3. **tube-Lipschitz**：於編碼格點的 tube 上有 Lipschitz 常數（餵 Brick 5 `tracks_ideal` 的 H1）；
4. **向格點收縮（re-rounding / 數位穩健）**：每步把累積誤差拉回、tube 不變式對**一般（擴張）**TM 成立
   （破 Brick 6 Wall B）。

## 編碼（Graça/Branicky 標準）

TM 組態 `c = (q, 左帶, 右帶, 讀頭符號)`：
- 狀態 `q ∈ Fin |Q|` → 整數 `ℝ`；
- 帶 = base-`k` 數字串 → 實數 `∈ [0,1)`（讀頭旁的符號 = 首位數字 `⌊k·y⌋`）；
- 一步 = 讀首位 → 查轉移表（有限 case）→ 改狀態 + 位移（乘/除 `k` + 加減）+ 寫符號。
- 全部「讀 / case / 寫 / 位移」須**光滑化**（見 G-bricks）。

## 有序 G-bricks（每塊 = 顯式函數 + HasDerivAt + 性質，延續 M39-43 紀律、零抽象 ODE 存在性）

| Brick | 內容 | 難度 | mathlib 缺口 | 專案資產 |
|---|---|---|---|---|
| **G1** | **smooth 分支 `smoothSelect`**：`s≤0→a, s≥1→b`、光滑（case 分析原子） | 低 ✅**先做** | 無（用 M41 `smoothTransition`） | M41 |
| G2 | **smooth 讀符號**：`⌊k·y⌋` 於格點的光滑逼近（首位數字提取） | 中 | 無 smooth floor/mod | M41 smoothTransition |
| G3 | **smooth 數位穩健（re-rounding）**：向最近格點收縮 `\|r(x)-round(x)\|≤ρ\|x-round(x)\|`, `ρ<1`（破 Wall B） | **高** | 無 smooth round-with-contraction；需自造誤差界 | M40/M41 gated |
| G4 | **smooth 單步 `σ`**：G1∘G2 + 位移組成，證 `σ(enc c)=enc(step c)`（格點精確） | 高 | 無 | G1-G3 |
| G5 | **tube 不變式**：G3 re-rounding + Brick 5 `tracks_ideal` ⟹ `∀n, dec(xₙ)=configₙ`（**推導**非假設） | 高 | 需 tube 幾何 + 誤差傳播 | M43 tracks_ideal |
| G6 | **轉移 splice**：G5 + M16/M30 TM 停機不可判定 ⟹ analog 流到達性不可判定（**兌現 Brick 6 (B) genuine 版**） | 中 | 無（接已證資產） | M16/M30/M33 手法 |

**關鍵 crux = G3**（smooth round-with-contraction）——這是 Wall B 的正面攻堅、GPAC 數位穩健的心臟。
G3 通 → G4/G5 是組裝 → G6 接已證停機不可判定。**G3 是真 research 核心**（Branicky error-correction 的
Lean 化、需自造光滑 round 的顯式收縮界）。

## 誠實邊界（持續）

- 每塊 G-brick 仍**只寫顯式函數 + HasDerivAt**（不碰 mathlib 抽象 ODE 存在性，延續 M39-43）。
- σ **具體化**後線三才脫離「σ 抽象」——但 G3/G5 是多月工程；**在 G6 兌現前，不宣稱線三達成 undecidability**。
- 主線 M33 的無條件結果**不受影響**（GPAC 是另一條、更強語意[真光滑場]、但更難的路線）。
- 路線圖本身 = 主控推理，**待對抗設計 workflow 驗證**（8:10pm 額度回）——brick 順序/編碼選擇/mathlib 缺口
  可能調整。

## 現在起手 = G1（smooth 分支，M44_SmoothSelect.lean）

最低風險、最清楚可達、明確 GPAC 基石（TM 轉移表的有限 case 分析 = n-way smoothSelect 的巢狀/疊加）。
先建 G1 立地基，G2/G3 續攻（G3 為真核心、需最多 research）。

---

## 2026-07-10 更新：G3 已建（M45）+ 難度修正（G3 非多月心臟、真 crux 在 G2）

**G3 設計 scope workflow（wf_776adfe3）裁決 = G3A_ACHIEVABLE**，並**修正本路線圖兩處誤導**：
1. **G3 資產不是 smoothTransition（M40/M41）**：smoothTransition 單調（平坦→升→平坦）是 gating/select
   工具（G1），是週期 re-rounding 的**錯工具**，且 mathlib 對它**零導數界引理**（M44 已撞牆）。
   **G3 改用週期 `sin`**：`sround(x)=x−sin(2πx)/(2π)`，整數 = 超吸引不動點、導數閉式 `1−cos(2πx)`、
   mathlib trig 全套量化支援。
2. **G3 不是多月心臟**：M45 一次建成（8 定理、零 sorry、標準三公理），含 CRUX `sround_contract`
   （basin 收縮 `ρ=1−cos(2πδ)`，MVT）+ **`bounded_orbit`（破 Wall B：發散 `ΣLⁱ` → 收斂 `b/(1−Λ)`）**。
   **真 crux 移到 G2**（smooth 讀符號 `⌊k·y⌋` 於格點**精確**——mathlib 無 smooth floor，且 G4 需
   `σ(enc c)=enc(step c)` **字面相等**非 ε-近似）——**比 G3 難**。

**修正 G-brick 難度**：G1 ✅（M44）、**G3 ✅（M45，低-中，非多月）**、**G2 = 新真核心 crux（高、mathlib
無 smooth floor）**、G4/G5 = 組裝（G5 有 `bounded_orbit` 備）、G6 = 接停機不可判定（中）、自治流黏合 =
paper-blocked。**下一步 = G2（smooth 讀符號 exact-on-lattice）= 真核心**，建議下輪先跑 G2 設計 scope。
**`ρ<1` 只在 `δ<1/4` 嚴格**（半整數斥不動點）= smooth rounding 內稟，下游全程 `δ`-tube。

## 2026-07-10 更新②：G2 已建（M46）— 診斷更正「G2 不是 smooth floor」

**G2 設計 scope（wf_047bf8a0）裁決 = G2A_ACHIEVABLE**。診斷更正：G2 標成「卡 mathlib 無 smooth floor」
是**範疇錯誤**——不需 smooth floor（不連續、不可能），需要的是 **gap 編碼格點上精確的光滑階梯**，
直接用 M41/M44 的 exact-plateau 引理（`smoothTransition.zero_of_nonpos/one_of_one_le`）疊出、≈ M41 等級。
**G2 已建（M46）**：`sstep c g u=smoothTransition((u−c)/g)`（單階）+ `sfloor k w u=∑_{j<k−1} sstep(j+w,1−w,u)`
（階梯）；**`sfloor_exact_on_plateau`（★CRUX★：`u∈[j₀,j₀+w]⟹sfloor=j₀` 字面相等）**+ `_contDiff`+`_hasDerivAt`。

**★新增誠實 concern（Brick 6 之上的真決策點）★**：整條 GPAC 線用 **C^∞（smoothTransition=expNegInvGlue）、
非 analytic**（`ContDiff ℝ ⊤` 現指 analytic ω、smoothTransition 對它為假；只 `ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`
=C^∞）。**本線目標 = C^∞ 光滑流**（同 M13 起全線）；**若** Brick 6 真目標是**嚴格 GPAC（analytic 向量場）**，
則 exact-on-lattice 是**不可能定理**（analytic 區間常值⟹全域常值）、M40-46 scaffold 離題。需先釘死此語意。

**修正 G-brick 難度（再次）**：G1✅(M44)、G2✅(M46、≈M41 等級非多月)、G3✅(M45)。**真牆全在下游、與 G2/G3
正交**：φ 自治化（M41 已標多月）、真不連續 σ 全域 tube 不變式（Wall A/B）、GPAC analytic 語意分歧（上）、
邊際價值（條件式仍弱於且冗餘於 M33 無條件）。**剩 G4（組單步 σ 格點精確恆等）+G5（tube 不變式、有
`bounded_orbit` 備）+G6（splice 停機不可判定）= 組裝為主，真牆是 φ 自治化 + analytic 語意。**

## 2026-07-10 更新③：G4a-c 已建（M47）— 單步 σ 格點精確組件

**G4 設計 scope（wf_e8cb6d82）裁決 = G4A_ACHIEVABLE**（全 σ 多 session，G4a-c 格點精確組件一次可達）。
洞見：不需「sfloor 再 smoothSelect 兩步」——`slookup`（value-carrying、telescoping）把 read∘lookup 融一階。
**G4a-c 已建（M47）**：
- G4a `slookup`（值載光滑查表）+ **`slookup_exact_on_plateau`（★CRUX 字面相等★）**+ `_contDiff`/`_hasDerivAt`；
  `stateNext`（read∘lookup 融合）+ `stateNext_exact`。
- G4b `tbl2D`（巢狀兩層）+ `tbl2D_exact`（(q,s)→δ q s 格點精確）。
- G4c `encTape`（Horner 分數）+ `moveR_exact`/`write_exact`（★move/write=純 `field_simp;ring`、無 Nat.digits★）。

**剩（多 session）**：G4d 全 σ 組裝（`σ:ℝ^d→ℝ^d`、正則憑證 ContDiff/HasFDerivAt）、G4e BitTM `ℤ→Bool`
帶橋（M25/M3b 級純簿記、工時中心）。**真牆全在下游、正交**：φ 自治化（多月）、plateau-readability 全域
tube 不變式（G5）、GPAC analytic 語意分歧、邊際價值（弱於 M33 無條件）。base `K=4k` 綁 headroom。
編碼決策=多分量向量 `(q,L,R)`。plateau 前提是假設（G5 discharge）、禁宣稱模擬 TM。

## 2026-07-10 更新④：G4d1 已建（M48）— 玩具全 σ demo（組件真拼得起來）

**G4d 設計 scope（wf_4c64fff7）裁決 = G4D_ACHIEVABLE**，且 agent lean_run_code 驗過**完整玩具右移-only
全 σ demo**。**G4d1 已建（M48）**：對 module-local 真 step `gStepR`（讀 R 首符、q→δq、寫 δw 入 L、R 右移），
組出顯式 `sigmaR:ℝ³→ℝ³`，證：
- **`sigmaR_exact`（★CRUX★）**：`σ(gEnc c)=gEnc(gStepR c)` **三分量逐一字面相等**（純組裝 M47/M46 引理：
  q'=tbl2D_exact、L'=push encTape、R'=sfloor_exact+moveR_exact）。**組件真拼得起來、對真 step 恆等。**
- `tbl2D_contDiff`（唯一新引理、**2 行 fun_prop**）+ `sigmaR_contDiff`（`ContDiff.prodMk` tuple C^∞）。
- **編碼決策拍板**：σ 用 `Prod`（ℝ×ℝ×ℝ），非 Fin 3→ℝ（prodMk 有直接建構子）。

**修正難度**：split 報告估 tbl2D_contDiff「20-35 行手工」= 過度悲觀（fun_prop 2 行）。σ-assembly 報告點
「σ₃ 左移三層巢狀」為最難 = 屬 G4d2、不在第一子磚。**剩**：G4d2（雙向 move、smoothSelect 挑臂、左移
三層巢狀 = 真機唯一新難點）、G4d3（多符號泛化 + 若 ODE 需 Jacobian 補 HasFDerivAt）、G4e（BitTM 帶橋、
邊界 L=[]/R=[] 破功需 eventually-0 stream 編碼、工時中心）。真牆不動：φ 自治化/G5 tube/analytic 語意/
邊際價值弱於 M33。**注**：sround(G3) 不可施於原始帶分量（非整數格點）、只作用狀態暫存器 + scaled read。

## 2026-07-11 更新⑤：G4d2 已建（M49）— 雙向 move 玩具全 σ（左移三層巢狀=純 ring）

**G4d2 設計 scope（wf_c05b5f18）裁決 = G4D2_ACHIEVABLE**（一磚、非多輪；agent lean_run_code 全驗）。
**G4d2 已建（M49）**：G4d1 右移-only 的**對稱鏡像 + 一新結構**。轉移表多 move 欄（M∈{0,1} 由第三個
tbl2D 查得字面）；每移動帶分量 = `smoothSelect(M, 左移臂, 右移臂)`（M=0→_left(0≤0)、M=1→_right(1≤1)）。
- **`moveL_R_exact`（★三層巢狀難點★）= 一行 `field_simp;ring`** —— **反駁「真機唯一新難點/多輪」恐懼**。
- `smoothSelect_contDiff`（唯一新義務、M44 只出 1-D、就地補）。
- **`sigmaRL_exact`（★CRUX★）**：雙向 `σ(gEnc c)=gEnc(gStepRL c)` 字面相等（cases move、smoothSelect
  挑臂、各臂 M47 純代數）+ `sigmaRL_contDiff`（ContDiff.prodMk + smoothSelect_contDiff）。

**G4d2 相對 G4d1 唯一真新增負擔 = 多一條 plateau 義務**（也讀 L 首符 l₀、新增 hsloL/hshiL）⟹ 下游 G5
tube 須維持**兩半帶皆可讀**（歸納不變式工作、非 paper-block）。**剩**：G4e（BitTM 帶橋、L=[]/R=[] 邊界破功
需 eventually-0 雙向 stream 編碼、M25 級工時中心）、G4d3（多符號 |Γ|>2 + ODE 場 Jacobian HasFDerivAt、
ContDiff 不提供）、G5 tube、G6 splice。真牆不動（φ 自治化/analytic 語意/邊際價值弱於 M33）。

## 2026-07-11 更新⑥：L3 戰役 Wave 1-2 — G5（M50）+ L3 φ 自治化主磚（M51）落地

**Wave 1 艦隊**（15 sonnet scouts、2.24M tokens；synths 撞限額、主控 inline 綜合）裁決：
G4d3=**SKIP**（多符號已泛化——δ 表 ℕ→ℕ→ℝ/任意 Q,K 自 M46 起免費；HasFDerivAt 存在性=ContDiff 兩行免費、
「ContDiff 不提供 HasFDerivAt」措辭過保守）；G5=ACHIEVABLE（已建 M50）；G4e=multi-round（★mathlib
`Turing.ListBlank` 就是現成 eventually-0 半帶、encTape 可下降；M25 點值橋已有、缺結構級等價；
cnotTM 需 stay 第三分支★）；G6=依賴 G4e（玩具家族=有限組態可判定死路；M16 splice 機制=funext+propext+
halting_problem 已盤點）；**L3 φ 自治化=ACHIEVABLE——修正「多月牆」誤判**（scout lean_run_code 全驗）。

**M50（G5）**：`digitsLt/wfCfg`+`encTape_le_headroom`（尾界 `(k−1)/(K−1)`）+`read_plateau_of_headroom`
（★plateau 假設 discharge★）+`gStepRL_wf`/`_iterate_wf`+`sigmaRL_exact_of_wf`+
**`sigmaRL_iterate_exact`（★N 步字面精確模擬★，條件於軌道兩堆疊非空）**。

**M51（L3 主磚）**：`φ₀` 邊界精確消沒（含 `φ₀_at_one` 單側極限）；**週期閘 `clockGate=φ₀∘fract`
C^∞（局部兩項和技巧、零商空間/無限和/FTC/MeasureTheory）**；**光滑階梯 `clockStair=smoothTransition∘fract+⌊·⌋`
= 閘的顯式反導數（`clockStair_hasDerivAt` 逐點）**；★L3 HEADLINE★ `autoSol_isSolution`：
`HasDerivAt (autoSol) (autoField (autoSol t)) t`、**`autoField(y,θ)=(−C·clockGate θ·(y−b),1)` 只依賴
狀態 = 真自治字面見證**、解顯式閉式（`targetingGatedSol` 餵階梯差）+ `autoField_contDiff`（場 C^∞）。

**剩（L3 完整版）**：M52 自治 leapfrog 對（`(y₁,y₂,θ)` 3D、period-2 閘給 HOLD、工作量≈M42）+ N 步
自治串接（M43 相位版）。誠實：M51 只清償單暫存器「非自治」caveat；不動 σ、禁宣稱 undecidability。

## 2026-07-11 更新⑦：L3 整合磚 M52 — 自治耦合 leapfrog 窗解

**M52（承 M51）**：`φ₀_at_zero`（0 邊界、`φ₀_at_one` 鏡像）；**period-2 閘** `clockGate2=φ₀(2·fract(θ/2))`
（活 `[2n,2n+1]`、**恰 0 於 `[2n+1,2n+2]` 全閉區間** `clockGate2_hold`，端點靠 `φ₀_at_zero/ge_one`）
+ C^∞（局部兩項和）+ **階梯** `clockStair2`（顯式反導數逐點 + HOLD 值凍結 `=n+1` 恰）；
**★自治耦合 leapfrog 場★** `leapField(y₁,y₂,θ)=(−C·gate2(θ)·(y₁−σ₁y₂), −C·gate2(θ−1)·(y₂−σ₂y₁), 1)`
（只依賴狀態、目標讀對方 live 值）；**★L3 整合 HEADLINE★** `leapWindow_isSolution`：A-窗 `[0,1]` 全閉
區間上凍結-`y₂` 顯式解真滿足耦合自治場（B-閘恰 0 ⟹ y₂ 分量吸收 = M42 write-protect 自治版）+
`leapField_contDiff`。誠實：同 M42「寫法耦合、動態解耦」；窗解非全域軌道（B-窗鏡像+N 窗串接=後續）；
σ₁ 只在凍結值取值。

**L3 戰役總結（M50-M52，一夜三磚）**：G5 tube 不變式（N 步精確模擬）+ L3 φ 自治化主磚（真自治
字面見證）+ L3 整合磚（自治耦合 leapfrog 窗解）。「φ 自治化=多月牆」誤判已修正。**L3 剩餘誠實
缺口**：B-窗鏡像、N 窗自治接力串接（M43 相位版）、自治 σ-耦合與 G4/G5 玩具 σ 的合體（把 leapField
的抽象 σ₁σ₂ 換 sigmaRL 分量+良編碼不變式）——皆組裝級。真牆不動：G4e 真機橋、analytic 語意、
邊際價值（弱於 M33 無條件）。

**（審查 cosmetic 補注）**「L3 φ 自治化=ACHIEVABLE」的精確範圍：M51/M52 交付**單暫存器自治 gated
targeting + 自治耦合 leapfrog 窗解**（時鐘自治化半邊、真自治字面見證）；**非**「L3 全部完成」——
B-窗鏡像/N 窗串接/自治場×玩具 σ 合體 = 組裝級後續；σ 具體化/undecidability 不在 L3 範圍。

## 2026-07-11 更新⑧：M53 合體 — 時鐘插進 CPU（自振盪流驅動真 sigmaRL、玩具晶片成形）

**M53（承 M52 純量自治 leapfrog + M48-50 玩具 σ）**：把 M52 抬到**向量**（兩個 ℝ³ 暫存器=兩份完整組態
編碼）+ 抽象 σ₁σ₂ 換**真** sigmaRL。5 定理(零 sorry、標準三公理):
- gtVec(向量 gated targeting=3 座標各一 targetingGatedSol)+gtVec_hasDerivAt(prodMk×3)+_start/_end。
- **cpuField σstep C(★自振盪 CPU 向量場★)**: (r₁,r₂,θ)↦(-C·gate2(θ)·(r₁-σstep r₂),
  -C·gate2(θ-1)·(r₂-σstep r₁), 1)——只依賴狀態、兩暫存器各讀對方跑 σstep、A/B 閘互補。
- **cpuWindow_isSolution(★HEADLINE★)**: A-窗 [0,1] 全閉區間凍結-r₂ 顯式解真滿足 cpuField(B-閘恰 0⟹r₂ 吸收)。
- cpuField_contDiff(σstep C^∞⟹場 C^∞、ℝ⁷ prodMk 組)。
- **cpuWindow_advances(★晶片跑一步★)**: σstep:=sigmaRL、r₂:=gEnc c(良編碼)⟹窗後 r₁=
  gEnc(gStepRL c)+(r₁₀-gEnc(gStepRL c))·e^{-C}——**一個自治時鐘週期把玩具組態推進一個 TM 步**(接 sigmaRL_exact_of_wf)。

**★關鍵誠實點★**: 連續流是 ε-近似(e^{-C} 殘差、exp 永不精確到達)、離散映射 sigmaRL 才字面精確;
橋 ε-流回精確需每步 re-rounding(sround/G3 施狀態暫存器)=Wall B 連續版、本磚不做(cpuWindow_advances
誠實顯示 e^{-C} 殘差)。玩具非真機(G4e)、窗解非全域軌道(B-窗鏡像+N 窗接力後續)、禁宣稱 undecidability。
**里程碑: 一顆被數學嚴格證明「零件+單步+時鐘自振+一個週期推進玩具程式一步」的半成品數學電腦。**
54 模組零 sorry 標準三公理。

## 2026-07-11 更新⑨：M54 — Wall B 連續版閉合（每步 re-round 清 e^{−C} 殘差 ⟹ 精確迭代流）

**M54（承 M53 ε-近似流 + M45 `sround` + M46 `sfloor`）**：閉合 M53 誠實缺口（連續流 `e^{−C}` 殘差）。
在每個時鐘邊緣把窗後值**重新量化**回精確格點 ⟹ 誤差**對所有 N 不累積**。兩條誠實路線（8 定理、零 sorry、標準三公理）:

**路線 A（`sround`、real-analytic、有界不歸零）**:
- `cleanStep`(flow-window+`sround`)+**`cleanStep_contract`**(一週期誤差 `× ρe^{−C}`、ρ=1−cos2πδ<1)。
- **`cleanTrack_bounded`(★A HEADLINE★)**: 移動整數目標軌道 tube 半徑 r 自洽(r+D≤δ、ρe^{−C}(r+D)≤r)
  ⟹ `∀n |yn−mn|≤r`(誤差對所有 N 有界不累積)。**代價=漸近、非字面歸零**(`e^{−C}>0` 恆有殘差)。

**路線 B（`sfloor` 置中量化、C^∞、literal-exact）**:
- `snapExact`(`sfloor` 平移 w/2 置中)+`snapExact_contDiff`+**`snapExact_exact`**(|y−m|≤w/2⟹=m 字面)。
- `exactStep`+**`exactStep_fix`**(殘差入 plateau 半寬⟹=m 字面、真 0 殘差)。
- **`exactTrack_zero`(★B HEADLINE★)**: 起點精確+有界跳幅+`e^{−C}D≤w/2`⟹ `∀n yn=mn` **字面相等**
  (誤差**恆等於 0**、對所有 N)=clocked/latched 數位流。**代價=C^∞ 非 analytic**。
- **`cpuWindow_state_latched`(★接 M53★)**: 真把 M53 窗後**狀態暫存器**(q-分量)用 `snapExact` latch
  =下個狀態 q' **字面**(殘差入半寬時)——「一個時鐘窗+邊緣 latch=精確推進狀態」(承 `cpuWindow_advances`)。

**★誠實★**: 是 clocked HYBRID(flow 窗+時鐘邊 latch 映射)、**非純自治 ODE**——latch=連續→離散再數位化所在
(正如真 flip-flop 比較器 plateau)；把 latch 嵌純流段撞「光滑流有限時間無法精確到達格點」牆(=真電路**為何**
要時鐘邊)。迭代(數位態序列)字面精確、底層連續流仍 ε-近似。只清**整數暫存器**(狀態 q+讀符;帶尾巴放大 Kⁱ
的全檔 tube=G5 下游)；狀態暫存器正是承載停機位元的關鍵。A(analytic)有界、B(C^∞)字面歸零=內稟取捨。仍玩具、
禁 undecidability。55 模組。
