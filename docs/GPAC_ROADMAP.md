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
