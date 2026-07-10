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
