# fluid_turing_lean — 流體動力學的圖靈完備性（Lean 4 形式化）

透過六模組翻譯鏈，把離散圖靈計算翻譯成連續流場，目標定理：
**Euler 穩態解（Beltrami 場）的動力學具備圖靈完備性**
（對應 Cardona–Miranda–Peralta-Salas–Presas 2021, PNAS 118(19), Theorem 1）。

- Lean `v4.32.0-rc1` + mathlib（pin 於 `lakefile.toml`）
- 建置：`lake build`（首次先 `lake exe cache get`）

## 成功定義（硬規則）

`lake build` 通過 ＋ 零 sorry ＋ 零自訂 axiom 才算完成；帶 sorry 的定理是鷹架不是結果。
每條 sorry 必須分類（`paper-blocked` / `可攻`），不得以自訂 axiom 或空證明掩蓋。
「不可證／為假」的判定不因後續壓力反轉。

## 六模組現況（v0.1，2026-07-04）

| 模組 | 檔案 | 內容 | sorry |
|---|---|---|---|
| M1 TTE 可計算分析 | `M1_Computability.lean` | `eml x y = exp x − log y`：連續性、雙向單調、`y→0⁺` 奇異點；TTE 快速柯西表示的存在與唯一 | 0 |
| M2 EML 語法樹與解釋器 | `M2_Interpreter.lean` | `EmlExpr` 語法樹 + 連續語意；`eml`/NAND 可表達；log-free 片段全域連續 | 0 |
| M3 康托爾編碼 | `M3_Encoding.lean` | `Encodable Γ ↪ ℝ`（`3⁻ⁿ`）單射；任意轉移函數共軛到 `ℝ` 上（`F ∘ enc = enc ∘ step`） | 0 |
| M4 懸掛構造 | `M4_Suspension.lean` | 映射環面 `(X×ℝ)/⟨(x,t+1)~(f x,t)⟩`；懸掛流群律、切片連續、時間-1 實現 `f` | 0 |
| M5 Reeb 介面層 | `M5_ReebInterface.lean` | 連續流結構（嚴格）＋抽象向量微積分簽名＋`IsBeltrami`；Etnyre–Ghrist 對應 | 1 ⛔ |
| M6 主定理 | `M6_EulerTuring.lean` | `Simulates` 謂詞；主定理（Euler-only）；已證的懸掛模擬配套 | 1 ⛔ |

## sorry 帳本（v0.1：共 2，全部 paper-blocked，零可攻）

| 宣告 | 分類 | 依賴 |
|---|---|---|
| `reeb_realizes_beltrami` (M5) | paper-blocked | Etnyre–Ghrist 2000 "Contact topology and hydrodynamics I" Thm 2.1；需要接觸幾何（mathlib 無） |
| `euler_flow_turing_complete` (M6) | paper-blocked | Cardona et al. 2021 Theorem 1；經 M5 對應 |

Axiom 檢查（`#print axioms`，2026-07-04）：18 條已證定理僅依賴
`[propext, Classical.choice, Quot.sound]`；上表兩條額外含 `sorryAx`；**零自訂 axiom**。

## M6 範圍決策（2026-07-04，使用者選定 B：Euler-only）

**明確不主張**「NS 黏滯免疫」（前身草案的斷言，已判定為假／超譯，永久移除）：

1. NS 黏滯耗散率是 `ν ∫ |∇u|² dV`，不是 `ν ∫ |Δu|²`；`Δ_H X = 0` 只給 closed + co-closed，不等於 `∇X = 0`。
2. Weitzenböck：`Δ_H = ∇*∇ + Ric`，「調和 ⟹ 平行」只在 Ricci-flat 流形成立。
3. Cardona et al. 2021 證的是 **Euler 穩態 + Beltrami**，非 NS（Beltrami 通常非 NS 穩態，`νΔu ≠ 0`）。

若未來要碰 NS，僅兩條合法路線（需重開範圍決策）：(A) 限制 Ricci-flat（平坦 T³）、(C) forced-NS。

## 誠實備註

- M3 的編碼像集每點孤立，「連續性」在其上不具內容；有內容的版本（康托爾集、
  generalized shift，Moore 1990）屬後續工作。
- M5 的 `VectorCalculus3` 是**運算元簽名**不是幾何：`curl`/`div` 未詮釋，
  任何用到它的定理都是「對所有滿足簽名的詮釋成立」。真詮釋等 mathlib 微分幾何。
