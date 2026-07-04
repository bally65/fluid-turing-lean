# fluid_turing_lean — 流體動力學的圖靈完備性（Lean 4 形式化）

透過六模組翻譯鏈（+ M3b 離散端橋接模組），把離散圖靈計算翻譯成連續流場，目標定理：
**Euler 穩態解（Beltrami 場）的動力學具備圖靈完備性**
（對應 Cardona–Miranda–Peralta-Salas–Presas 2021, PNAS 118(19), Theorem 1）。

- Lean `v4.32.0-rc1` + mathlib（pin 於 `lakefile.toml`）
- 建置：`lake build`（首次先 `lake exe cache get`）

## 成功定義（硬規則）

`lake build` 通過 ＋ 零 sorry ＋ 零自訂 axiom 才算完成；帶 sorry 的定理是鷹架不是結果。
每條 sorry 必須分類（`paper-blocked` / `可攻`），不得以自訂 axiom 或空證明掩蓋。
「不可證／為假」的判定不因後續壓力反轉。

## 模組現況（v0.4，2026-07-04）

| 模組 | 檔案 | 內容 | sorry |
|---|---|---|---|
| M1 TTE 可計算分析 | `M1_Computability.lean` | `eml x y = exp x − log y`：連續性、雙向單調、`y→0⁺` 奇異點；TTE 快速柯西表示的存在與唯一 | 0 |
| M2 EML 語法樹與解釋器 | `M2_Interpreter.lean` | `EmlExpr` 語法樹 + 連續語意；`eml`/NAND 可表達；log-free 片段全域連續 | 0 |
| M3 康托爾編碼 | `M3_Encoding.lean` | `Encodable Γ ↪ ℝ` 單射 + 轉移共軛；**v0.2 真康托爾集升級**：`cantorEncode : (ℕ→Bool) → ℝ` 三進位編碼，單射（首異位論證）、連續（M-判別法）、閉嵌入、shift 動力學在康托爾集上的**連續**共軛；**v0.3 generalized shift（Moore 1990）**：`GenShift` 有限視窗局部規則結構（平移量 `F` 與改寫 `G` 都只依賴視窗、`G` 視窗外恆等）、乘積拓撲下連續（柱集上＝常數或座標投影）、**可逆 ⟹ 自同胚**（`toHomeomorph`，緊 Hausdorff 連續雙射的逆自動連續） | 0 |
| M3b 可逆 TM → GS | `M3b_ReversibleTM.lean` | **v0.4 定理鏈離散端**：`BitTM` 自足雙向無限帶圖靈機（moving-tape、狀態=滿位向量 `Fin m → Bool`，docstring 記錄對比 mathlib `TM0` 的取捨）；`encCfg` 組態空間 ≃ `(ℤ→Bool)` **顯式雙射**打包；`GenShift.ofLocal` 局部資料打包器；`toGenShift`：**機器單步在編碼下實現為 generalized shift**（視窗 `[-1,m]`）且 `step` 雙射 ⟹ `GenShift.Reversible`；`LocalReversible`：**局部可判定**（有限鋪磚檢查）的可逆充分條件 ⟹ 全域雙射；實例 `cnotTM`（受控反閘機，`decide` 驗證）。**里程碑 B（部分）**：Bennett 1973 history 構造 `bennett f`——單射 + n 步模擬已證；`bennett_not_surjective` 誠實記錄缺口（抽象構造不滿射，機器級 backward-complete 化=後續工作） | 0 |
| M4 懸掛構造 | `M4_Suspension.lean` | 映射環面 + 懸掛流群律/切片連續/時間-1 實現；**v0.2 可逆升級**：完整不變量 `(e^⌊t⌋x, fract t)`、`mk` 等價刻劃、切片嵌入單射、`X` 緊 ⟹ 環面緊、商投影是開映射、懸掛流**聯合連續**（開商映射法，免 Whitehead） | 0 |
| M5 Reeb 介面層 | `M5_ReebInterface.lean` | 連續流結構（嚴格）＋抽象向量微積分簽名＋`IsBeltrami`；Etnyre–Ghrist 對應 | 1 ⛔ |
| M6 主定理 | `M6_EulerTuring.lean` | `Simulates` 謂詞；主定理（Euler-only，paper-blocked）；**v0.2 下半層主定理（全證）**：`suspension_flow_simulates` — 緊空間上任何同胚都被緊空間上的連續 ℝ-流經單射編碼模擬；實例 `fullShift_suspension_simulates`（雙邊 full shift）；**v0.3 推論（全證）**：`genShift_suspension_simulates` — 任何**可逆 generalized shift** 被緊空間上連續 ℝ-流經單射編碼模擬；`fullShiftGS` = full shift 作為 GenShift 的平凡實例；**v0.4 推論（全證）**：`reversibleTM_suspension_simulates` — 任何**可逆位元圖靈機**的組態動力學被緊空間上連續 ℝ-流經單射編碼模擬；端到端實例 `cnotTM_suspension_simulates` | 1 ⛔ |

## sorry 帳本(v0.4：共 2，全部 paper-blocked，零可攻)

| 宣告 | 分類 | 依賴 |
|---|---|---|
| `reeb_realizes_beltrami` (M5) | paper-blocked | Etnyre–Ghrist 2000 "Contact topology and hydrodynamics I" Thm 2.1；需要接觸幾何（mathlib 無） |
| `euler_flow_turing_complete` (M6) | paper-blocked | Cardona et al. 2021 Theorem 1；經 M5 對應 |

Axiom 檢查（`#print axioms`，2026-07-04 v0.4）：全部已證定理（含 M3b 全部 +
M6 新推論兩條）僅依賴 `[propext, Classical.choice, Quot.sound]`
（`bennett_*` 三條甚至零公理）；上表兩條額外含 `sorryAx`；**零自訂 axiom**。
特別地 `suspension_flow_simulates` / `genShift_suspension_simulates` /
`reversibleTM_suspension_simulates` / `cnotTM_suspension_simulates`
**不依賴任何 sorry**。

## v0.4 的定理鏈意義

主定理 = 下半層（已全證）+ 幾何實現（paper-blocked）：

```
不可逆 TM ─(Bennett 1973 可逆化：構造+單射+n步模擬已證，
            雙射缺口誠實標示 bennett_not_surjective，後續工作)→ 可逆機器
可逆位元 TM（M3b BitTM，step 雙射；局部可判定條件 LocalReversible ⟹ 雙射）
  ─(M3b toGenShift + encCfg 雙射打包，已證)→ 可逆 generalized shift（Moore 1990）
  ─(M3 GenShift.toHomeomorph，已證)→ 緊空間 (ℤ→Bool) 上的自同胚
  ─(M4 懸掛 + M6 下半層定理，已證)→ 緊空間上的連續 ℝ-流、單射模擬
  ─(M5 Etnyre–Ghrist + Cardona Thm 1，paper-blocked)→ Euler 穩態 Beltrami 流
```

未證缺口收窄為：離散端只剩 **Bennett 可逆化的機器級雙射**
（history 構造的單射與模擬已證；抽象構造不滿射已證死、需機器級
backward-complete 化，非 paper-blocked），與連續端的接觸幾何詮釋層
（paper-blocked）。中段「**可逆 TM** → 可逆 GS → 同胚 → 流」已全證
（`reversibleTM_suspension_simulates`，端到端實例 `cnotTM`）。

## M6 範圍決策（2026-07-04，使用者選定 B：Euler-only）

**明確不主張**「NS 黏滯免疫」（前身草案的斷言，已判定為假／超譯，永久移除）：

1. NS 黏滯耗散率是 `ν ∫ |∇u|² dV`，不是 `ν ∫ |Δu|²`；`Δ_H X = 0` 只給 closed + co-closed，不等於 `∇X = 0`。
2. Weitzenböck：`Δ_H = ∇*∇ + Ric`，「調和 ⟹ 平行」只在 Ricci-flat 流形成立。
3. Cardona et al. 2021 證的是 **Euler 穩態 + Beltrami**，非 NS（Beltrami 通常非 NS 穩態，`νΔu ≠ 0`）。

若未來要碰 NS，僅兩條合法路線（需重開範圍決策）：(A) 限制 Ricci-flat（平坦 T³）、(C) forced-NS。

## 誠實備註

- M3 的 `encodeNat`（`3⁻ⁿ`）像集每點孤立，其上的連續性不具內容 —— v0.2 已補
  真康托爾集版本（`cantorEncode`，無孤立點，連續性是真命題）；v0.3 已補
  generalized shift 的**局部規則結構**（`GenShift`）並全證「可逆 ⟹ 同胚 ⟹ 被流模擬」；
  v0.4 已補「**可逆 TM ⟹ 可逆 GS**」（M3b），`GenShift.Reversible` 有了
  非平凡實例族（任何 `LocalReversible` 位元機，如 `cnotTM`）。
  剩餘後續工作：**不可逆** TM 的 Bennett 1973 可逆化 —— history 構造的
  單射與模擬已證，但其抽象形式不滿射（`bennett_not_surjective`），
  補成雙射需要機器級 backward-complete 化。
- M3b 的 `BitTM` 狀態空間取滿位向量（非任意有限型別），是為了讓組態編碼
  是雙射而非僅單射（可逆性才能整包搬到編碼側）；任意有限狀態機可補位嵌入，
  但該嵌入後的機器是否保持可逆，取決於補位轉移怎麼填 —— 這是使用此模型時
  要自己扛的義務，本 repo 不隱藏。
- M4 懸掛流的模擬用時間-1 映射；`Simulates` 只要求正時間實現一步轉移，
  未主張軌道分離性（expansivity）等更強動力學性質。
- M5 的 `VectorCalculus3` 是**運算元簽名**不是幾何：`curl`/`div` 未詮釋，
  任何用到它的定理都是「對所有滿足簽名的詮釋成立」。真詮釋等 mathlib 微分幾何。
