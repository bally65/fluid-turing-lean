# 不可判定線（M9–M15）——地圖 + (ii) 緊空間實現 KICKOFF 規格

> 2026-07-09。本線起點 = 使用者洞見「一個積分、一個微分」（軌道可達性 = 積分/全域側；
> blowup = 微分/局部側）。經 deep-research 扎根文獻（Graça 2009 / Huynh 2024 / Tao 綱領）
> 後逐塊機器化。全部零 sorry、標準三公理，`scripts/check.sh` 驗。

## 現況地圖（全部已證）

| 模組 | 內容 | 狀態 |
|---|---|---|
| M9 | `halts_imp_orbitReaches`：停機 ⟹ 流軌道可達（積分側） | ✅ |
| M10 | `finite_time_blowup_undecidable`：blowup⟺halts ⟹ 爆破偵測不可判定（還原） | ✅ |
| M11 | `blowupSol`：顯式 `y'=y²` 有限時間爆破原子 | ✅ |
| M12 | `halts_imp_hybrid_blowup`：停機觸發爆破橋（混成） | ✅ |
| M13 | `halts_imp_smooth_blowup`：光滑化開關（`smoothTransition`、C^∞、消混成 caveat） | ✅ |
| M14 | `orbitReaches_iff_halts`＋`coupled_blowup_undecidable`（閉環）＋`suspension_flow_simulates_faithful`（**忠實性=定理**） | ✅ |
| M15 | `stepT_halts_iff_code_eval_dom`＋`univ_wiring`＋**`stepT_halting_undecidable`（無條件機器層不可判定）** | ✅ |

**假設帳本**：① OrbitFaithful = 定理（懸掛幾何）✅；② huniv 機器側+通用碼 (i) = 定理 ✅。
**唯一剩餘 = (ii)**：mathlib 機器（`ToPartrec` 家族）的**緊空間同胚實現**。接上後
`coupled_blowup_undecidable` 變**無條件**的「流家族爆破觸發不可判定」。

## (ii) KICKOFF 規格（下 session / 專門立項照此執行）

### 目標

把 M15 的不可判定機器接進本專案的緊化管線（M3 康托爾編碼 + M3c Bennett + M4 懸掛），
得最終定理：**「懸掛流家族的爆破觸發（= OrbitReaches 編碼停機區）無演算法可判定」——
無條件**（僅標準三公理）。

### 路線判定（先想清楚、勿直接 generic Bennett）

- **❌ 路線 B（generic Bennett on `Option Cfg`）不通**：`ToPartrec.step` 每步可丟
  **無界**資訊（丟整個 continuation frame），M3c Feistel `bufferedStep` 靠**有界**
  丟失記錄（BitTM 每步丟 (舊態,舊位) 有界）——generic 版縮不進固定緩衝。此即當初
  C4b 無界牆的近親，勿重蹈。
- **✅ 路線 A（經 mathlib TM2）**：mathlib `Turing.PartrecToTM2.tr_eval` 已證
  **TM2 機器模擬 `ToPartrec.Code`**（`eval (TM2.step tr) (init c v) = halt <$> c.eval v`）。
  TM2 = 有限狀態 + 有限字母堆疊、**每步丟失有界**（只碰堆疊頂）→ Bennett 適用、
  BitTM 編譯可行。且只需編譯**這一台固定機器 `tr`**（非 generic TM2→BitTM）。

### 有序 bricks

1. **B1 — TM2 停機介面**（day-1、小）：對 `TM2.step tr` 鏡射 M15 模式（全化 stepT'、
   `StateTransition.mem_eval`、`tr_eval` 接 `Code.eval`）。M15 的證明骨架逐字可搬。
2. **B2 — `tr` 的 BitTM 編譯（核心、多 session）**：TM2 組態（有限態 × K 個有限字母
   堆疊）編碼進 BitTM 位帶（態 ↪ 狀態位向量、堆疊 ↪ 帶區交錯）；一 TM2 步 = BitTM
   **有界宏步**（讀寫堆疊頂 = 走位到區標記 + 有界位操作）。**方案 C 的機器直接復用**：
   `trackWalkTM`/`trackWalkTM_reaches_marker`（走位到唯一標記於資料相依距離、已證）、
   控制表機器 `ctrlEquivOfInverse`+decide、`phaseDispatch`/`prodShear`。目標陳述：
   `∃ M : BitTM, ∃ encB, ∀ cfg, ∃ n ≥ 1, M.step^[n] (encB cfg) = encB (TM2 一步)` +
   停機組態為 fixpoint。**先撒對抗設計艦隊驗佈局**（方案 C 教訓：驗牆再建）。
3. **B3 — Bennett + 忠實懸掛**：編譯後 BitTM 餵 M3c（`bennettHomeo` 緊空間同胚）→
   M14 `suspension_flow_simulates_faithful`。查核點：停機集在 Bennett 化後仍**吸收**
   （機器分量固定、歷史照走 → H := {機器分量 ∈ 停機態} 吸收 ✓ 設計上成立、要證）。
4. **B4 — 終定理 splice**：`coupled_blowup_undecidable` 餵 B1∘B2 傳輸的 huniv +
   忠實懸掛 → **★流家族爆破觸發不可判定（無條件）★**。

### 風險/提醒

- B2 是唯一大核。TM2 每步有界丟失 = Bennett 前提 ✓；堆疊頂存取距離資料相依 =
  方案 C 走位機器的正戲（synergy：C-δ 的可達性歸納正是為此練的）。
- 宏步「∃n 變長」在 `Simulates`/`Simulates.iterate` 語意下天然容納（M9 已用）。
- 每塊 `scripts/check.sh` 收尾守硬規則（零 sorry + 標準三公理）。
- 誠實界線持續：本線的「流」是懸掛流（緊空間連續 ℝ-流）；接真 Euler/NS 幾何仍走
  M5/M7 的明寫假設（paper-blocked、與本線正交）。
