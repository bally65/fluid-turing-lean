# Brick 6 決策文件 — 條件式 undecidability 轉移：GENUINE / THIN / HONEST_STOP

> 2026-07-10。線三（analog computation）Brick 1–5 已收（M39–M43，全零 sorry、標準三公理、已 push）。
> 本文用**主控自身推理**（對抗 scope workflow 撞 Anthropic 額度未完成）誠實裁決 Brick 6 該是什麼、或該不該有。
> **最高原則 = 誠實：寧可 HONEST_STOP，也不交 thin/circular 的假 brick。**

---

## 0. 問題

線三想造「光滑 ODE 流，其到達性不可判定」，作法 = 流逐步模擬 TM。Brick 1–5 建好了**動力學 scaffold**
（steer→gate/HOLD→具體窗→leapfrog 半步→N 步斷點軌道 + 條件式誤差界），**全部 σ 抽象、非自治、條件式**。
Brick 6 的候選 = **把 `leapfrogOrbit` 連到真 undecidability**（條件式轉移）。本文問：這一步是 genuine、
還是 thin/circular、還是撞牆（paper-blocked）？

---

## 1. 一個「genuine 轉移鏈」需要什麼（理想版）

| 步 | 內容 | 狀態 |
|---|---|---|
| 1 | TM 停機不可判定 | ✅ 已證資產（mathlib `ComputablePred.halting_problem`、專案 M16/M30） |
| 2 | `enc : Config→ℝ`、`dec : ℝ→Config`；`σ : ℝ→ℝ` 於編碼上**精確**實現一步：`σ(enc c) = enc(step c)` | 假設 |
| 3 | `σ^[n](enc c₀) = enc(configₙ)`（理想軌道 = 編碼的 TM 軌跡） | 由步 2 迭代、**真證** |
| 4 | Brick 5 `tracks_ideal`：`\|xₙ − σ^[n](enc c₀)\| ≤ M·e^{−C}·ΣLⁱ =: εₙ` | ✅ 已證（M43，條件於 σ Lipschitz + 步殘差 ≤ M） |
| 5 | `dec` 穩健：編碼 `ρ`-分離、`dec` 就近取整 ⟹ `\|x − enc c\| < ρ → dec x = c` | 假設 |
| 6 | **tube 不變式**：`εₙ < ρ` ⟹ `dec xₙ = configₙ` | 由步 4+5 **推導**（非假設！） |
| 7 | `dec xₙ = halt ⟺ configₙ = halt ⟺ TM 於 n 步停機` ⟹ analog 軌道的 halt-decode 到達性**不可判定** | 由步 6 + 步 1 |

**關鍵**：步 6 的 tube 不變式若是**推導**（非假設），整條轉移就**非 circular、genuine**（步 3–7 = 真正的
Graça 誤差分析）。若步 6 是**假設**，就 thin（見 §2）。

---

## 2. 三堵牆（為何 genuine 版撞 paper-block）

### Wall A — 真 TM `σ` 是不連續 round map，無 Lipschitz 常數
`tracks_ideal` 要 `σ` 在 tube 上 Lipschitz（H1）。但真 `σ = decode→step→encode` 作為 `ℝ→ℝ` 必須定義在
**所有**實數上（ODE 流經所有值），而在判定邊界（round 跳點）`σ` **本質不連續** ⟹ 無 Lipschitz 常數。
Graça 的解 = 造一個**光滑** `σ`，於編碼格點上 = TM step、於格點**tube** 上 Lipschitz，並證軌道**恆留 tube**。
造這個光滑 `σ` = GPAC 構造 = **mathlib 從零、多月、paper-blocked**。

### Wall B — 誤差累積 / tube-staying 對一般（擴張）TM 失效
`tracks_ideal` 給 `εₙ ≤ M·e^{−C}·ΣLⁱ`。一般 TM 的有效 `σ` 是**擴張**（`L ≥ 1`）⟹ `ΣLⁱ` 隨 n 增長 ⟹
`εₙ` 終將超過 `ρ` ⟹ tube 不變式（步 6）對大 n **失效**。修法 = 要嘛 `L < 1`（非一般 TM），要嘛**每步
re-rounding**（`dec` 後 re-`enc` 把 `xₙ` 拉回精確格點、殺掉累積誤差）。re-rounding 本身是一個必須焊進 `σ`
的光滑操作（GPAC 構造的一部分） = **paper-blocked**。無它，一般 TM 的 tube 不變式無法對所有 n 成立。

### Wall C — `σ` 同時滿足「光滑 ∧ 格點=step ∧ tube-Lipschitz ∧ 向格點收縮」
Graça/Branicky 用光滑插值 + round 以 sigmoid 光滑逼近來造。**mathlib 完全沒有這套**。= paper-blocked 核心。

---

## 3. 三個子裁決

### (A) 若 Brick 6 把 tube 不變式 `dec xₙ = configₙ` 當**假設** → **THIN / circular，AVOID**
則轉移 = 「`dec xₙ = configₙ`（假設）+ TM 停機不可判定 → analog halt-decode 不可判定」，**假設做了全部
模擬工作**。這正是 fluent-but-thin、違硬規則。**不交。**

### (B) 若 Brick 6 從 {tracks_ideal + H_σ 精確 + dec ρ-robust + εₙ<ρ} **推導** tube 不變式 → **GENUINE，但假設不可為真 TM 實例化**
轉移非 circular（步 3–7 是真推導）。但假設 bundle{光滑 σ、tube-Lipschitz、re-rounding} **對真 TM 的不連續
round map 不可實例化**（Wall A/B/C）。= 一條**條件式**定理，方法學同**方案 A**（M33 的幾何依賴明寫假設）。
價值 = **精確定位 paper-blocked 前沿**（誰若造出 GPAC `σ`，即得 undecidability）。**但**：真誠實版需 `L<1`
或 re-rounding 控誤差（Wall B），且下一項（C）指出它與主線重複。

### (C) 與主線 M33 **重複**、邊際價值低
主線 `fluid_blowup_undecidable`（M33）**已無條件**證「緊空間懸掛流到達性不可判定」——經**另一條已完成**的
路線（mathlib TM 化約鏈 + 自建 BitTM + Bennett + 懸掛流）。故專案**已擁有**「特定流 → 到達性不可判定」的
**無條件**結果。Brick 6 的條件式 analog-flow 版 = **更弱**（條件式）**且經更難**（paper-blocked）的路線。
其唯一增量 = (i) 真·**光滑** ODE 向量場（M33 是拓撲懸掛流、非光滑 ODE 場）、(ii) 定位 GPAC 前沿。

---

## 4. 裁決：**HONEST_STOP 於 Brick 5**（+ 選配的前沿定位條件式草圖，不建）

**線三的誠實天花板 = Brick 5。** 理由：

1. **真酬勞**（光滑 analog 流到達性不可判定）需 paper-blocked 的 GPAC `σ`（Wall A/B/C = 不連續 round 的光滑化
   + tube 不變式 + re-rounding）= mathlib 從零、多月。
2. **條件式版**可達但：(a) thin 風險高（假設易做掉全部工作）；(b) 嚴格**弱於已完成的 M33 無條件結果**；
   (c) 誠實誤差控制（Wall B）逼你選 `L<1`（非一般 TM）或 re-rounding（paper-blocked）。
3. Bricks 1–5 已交付**真·可重用、誠實的 analog-computation ODE 原子鏈**（steer/gate/HOLD/窗/leapfrog/N 步 +
   條件式誤差界）——這本身是紮實成果。undecidability 轉移正撞線三**自始明標**的那堵牆：σ 具體化（不連續
   round）+ tube 不變式 = paper-blocked。

**不建 Brick 6 假磚。** genuine 版 = paper-blocked；thin 版違規；條件式版與 M33 重複且風險高。

---

## 5. 若日後要「前沿定位條件式草圖」（選配、非現在、明框為「定位前沿」非「達成」）

可誠實陳述（方案 A 式，**清楚標非可為真 TM 實例化**）：

```
-- 假設 bundle（全部 paper-blocked 的 GPAC 零件明寫成假設）：
--   (H_enc) enc : Config → ℝ, dec : ℝ → Config, ρ-分離 + dec 就近
--   (H_σ)   ∀ c, σ (enc c) = enc (step c)                    -- σ 於格點精確 = TM step
--   (H_lip) ∀ x y ∈ tube, |σ x − σ y| ≤ L * |x − y|          -- tube-Lipschitz（真 TM 不可實例化）
--   (H_ctl) ∀ n, εₙ < ρ                                       -- 誤差恆小於分離半徑（需 L<1 或 re-rounding）
-- 結論（genuine 推導、非假設 tube）：
--   ∀ n, dec (leapfrogOrbit σ (enc c₀) C n) = (step^[n] c₀)   -- tube 不變式（推導自 Brick 5 tracks_ideal）
--   ⟹ ¬ ComputablePred (fun code => ∃ n, dec (xₙ code) = halt)  -- 轉移自 TM 停機不可判定
```

**此草圖的誠實定位**：它**不**證出 undecidability（假設 H_lip/H_ctl 對真 TM 不可實例化），只**精確標出**：
「補上 GPAC `σ` 的四個性質，Brick 5 的軌道即 decode 成 TM 計算、到達性即不可判定」。價值 = 前沿地圖，
**非**新的無條件結果（那已由 M33 給）。**除非**使用者明確要這張前沿地圖，否則不值得建（與 M33 重複 + thin 風險）。

---

## 6. 什麼能真正 unblock

單一 mathlib-from-zero 工程：**Graça/Branicky 的 GPAC `σ` 構造**——把 round:ℝ→ℤ 以 `expNegInvGlue`/
`smoothTransition` 型光滑 sigmoid 逼近、造出「光滑 ∧ 格點=step ∧ tube-Lipschitz ∧ 向格點收縮（re-rounding）」
的 `σ:ℝ→ℝ`，並證 tube 不變式。多月、需大量新分析引理（誤差傳播、tube 幾何、光滑 round 的顯式界）。
做出它 → Brick 6 (B) 版的假設全可實例化 → 線三得**真·光滑 analog 流到達性不可判定**（超越 M33 的拓撲懸掛流）。

---

## 7. 一句話結論

> **線三收在 Brick 5。** Bricks 1–5 = 誠實可重用的 analog-computation ODE 原子鏈；Brick 6 的 genuine 轉移
> 撞 GPAC `σ` 光滑化 paper-block（Wall A/B/C），thin 版違規，條件式版與已完成的 M33 無條件結果重複。
> 不建假磚。真 undecidability 已由**主線 M33 無條件**達成（另一條完成的路線）。
