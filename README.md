# fluid_turing_lean — 流體動力學的圖靈完備性（Lean 4 形式化）

透過六模組翻譯鏈（+ M3b/M3c 離散端橋接模組），把離散圖靈計算翻譯成連續流場，目標定理：
**Euler 穩態解（Beltrami 場）的動力學具備圖靈完備性**
（對應 Cardona–Miranda–Peralta-Salas–Presas 2021, PNAS 118(19), Theorem 1）。

- Lean `v4.32.0-rc1` + mathlib（pin 於 `lakefile.toml`）
- 建置：`lake build`（首次先 `lake exe cache get`）

## 成功定義（硬規則）

`lake build` 通過 ＋ 零 sorry ＋ 零自訂 axiom 才算完成；帶 sorry 的定理是鷹架不是結果。
每條 sorry 必須分類（`paper-blocked` / `可攻`），不得以自訂 axiom 或空證明掩蓋。
「不可證／為假」的判定不因後續壓力反轉。

## 模組現況（v0.5，2026-07-04）

| 模組 | 檔案 | 內容 | sorry |
|---|---|---|---|
| M1 TTE 可計算分析 | `M1_Computability.lean` | `eml x y = exp x − log y`：連續性、雙向單調、`y→0⁺` 奇異點；TTE 快速柯西表示的存在與唯一 | 0 |
| M2 EML 語法樹與解釋器 | `M2_Interpreter.lean` | `EmlExpr` 語法樹 + 連續語意；`eml`/NAND 可表達；log-free 片段全域連續 | 0 |
| M3 康托爾編碼 | `M3_Encoding.lean` | `Encodable Γ ↪ ℝ` 單射 + 轉移共軛；**v0.2 真康托爾集升級**：`cantorEncode : (ℕ→Bool) → ℝ` 三進位編碼，單射（首異位論證）、連續（M-判別法）、閉嵌入、shift 動力學在康托爾集上的**連續**共軛；**v0.3 generalized shift（Moore 1990）**：`GenShift` 有限視窗局部規則結構（平移量 `F` 與改寫 `G` 都只依賴視窗、`G` 視窗外恆等）、乘積拓撲下連續（柱集上＝常數或座標投影）、**可逆 ⟹ 自同胚**（`toHomeomorph`，緊 Hausdorff 連續雙射的逆自動連續） | 0 |
| M3b 可逆 TM → GS | `M3b_ReversibleTM.lean` | **v0.4 定理鏈離散端**：`BitTM` 自足雙向無限帶圖靈機（moving-tape、狀態=滿位向量 `Fin m → Bool`，docstring 記錄對比 mathlib `TM0` 的取捨）；`encCfg` 組態空間 ≃ `(ℤ→Bool)` **顯式雙射**打包；`GenShift.ofLocal` 局部資料打包器；`toGenShift`：**機器單步在編碼下實現為 generalized shift**（視窗 `[-1,m]`）且 `step` 雙射 ⟹ `GenShift.Reversible`；`LocalReversible`：**局部可判定**（有限鋪磚檢查）的可逆充分條件 ⟹ 全域雙射；實例 `cnotTM`（受控反閘機，`decide` 驗證）；**v0.5 `ofPerm` 置換機引擎**：局部更新 `(q,a)↦(next,write)` 是置換且 `move` 只依賴新狀態 ⟹ `LocalReversible`（參數化鋪磚證明，機器級可逆化的可逆性引擎）。**里程碑 B（部分）**：Bennett 1973 history 構造 `bennett f`——單射 + n 步模擬已證；`bennett_not_surjective` 誠實記錄缺口（抽象構造不滿射；動力學層已由 M3c 封死，機器級=後續工作） | 0 |
| M3c Bennett 可逆化 | `M3c_Bennett.lean` | **v0.5 動力學層 Bennett（全證）**：`histConveyor` —— `X × V` 上任意雙射升級成 `X × (ℤ→V)` 上雙射（歷史輸送帶：讀流位 0 當緩衝、記錄從 -1 吐出、整流下移；雙向無限流無「空歷史」角點，滿射由顯式逆映射成立）；`BitTM.bufferedStep` **Feistel 帶緩衝單步**——任意（不可逆）位元機單步配一格緩衝成顯式雙射（新狀態=`next⊕r`、寫入位=`write⊕b`、緩衝吐出被丟棄的 `(q,t 0)`），空白緩衝上精確=`M.step`；`bennettAut`+`bennettAut_iterate`：n 步 conveyor = n 步機器（**無時間膨脹**）、垃圾誠實外顯；`bennettHomeo`：緊 Hausdorff 上正向連續（每輸出座標只讀有限離散資料+至多三帶座標）⟹ 自同胚 | 0 |
| M3d 機器級 Bennett | `M3d_BennettTM.lean` | **milestone A（構造 + 可逆性，全證）**：`bennettTM : BitTM → BitTM` —— 狀態打包 `m' = m + (m+1) + 3`（M-狀態 × HistRec 緩衝 × 3 相位位，顯式 `Equiv` 鏈 `bitsSplit`/`bufSplit`/`shuttleUnpack`）；微步原語全是逐段驗證的置換（`feistelCore` = M3c `bufferedStep` 狀態側 Feistel 輪、`swapHead` 對合、`rotBuf` 循環旋轉、`phaseInc` 3 位遞增、`phaseDispatch` = `prodShear` 相位纖維分派）；`L = shuttleL` 打包共軛複合、`μ = shuttleDir` 只讀新狀態相位位（`ofPerm` 紀律）；`bennettTM_reversible` 由 `ofPerm_reversible` 免費。**只主張構造 + 可逆**；模擬語意（乾淨組態不變量、宏步引理）= milestone B/C，占位相位排程屆時換標記驅動可逆分支，可逆性定理與排程無關。待決清單成文於檔頭 docstring | 0 |
| M4 懸掛構造 | `M4_Suspension.lean` | 映射環面 + 懸掛流群律/切片連續/時間-1 實現；**v0.2 可逆升級**：完整不變量 `(e^⌊t⌋x, fract t)`、`mk` 等價刻劃、切片嵌入單射、`X` 緊 ⟹ 環面緊、商投影是開映射、懸掛流**聯合連續**（開商映射法，免 Whitehead） | 0 |
| M5 Reeb 介面層 | `M5_ReebInterface.lean` | 連續流結構（嚴格）＋抽象向量微積分簽名＋`IsBeltrami`；Etnyre–Ghrist 對應 | 1 ⛔ |
| M6 主定理 | `M6_EulerTuring.lean` | `Simulates` 謂詞；主定理（Euler-only，paper-blocked）；**v0.2 下半層主定理（全證）**：`suspension_flow_simulates` — 緊空間上任何同胚都被緊空間上的連續 ℝ-流經單射編碼模擬；實例 `fullShift_suspension_simulates`（雙邊 full shift）；**v0.3 推論（全證）**：`genShift_suspension_simulates` — 任何**可逆 generalized shift** 被緊空間上連續 ℝ-流經單射編碼模擬；`fullShiftGS` = full shift 作為 GenShift 的平凡實例；**v0.4 推論（全證）**：`reversibleTM_suspension_simulates` — 任何**可逆位元圖靈機**的組態動力學被緊空間上連續 ℝ-流經單射編碼模擬；端到端實例 `cnotTM_suspension_simulates`；**v0.5 推論（全證）**：`bitTM_suspension_simulates` — **任意（不可逆）位元機**經 Bennett 歷史編碼被緊空間上連續 ℝ-流模擬（可逆性假設拿掉；歷史分量與落點垃圾誠實外顯為存在量詞） | 1 ⛔ |

## sorry 帳本(v0.5：共 2，全部 paper-blocked，零可攻)

| 宣告 | 分類 | 依賴 |
|---|---|---|
| `reeb_realizes_beltrami` (M5) | paper-blocked | Etnyre–Ghrist 2000 "Contact topology and hydrodynamics I" Thm 2.1；需要接觸幾何（mathlib 無） |
| `euler_flow_turing_complete` (M6) | paper-blocked | Cardona et al. 2021 Theorem 1；經 M5 對應 |

Axiom 檢查（`#print axioms`，2026-07-04 v0.5）：全部已證定理（含 M3b `ofPerm`、
M3c 全部、M6 `bitTM_suspension_simulates`）僅依賴
`[propext, Classical.choice, Quot.sound]`；上表兩條額外含 `sorryAx`；
**零自訂 axiom**。特別地 `suspension_flow_simulates` /
`genShift_suspension_simulates` / `reversibleTM_suspension_simulates` /
`cnotTM_suspension_simulates` / `bitTM_suspension_simulates`
**不依賴任何 sorry**（v0.5 迴歸抽查通過）。

## v0.5 的定理鏈意義

主定理 = 下半層（已全證）+ 幾何實現（paper-blocked）：

```
任意（不可逆）位元 TM（M3b BitTM）
  ─(M3c bufferedStep：Feistel 帶緩衝單步，已證)→ Cfg × 記錄 上的雙射
  ─(M3c histConveyor：歷史輸送帶，已證)→ Cfg × 歷史流 上的雙射
  ─(M3c bennettHomeo：緊 Hausdorff + 正向連續，已證)→ 緊空間自同胚
  ─(M4 懸掛 + M6 下半層定理，已證)→ 緊空間上的連續 ℝ-流、單射模擬
      （M6 bitTM_suspension_simulates：可逆性假設已拿掉、垃圾誠實外顯）
  ─(M5 Etnyre–Ghrist + Cardona Thm 1，paper-blocked)→ Euler 穩態 Beltrami 流

平行支線（可逆機器，無歷史負擔）：
可逆位元 TM（step 雙射；LocalReversible 鋪磚 ⟹ 雙射；ofPerm 置換機引擎）
  ─(M3b toGenShift + encCfg，已證)→ 可逆 generalized shift（Moore 1990）
  ─(M3 toHomeomorph，已證)→ (ℤ→Bool) 自同胚 ─(M4+M6，已證)→ 連續流
```

離散端的 Bennett 缺口已在**動力學層**全部封死（`bennett_not_surjective`
指出的滿射障礙由 M3c 的雙向無限歷史流繞開；模擬無時間膨脹）。
未證缺口收窄為：連續端的接觸幾何詮釋層（paper-blocked），以及
（非阻斷、錦上添花的）字面機器級 `bennettTM : BitTM → BitTM`，見下節。

## 後續工作：機器級 shuttle Bennett（非阻斷）

把 M3c 的動力學層構造下沉為字面的 `bennettTM : BitTM → BitTM`
（歷史寫進帶本身），攻擊計畫（2026-07-04 評估；**milestone A 已於 M3d 落袋**）：

1. ~~**可逆性免費**：機器以 `ofPerm`（M3b）形式給出 —— 只需設計局部更新置換
   `L : (狀態×位元) ≃ (狀態×位元)` 與方向表 `μ`，`LocalReversible` 一次付清。~~
   **✅ 完成（M3d milestone A）**：`bennettTM := ofPerm shuttleBits shuttleL
   shuttleDir`，`bennettTM_reversible` 全證、只依賴標準三公理。
2. ~~**帶佈局**（狀態側）~~ **✅ 狀態打包完成**：M-狀態 × `m+1` 位緩衝 ×
   3 相位位（**設計修訂**：無獨立程式/相位計數器暫存器 —— 掃描以帶上標記
   終止、緩衝走位用循環旋轉，計數器不進狀態）。帶側 4-軌區塊
   （工作位、垃圾資料位、垃圾標記位、home 標記位）**未實作**——
   進 milestone B 的乾淨組態謂詞。
3. ~~**微步設計全用置換原語**~~ **✅ 原語庫完成**：`feistelCore`（Feistel 輪）、
   `swapHead`（swap 對合）、`rotBuf`、`phaseInc`、`phaseDispatch`
   （`prodShear` 相位纖維分派）—— 逐段 `Equiv` 驗證。**占位排程**
   （相位 0 = Feistel、1 = 垃圾走位、餘恆等）待 milestone C 換成
   標記驅動可逆分支；可逆性定理與排程無關。
4. **垃圾堆疊拖曳**（milestone B，未動）：歷史堆疊保持與 home 相鄰
   （標記連續區段），頭移動時旋轉堆疊一格（撿底放頂；垃圾內容順序無關）；
   所有掃描以標記邊界終止，無無界搜尋失敗模式。堆疊區不變量：
   未標記格=0（撿起時歸零維持）。乾淨組態謂詞 + 每類微步保不變量引理。
5. **模擬引理**（milestone C，未動；風險集中）：每 M-步耗 O(堆疊長) 微步
   （`∃ n` 陳述容納變長排程，配 M6 `Simulates.iterate` 語意）；
   正確性歸納 = 相位×區段不變量。爆量時先證單一相位段部分引理。
   Lean 工程量估 1500+ 行。設計待決 7 條成文於 M3d 檔頭 docstring。

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
  非平凡實例族（任何 `LocalReversible` 位元機，如 `cnotTM`）；
  v0.5 已補**不可逆** TM 的 Bennett 可逆化（M3c，動力學層全證：
  `bennett_not_surjective` 的滿射障礙由雙向無限歷史流繞開）。
- M3c/M6 v0.5 的 `bitTM_suspension_simulates` 陳述裡，編碼域帶歷史分量、
  第 n 步落點的歷史內容是存在量詞 —— 這是 Bennett 構造的本質代價
  （垃圾），不是證明偷懶；工作分量由 `enc` 單射唯一讀出。其產物是
  緊空間自同胚而**非** generalized shift（雙軌不同平移量超出單一有限視窗
  局部規則），故此支線走 M4 懸掛直達流、不經 M3 的 GS 層。
- M3b 的 `BitTM` 狀態空間取滿位向量（非任意有限型別），是為了讓組態編碼
  是雙射而非僅單射（可逆性才能整包搬到編碼側）；任意有限狀態機可補位嵌入，
  但該嵌入後的機器是否保持可逆，取決於補位轉移怎麼填 —— 這是使用此模型時
  要自己扛的義務，本 repo 不隱藏。
- M4 懸掛流的模擬用時間-1 映射；`Simulates` 只要求正時間實現一步轉移，
  未主張軌道分離性（expansivity）等更強動力學性質。
- **主定理陳述層待審（v0.5 驗收時記錄）**：`euler_flow_turing_complete` 對
  **任意**（可合流）`step` 主張嚴格 `Simulates`（單射 `enc`、每步精確落點）。
  流的時刻映射可逆 ⟹ 合流組態被迫線性化進同一軌道 —— 語意上未必矛盾
  （各組態時刻不同），但 Cardona 原文走的是雙射 generalized shift，
  未對合流 step 主張此形式。未來消該 paper-blocked sorry 時，應同步檢視
  主定理是否收斂為「可逆 step」版本、或改用 M3c 的垃圾外顯語意 ——
  屆時屬範圍決策，需使用者拍板，不得靜默放寬或收緊。
- M5 的 `VectorCalculus3` 是**運算元簽名**不是幾何：`curl`/`div` 未詮釋，
  任何用到它的定理都是「對所有滿足簽名的詮釋成立」。真詮釋等 mathlib 微分幾何。
