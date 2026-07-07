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

## 模組現況（2026-07-08；M3d 里程碑 C 大幅推進）

> M3d 里程碑 C 的完整設計日誌與逐步進度見 [`docs/M3D_C_DECOMPOSITION_PLAN.md`](docs/M3D_C_DECOMPOSITION_PLAN.md)。
> 下表 M3d 欄為摘要。

| 模組 | 檔案 | 內容 | sorry |
|---|---|---|---|
| M1 TTE 可計算分析 | `M1_Computability.lean` | `eml x y = exp x − log y`：連續性、雙向單調、`y→0⁺` 奇異點；TTE 快速柯西表示的存在與唯一 | 0 |
| M2 EML 語法樹與解釋器 | `M2_Interpreter.lean` | `EmlExpr` 語法樹 + 連續語意；`eml`/NAND 可表達；log-free 片段全域連續 | 0 |
| M3 康托爾編碼 | `M3_Encoding.lean` | `Encodable Γ ↪ ℝ` 單射 + 轉移共軛；**v0.2 真康托爾集升級**：`cantorEncode : (ℕ→Bool) → ℝ` 三進位編碼，單射（首異位論證）、連續（M-判別法）、閉嵌入、shift 動力學在康托爾集上的**連續**共軛；**v0.3 generalized shift（Moore 1990）**：`GenShift` 有限視窗局部規則結構（平移量 `F` 與改寫 `G` 都只依賴視窗、`G` 視窗外恆等）、乘積拓撲下連續（柱集上＝常數或座標投影）、**可逆 ⟹ 自同胚**（`toHomeomorph`，緊 Hausdorff 連續雙射的逆自動連續） | 0 |
| M3b 可逆 TM → GS | `M3b_ReversibleTM.lean` | **v0.4 定理鏈離散端**：`BitTM` 自足雙向無限帶圖靈機（moving-tape、狀態=滿位向量 `Fin m → Bool`，docstring 記錄對比 mathlib `TM0` 的取捨）；`encCfg` 組態空間 ≃ `(ℤ→Bool)` **顯式雙射**打包；`GenShift.ofLocal` 局部資料打包器；`toGenShift`：**機器單步在編碼下實現為 generalized shift**（視窗 `[-1,m]`）且 `step` 雙射 ⟹ `GenShift.Reversible`；`LocalReversible`：**局部可判定**（有限鋪磚檢查）的可逆充分條件 ⟹ 全域雙射；實例 `cnotTM`（受控反閘機，`decide` 驗證）；**v0.5 `ofPerm` 置換機引擎**：局部更新 `(q,a)↦(next,write)` 是置換且 `move` 只依賴新狀態 ⟹ `LocalReversible`（參數化鋪磚證明，機器級可逆化的可逆性引擎）。**里程碑 B（部分）**：Bennett 1973 history 構造 `bennett f`——單射 + n 步模擬已證；`bennett_not_surjective` 誠實記錄缺口（抽象構造不滿射；動力學層已由 M3c 封死，機器級=後續工作） | 0 |
| M3c Bennett 可逆化 | `M3c_Bennett.lean` | **v0.5 動力學層 Bennett（全證）**：`histConveyor` —— `X × V` 上任意雙射升級成 `X × (ℤ→V)` 上雙射（歷史輸送帶：讀流位 0 當緩衝、記錄從 -1 吐出、整流下移；雙向無限流無「空歷史」角點，滿射由顯式逆映射成立）；`BitTM.bufferedStep` **Feistel 帶緩衝單步**——任意（不可逆）位元機單步配一格緩衝成顯式雙射（新狀態=`next⊕r`、寫入位=`write⊕b`、緩衝吐出被丟棄的 `(q,t 0)`），空白緩衝上精確=`M.step`；`bennettAut`+`bennettAut_iterate`：n 步 conveyor = n 步機器（**無時間膨脹**）、垃圾誠實外顯；`bennettHomeo`：緊 Hausdorff 上正向連續（每輸出座標只讀有限離散資料+至多三帶座標）⟹ 自同胚 | 0 |
| M3d 機器級 Bennett | `M3d_BennettTM.lean` | **milestone A（構造 + 可逆性，全證）**：`bennettTM : BitTM → BitTM` —— 狀態打包 `m' = m + (m+1) + 3`（M-狀態 × HistRec 緩衝 × 3 相位位，顯式 `Equiv` 鏈 `bitsSplit`/`bufSplit`/`shuttleUnpack`）；微步原語全是逐段驗證的置換（`feistelCore` = M3c `bufferedStep` 狀態側 Feistel 輪、`swapHead` 對合、`rotBuf` 循環旋轉、`phaseInc` 3 位遞增、`phaseDispatch` = `prodShear` 相位纖維分派）；`L = shuttleL` 打包共軛複合、`μ = shuttleDir` 只讀新狀態相位位（`ofPerm` 紀律）；`bennettTM_reversible` 由 `ofPerm_reversible` 免費。**只主張構造 + 可逆**；**milestone B（部分）**：4-軌帶佈局定案（模擬格 `k` ↦ 帶位 `4k..4k+3` = 工作/垃圾資料/垃圾標記/home 標記）、`shuttleEncode` 編碼、`IsClean` 乾淨組態謂詞（垃圾標記 = 與 home 相鄰連續區段 `[-L,0)`、未標記格 = 0、垃圾內容自由）、`shuttleEncode_isClean`（編碼落在 `IsClean 0`）——皆排程無關全證。**milestone C（2026-07-08 大幅推進，見 docs 設計日誌）**：**C0** `Profile` 凍 16 值（decide）；**C1a** 統一控制表 `ctrlU`（guard 帶位分支+π 合流分派合一、全 decide 驗雙射、週期閉合刻劃）+`ctrlSegment` 組裝；**C2** `ctrlDemoTM`/`ctrlFullTM`（統一控制表→真可逆機→流，端到端）+`dataSeg`（Feistel 條件化於 mstep）；**C3c** `IsCleanQuad`（垃圾散置一般化）；**C5a** `bennettTM_suspension_simulates`（字面 shuttle 機→流）；**C4b 有界版** `unifiedStepL_macro2_blank`（乾淨起點 2 微步做 M 實際 next/write，垃圾外顯）。**剩**：C4b 無界宏步（帶穿梭+傾倒迴圈+環計數器破 in-degree，多週核）。全 verified 零新 sorry | 0 |
| M4 懸掛構造 | `M4_Suspension.lean` | 映射環面 + 懸掛流群律/切片連續/時間-1 實現；**v0.2 可逆升級**：完整不變量 `(e^⌊t⌋x, fract t)`、`mk` 等價刻劃、切片嵌入單射、`X` 緊 ⟹ 環面緊、商投影是開映射、懸掛流**聯合連續**（開商映射法，免 Whitehead） | 0 |
| M5 Reeb 介面層 | `M5_ReebInterface.lean` | 連續流結構（嚴格）＋抽象向量微積分簽名＋`IsBeltrami`；Etnyre–Ghrist 對應 | 1 ⛔ |
| M6 主定理 | `M6_EulerTuring.lean` | `Simulates` 謂詞；主定理（Euler-only，paper-blocked）；**v0.2 下半層主定理（全證）**：`suspension_flow_simulates` — 緊空間上任何同胚都被緊空間上的連續 ℝ-流經單射編碼模擬；實例 `fullShift_suspension_simulates`（雙邊 full shift）；**v0.3 推論（全證）**：`genShift_suspension_simulates` — 任何**可逆 generalized shift** 被緊空間上連續 ℝ-流經單射編碼模擬；`fullShiftGS` = full shift 作為 GenShift 的平凡實例；**v0.4 推論（全證）**：`reversibleTM_suspension_simulates` — 任何**可逆位元圖靈機**的組態動力學被緊空間上連續 ℝ-流經單射編碼模擬；端到端實例 `cnotTM_suspension_simulates`；**v0.5 推論（全證）**：`bitTM_suspension_simulates` — **任意（不可逆）位元機**經 Bennett 歷史編碼被緊空間上連續 ℝ-流模擬（可逆性假設拿掉；歷史分量與落點垃圾誠實外顯為存在量詞） | 1 ⛔ |

## sorry 帳本(2026-07-08：仍共 2，全部 paper-blocked，零可攻)

| 宣告 | 分類 | 依賴 |
|---|---|---|
| `reeb_realizes_beltrami` (M5) | paper-blocked | Etnyre–Ghrist 2000 "Contact topology and hydrodynamics I" Thm 2.1；需要接觸幾何（mathlib 無） |
| `euler_flow_turing_complete` (M6) | paper-blocked | Cardona et al. 2021 Theorem 1；經 M5 對應 |

> M3d 里程碑 C 全部推進（C0-C5a、C2、C4b 有界版）**零新 sorry**——共 2 條不變。

Axiom 檢查（`#print axioms`，2026-07-08 綜合掃描 13 頭條定理）：主線 M1-M6 +
M3d 字面機（C0-C5a/C2/C4b 有界）全部已證定理僅依賴
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

> **2026-07-08 里程碑 C 大幅推進**（見 [`docs/M3D_C_DECOMPOSITION_PLAN.md`](docs/M3D_C_DECOMPOSITION_PLAN.md)）：
> C0-C5a、C2、C4b **有界版**全達成、零新 sorry。剩**無界 C4b 宏步**經 U1 對抗艦隊
> 裁決 **BLOCKED_irreducible_obstruction**（傾倒迴圈跳塊數奇偶=帶內容決定=無界量、
> 環計數器修終止不修 merge 單射崩潰、無界量編不進 Fintype Profile；吻合 repo 四次
> 嘗試 rev.1/2/3/ring 皆同機制失敗）→ **永久具名停損**，除非紙上先找到 rev.4 有界修復。
> **主線定理鏈不需要它**（M3c `bitTM_suspension_simulates` 已供動力學層等價全證）。

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
4. **垃圾堆疊拖曳**（milestone B **部分完成**）：✅ 帶佈局 4-軌定案、
   `shuttleEncode` 編碼、`IsClean` 謂詞（標記連續區段 `[-L,0)` 與 home
   相鄰、未標記格=0、垃圾內容自由）、`shuttleEncode_isClean` —— 排程無關
   半邊全證。**未動**：頭移動時旋轉堆疊一格（撿底放頂）、掃描以標記邊界
   終止的微步排程、每類微步保不變量引理 —— 這半邊綁定排程，與步驟 5 一起做
   （對占位排程證引理 = 死工，故不先證）。
5. **模擬引理**（milestone C，未動；風險集中）：每 M-步耗 O(堆疊長) 微步
   （`∃ n` 陳述容納變長排程，配 M6 `Simulates.iterate` 語意）；
   正確性歸納 = 相位×區段不變量。爆量時先證單一相位段部分引理。
   Lean 工程量估 1500+ 行。設計待決 7 條成文於 M3d 檔頭 docstring。

**停損記錄（2026-07-04 第二輪，milestone C 前半）**：本輪把 C 的
**設計面**推進三個 rev 並全部入檔（M3d 檔頭設計日誌），程式面全綠零
sorry：
- **rev.2 幾何定案**：5 格區塊（工作/垃圾資料/垃圾標記/causeway/
  **原點哨兵軌**）+ 垃圾散置 + 傾倒跳過 causeway —— 修掉 rev.1 兩個洞
  （回程端點不可分辨、哨兵可被垃圾假冒）；暫存器加寬（相位 5 位、
  offset 3 位 mod-5）、17 相位 FSM 表成文。
- **rev.3**：緩衝加路徑位 π（`m+2` 位）修「extendL/retractL 控制合流
  ⟹ L 不單射」；控制表架構（抽象控制空間 + 顯式正反表 + `decide`）。
- **第三層障礙（本輪停損點）**：寫+移一體的步進制下，長掃描相位的
  過境入度與「帶相依跳塊計數的奇偶」使傾倒迴圈末端合流**不可逆**——
  有限相位分身救不了。**收斂出的正確路線 = Bennett 1973 quadruple
  紀律**：用 `Dir.stay` 把讀寫步與移動步分離（stay 步讀格轉相位、
  移動相位純移），前驅局部可定，twin 鏈與奇偶問題同時消失；
  另加 one-hot 環形計數器（`m+2` 位）做固定計數傾倒。
  屬新一輪重設計，誠實停損不硬塞。
`bennettTM_reversible` 與 v0.5 四條迴歸定理不受任何本輪改動影響
（可逆性與排程無關）。

## M6 範圍決策（2026-07-04，使用者選定 B：Euler-only）

**明確不主張**「NS 黏滯免疫」（前身草案的斷言，已判定為假／超譯，永久移除）：

1. NS 黏滯耗散率是 `ν ∫ |∇u|² dV`，不是 `ν ∫ |Δu|²`；`Δ_H X = 0` 只給 closed + co-closed，不等於 `∇X = 0`。
2. Weitzenböck：`Δ_H = ∇*∇ + Ric`，「調和 ⟹ 平行」只在 Ricci-flat 流形成立。
3. Cardona et al. 2021 證的是 **Euler 穩態 + Beltrami**，非 NS（Beltrami 通常非 NS 穩態，`νΔu ≠ 0`）。

若未來要碰 NS，僅兩條合法路線（需重開範圍決策）：(A) 限制 Ricci-flat（平坦 T³）、(C) forced-NS。

## 範圍決策二（2026-07-05，使用者選定 A：緊空間自同胚版）

主定理 `euler_flow_turing_complete` 的被模擬對象由「任意 `Encodable Γ` 上的
任意 `step`」收斂為「緊空間自同胚 `e : X ≃ₜ X`」。理由（v0.5 驗收記錄的
兩處落差）：(1) 對可合流 `step` 主張嚴格 `Simulates` 超出 Cardona 原文
（原文走雙射 generalized shift）；(2) `Encodable`（可數）與原文康托爾型
不可數空間不合。新版與已證下半層 `suspension_flow_simulates` 逐字對接；
TM/GS/Bennett 由 M3b/M3/M3c 既有已證橋接餵入；任意（可合流）機器改由
`bitTM_suspension_simulates` 的垃圾外顯語意承接。

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
- ~~主定理陳述層待審（v0.5 驗收時記錄）~~ —— **已解決（2026-07-05，
  範圍決策二，使用者選定 A：緊空間自同胚版）**，見上節。
- M5 的 `VectorCalculus3` 是**運算元簽名**不是幾何：`curl`/`div` 未詮釋，
  任何用到它的定理都是「對所有滿足簽名的詮釋成立」。真詮釋等 mathlib 微分幾何。
