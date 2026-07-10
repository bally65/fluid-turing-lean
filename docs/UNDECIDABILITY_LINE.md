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

### B2 對抗設計裁決（2026-07-09，艦隊 wf_7bf26d1d-802，6 agents/918k tok）

3 藍圖（reuse-方案C / bennett-first / layout-first）各對抗驗（丟失有界/堆疊宏步/停機吸收+splice）。
**三驗一致：無「無界量塞不進 Fintype」牆；Route A 正確；可建、多 session。**

- **(A) 丟失有界 = SOUND**（三驗對真 mathlib 碼核過）：每個 `tr l` ≤1 pop + ≤1 peek + ≤2 push
  後 goto/halt（逐案檢查）。每步丟 = 舊 label（∈ `codeSupp cu Cont'.halt` = 固定 `Finset Λ'`、
  forward-closed，mathlib `tr_supports`/`codeSupp_supports` 已證）+ 舊 var(`Option Γ'` 5 值)+
  popped(`Option Γ'` 5 值)。**全有界、真不像 ToPartrec.step 的無界 continuation frame** →
  route A over route B 正確。
- **★重大 reframe（bennett-first、改變 B2 計劃）★**：`M3c.bufferedStep` 是**無條件 Equiv**
  （對 M 零假設）+ size-generic + `bufferedStep_blank`=空白緩衝上恰 `M.step`。⟹ **可逆性由
  M3c 整批買下、作用在任意「不可逆掃描解釋器」上**。**故 B2 不需方案 C 的 ofPerm/decide
  可逆性苦工**：建普通（不可逆）掃描解釋器 `M_tr : BitTM`（模擬 tr）、M3c 把它變可逆 +
  `bennettHomeo` 緊空間同胚、`bennettAut_iterate` 給 n 步。方案 C 的 in-degree 牆在此 moot
  （無界量住帶 ℤ→Bool、有限態只放 offset/相位/緩衝）。
- **(B) 宏步 = HOLE（非 WALL）**：`trackWalkTM_reaches_marker` 真接得上（4 堆疊各獨立唯一標記
  軌、無跨堆疊無界量），且因可不可逆走位更簡單。**THE CRUX HOLE = 宏步正確不變量 `R`
  (`M_tr`↔`TM2.Cfg`) + 歸納**（C-δ 味、但無可逆性約束）= 多 session 核心、無牆。
- **(C) 停機吸收+splice = HOLE**：可逆層的緩衝使停機非字面 fixpoint（in-degree 陷阱）→
  用**吸收區 parking**（`H_Γ:={控制=qhalt}`、qhalt 給 reversible 空轉不離 H_Γ；= M14 `hH`）。
  simulation 引理（`M_tr.step^[n_k]`=一 TM2 步、halt↔halt）傳 `tm2_halting_undecidable`。

**具體修（皆有界非牆）**：record popped 用 3 位（`Option Γ'` 5 值、非 2 位）；`|codeSupp|`
可能上百態 → 控制用 `feistelCore`（xor-based、**無 decide**、size-generic）避 decide 爆，
勿用 `ctrlEquivOfInverse`（decide 會炸）。

**修訂建置順序（依裁決）**：B2a 建不可逆掃描解釋器 `M_tr : BitTM`（模擬 tr、多 session 核心，
走位存取堆疊頂、bounded-loss record）→ B2b M3c 可逆化+緊同胚（免費、literal copy）→
B2c 宏步正確不變量 `R`+歸納（真核心）→ B3 忠實懸掛 → B4 終定理。**放棄「直接建可逆
BitTM」，改「不可逆解釋器 + M3c 整批可逆化」= 大幅省工。**

### 風險/提醒

- B2 是唯一大核。TM2 每步有界丟失 = Bennett 前提 ✓；堆疊頂存取距離資料相依 =
  方案 C 走位機器的正戲（synergy：C-δ 的可達性歸納正是為此練的）。
- 宏步「∃n 變長」在 `Simulates`/`Simulates.iterate` 語意下天然容納（M9 已用）。
- 每塊 `scripts/check.sh` 收尾守硬規則（零 sorry + 標準三公理）。
- 誠實界線持續：本線的「流」是懸掛流（緊空間連續 ℝ-流）；接真 Euler/NS 幾何仍走
  M5/M7 的明寫假設（paper-blocked、與本線正交）。

## B2a 進度 + M_tr step 本體 KICKOFF（下 session 專攻）

**B2a 佈局層完備 ✅（M17，全零 sorry/標準三公理）**：
- `multiTrackEnc` / `trackIdx`：P=n+1 軌交錯 + readback + 單射（泛化 fixedEnc4）。
- `Γ'BitEquiv`：TM2 字母 Γ'(4 符號) ↔ 2 位元（零公理）。
- `stackContent` / `stackMark`：一堆疊 List Γ' → (內容軌 + 唯一頂標記軌)；
  `stackContent_get`(readback) / `stackContent_push_top`(push 落頂) / `stackMark_self/ne/push`(唯一 + 移標記 ±1)。
- `stackDecode` / `stackDecode_stackContent`：**編碼忠實性 round-trip**（組態由位帶唯一決定）。

**剩 = M_tr step 函數本體（唯一大核、下 session 專攻起點）。**

### M_tr step KICKOFF 規格

目標：定 `M_tr : BitTM`（不可逆 OK），其 step 逐步模擬 mathlib `Turing.PartrecToTM2.tr` 的
一個 TM2 步（= `stepAux (tr l) v S`）。**不需可逆**（M3c bufferedStep 之後整批買可逆性）。

**狀態（`Fin m → Bool`，有限、bounded-loss 的關鍵）**：packs
`(label idx ∈ Fin |codeSupp cu Cont'.halt| , local var : Option Γ' [3 位], phase, offset mod P, buffer)`。
`codeSupp cu Cont'.halt : Finset Λ'`（mathlib、forward-closed `tr_supports`）給 label 的有限性；
`cu` = M16 `tm2_univ_wiring` 的固定通用碼。

**帶（`ℤ → Bool`）**：M17 `multiTrackEnc` 把 4 堆疊（main/rev/aux/stack，各 = stackContent 2 軌
+ stackMark 1 軌 = 3 軌 × 4 = 12 軌，+home/垃圾）交錯。

**step 排程（macrostep = ∃n microsteps）**：讀 (l,v) in-state → 逐 `tr l` 的 ≤const 堆疊 op：
走位到該堆疊頂標記（M3e `trackWalkTM` + `trackWalkTM_reaches_marker`，offset 泛化 Fin 4→Fin P）
→ 有界局部編輯（stackContent push/pop + stackMark ±1，用 stackContent_push_top/stackMark_push）
→ 淨零回 home。丟失（舊 label/var/popped）存 buffer（供 B2b Bennett）。

**有序子塊**：
1. `tr` 的案例分解引理：`tr l` 逐案（move/clear/copy/succ/pred/ret*）的堆疊 op 列表（讀 mathlib ToPartrec.lean:302-342）。
2. 單堆疊-op 的 BitTM 微步實現（走位 + 編輯）+ 正確性（用 M17 stack 引理 + M3e 走位可達性）。
3. 組成 M_tr.step（phase 排程）+ `encTM2 : TM2.Cfg → M_tr.Cfg`（用 multiTrackEnc + stackDecode 忠實）。
4. **macrostep 正確**：`∃n, M_tr.step^[n] (encTM2 c) = encTM2 (TM2 一步 c)` + halt↔halt（B2c）。

**提醒**：offset 泛化 Fin 4→Fin P 要一般證（非 decide，P 變數）；label 用 feistelCore 式 xor（非
decide，|codeSupp| 大）；先做子塊 1（純案例列舉、可 day-1）暖身。

---

## M_tr step 進度更新（子塊 1-4）

- **子塊 1 ✅（M18）** 控制有限性：`trLabels c := codeSupp c Cont'.halt`（Finset Λ'）+
  `tr_supports_trLabels`（= mathlib `tr_supports`，`TM2.Supports`）+ `trLabelEquivFin`
  （label ≃ Fin card）= route A 有限控制地基。
- **子塊 2 ✅（M17）** 單堆疊-op 編碼正確性：`stackContent_push_lower`（push 下層不變）+
  `stackContent_dropLast_eq`（pop 留下層）+ `stackDecode_push/pop`（decode 忠實）= push/pop
  局部編輯的編碼層規格（子塊 3 的正確性目標）。
- **子塊 3 ✅（M19）** encStacks 全組態編碼器 + 忠實性：`kEquiv:K'≃Fin 4` + `stackTracks`（3 軌）
  + `allTracks`（12 軌）+ `encStacks := multiTrackEnc` + `encStacks_injective`（位帶唯一決定
  全 4 堆疊）= M17 單堆疊 round-trip 抬到全組態。

- **子塊 4 動力學組裝 ✅（M20）+ M_tr 本體 = 唯一剩餘缺口**。
  **關鍵發現**：到「懸掛流有限時間 blowup 觸發不可判定」的**下游全鏈已證且已接**
  （M3c bennett + M4 suspension + M14 忠實 + M10 blowup + M16 TM2 停機不可判定）。M20 組裝：
  - `suspension_blowup_trigger_undecidable`：任意緊自同胚 `e` + 前向可達不可判定 ⟹ 懸掛流
    blowup 觸發不可判定（M14 兩定理 3 行組合）。
  - `bitTM_bennett_blowup_undecidable`：實例化到 `e := bennettHomeo M`，`huniv` 由
    `bennettAut_iterate`（無時間膨脹）從機器級 `M.step` 停機證出。**剩兩條 crisp 義務**：
    (1) `hmachine`：`M.step` 模擬通用 TM2 停機（配 M16）；(2) `hHclosed`：停機集 bennett-不變。

  ⟹ **整個流體端不可判定性 = 造一個位元機 `M_tr` 使 `M_tr.step` 模擬通用 TM2 `stepAux` 樹走**
  （+ 不變停機集）。這是 M_tr 建構本體：定義 `M_tr : BitTM`（控制 = M18 Fin 編碼、帶 = M19
  encStacks；`next/write/move` = 解釋器迴圈：讀 (l,v) → 逐 `tr l` 的堆疊 op → M3e 走位取頂 +
  局部編輯 → 回 home）+ 證 `∃N, M_tr.step^[N](encCfg c) = encCfg (TM2.step tr c)`（對 Stmt 樹歸納）。
  **非 paper-blocked**（mathlib 有全零件：`tr`/`stepAux`/`codeSupp`/M3e 走位可達性）、**非可 fake**、
  是**大型多 session 工程**。M20 把它誠實外顯為唯一缺口（方案 A 條件化，同 M7 NS 幾何依賴手法）。

  **M_tr 本體下 session 起手點**：(4a) 定 `encCfg : Cfg' → M_tr.Cfg`（控制用 M18 trLabelEquivFin
  塞 Fin m→Bool、帶用 M19 encStacks）；(4b) 逐 Stmt 建構子（goto/load = 純控制、push/pop/peek =
  走位+編輯）的單微步引理；(4c) Stmt 樹歸納組 macrostep；(4d) halt↔halt + 用 M16 兌現 hmachine。

  - **4a ✅（M21）** `encCfg : Cfg' → (Option Λ' × Option Γ' × (ℤ→Bool))`（位帶 = M19 encStacks、
    label/var 保留原型真忠實）+ `encCfg_injective`（全組態由編碼唯一決定，位帶真編 4 堆疊）+
    `ctrlLabels cu := insert none ((trLabels cu).image some)` + `l_mem_ctrlLabels`（可達組態控制
    落在有限集 = M_tr 的 Fin m 控制地基）+ `ctrlFin`（控制 ≃ Fin card）。範圍界線：把 label 實壓進
    位元向量 + 接動力學 = 4b。
  - **4b 路線決策（使用者定）= 接 mathlib TM 化約鏈（route β）**。**關鍵發現**：mathlib
    `Turing.TM2to1` / `TM1to1` / `TM1to0` **已證** TM2 → TM1 → TM1(Bool 字母) → TM0(Bool) 完整
    化約——含把 4 堆疊交錯到帶、**頭走位到堆疊頂**（`addBottom` + `(Tape.move right)^[(S k).length]`），
    正是 M3e/M17/M19 手刻的走位+編碼；三段皆保停機（`tr_eval_dom` / `tr_eval`）+ 有限可達
    （`tr_supports`）。⟹ **不手刻走位**（那道多月牆倒了），只補「TM0(Bool) → 我們的 `BitTM`」有界橋。
    - **4b-1 ✅（M22）** `instFintypeK'`（補 mathlib 缺的 `Fintype K'`，`TM1to1` 的 Bool 字母化約需
      `Fintype (Γ' K' Γ)` ⟸ 之）+ `tm2to1_halts_iff`（通用機器經 `TM2to1` 化約成 TM1、停機保持，確認
      鏈在我們參數 `K'/Γ'/Λ'/Option Γ'` 上可套用）。
    - **4b-2 ✅（M23）** `TM1to1` Bool 字母化約：`tm1to1_halts_iff`（組態級停機橋 =
      `TM1to1.tr_respects` ∘ `StateTransition.tr_eval_dom`，參數化於 init 翻譯 `h`）+ `tm1to1_supports`
      （有限可達，字母需 `Fintype`←`instFintypeK'`）+ `tm1to1_enc`（`exists_enc_dec` 免費 bit 編碼）。
      踩雷：`tr_respects` 需第 4 參 `encdec`；mathlib 不給 eval/init 助手、不預組合鏈。
    - **4b-3 ✅（M24）** `TM1to0` 化約（三段純化約橋完成）：`tm1to0_halts_iff`（組態級停機橋，同介面）
      + `tm1to0_eval`（**eval 等式** `TM0.eval = TM1.eval`，mathlib `tr_eval` 直接給）+ `tm1to0_supports`
      （有限可達，需 `Inhabited σ`+`Fintype σ`）。TM0 一步語意（讀→寫或移）最接近我們 `BitTM`。
    - **4b-4 = TM0(Bool) → 我們 `BitTM` 橋**（route β 唯一需動腦接口），拆 4 子鑽：
      - **4b-4a ✅（M25）** 帶表示橋：mathlib `Tape.nth` = `ℤ→Bool` 視圖；我們 `Dir` 有 **stay**
        （3 態）⟹ 1 BitTM 步 = 1 TM0 步。`tapeStep_nth`（= 我們 BitTM 帶更新公式，逐格吻合）+
        `dirMove`/`dirMove_nth`/`tape_head_nth`。踩雷：`open Turing` 遮蔽我們 `Dir`→不 open + qualify。
      - **4b-4b ✅（M26）** 狀態編碼：`ctrlType S := Option ↥S`（停機槽+可達標籤）+ one-hot `encCtrl`
        （`m=ctrlCard`）+ `encCtrl_injective` + `decCtrl := Function.invFun`（左逆免費，免 dite/castLE）+
        `decCtrl_encCtrl`（round-trip）+ `encHalt`（停機 sentinel）。踩雷：`decide_eq_decide` 後 `x=x→True`。
      - **4b-4c ✅（M27）** 定 `M_tr : BitTM` + 一步模擬（核心 payload）：`Mtr`（`stepData` 由讀
        `(狀態,位)` 算 `(下一控制,寫,方向)`）+ `encTM0`（組態編碼器）+ `Mtr_step_halt`（`encHalt` 自環
        = 停機吸收）+ **`Mtr_step_run`**（非停機一步追蹤：`M q head=some(q',act)` ⟹
        `M_tr.step (encTM0⟨q,T⟩) = encTM0⟨q',actApply act T⟩`；狀態用 M26 `decCtrl_encCtrl`、帶用 M25
        `tapeStep_nth`+`Tape.write_self`）。**1 BitTM 步=1 TM0 步**（我們 `Dir` 有 stay）。踩雷：`ctrlType`
        改 `abbrev`；`Supports` 前向封閉 → `dif_pos hq'`。
      - **剩 4b-4d** 停機橋：`∃k, M_tr.step^[k](encTM0 init) 之控制 = encHalt` ⟺ TM0 停機（串
        `Mtr_step_run`+`Mtr_step_halt` 對 `TM0.step` 迭代歸納）。
    - **4b-5** 接 M16 兌現 `hmachine` + `hHclosed` → M20 收**無條件**。
    - **4b-5** 接 M16 兌現 `hmachine` + `hHclosed` → M20 收**無條件**。
    - **取代關係**：M3e/M17/M19 手刻走位+編碼**大部分被 mathlib 取代**；M18/M20/M21 照用
      （有限性壓縮 + route-agnostic 頂石 + 全組態忠實性想法）。
