# M3d 里程碑 C — 切割評估方案（評估艦隊產出，2026-07-08）

> 來源：9 隻評估艦隊（4 提案角度→各自對抗審查→1 綜合，全 sonnet）。
> 這是**切割方案，非已測 Lean**——綜合器沒跑過 `lake build`，簽名據既有碼推。
> 下週執行前照本文「第一件事」先做紙上判定。

## 一句話結論：go/no-go = **hybrid（混合）**

這是**單人關鍵路徑專案**，不是艦隊題。艦隊只在三座島真的有用
（C3a/C3b 相斥相位分家、C3c IsClean 一般化 day-1 可起、C5a 免費半邊早銀行）；
其餘全序列，並行是演戲。四份提案的對抗審查**各自獨立**都指向同一句：
`C1a→C1b→C1c→C1d` 是一個腦的重設計、拆不開；C4b 是一條跨相位段邊界的長歸納、
不先釘死逐段不變量就切不動。**艦隊買日曆時間、不買工時**——瓶頸引理不因人多變小。

四份提案**全部被自己的審查判 weak**（沒有一個真正隔離障礙或黏得起來）——
這不是艦隊失敗，是誠實：綜合的價值在**補了一條沒人提的承重引理 C1d**。

## 最關鍵發現：C1d — decide 過 ≠ 單射

每份審查的 salvage 都收斂到同一點：**控制表雙射（`decide`）是必要非充分**。
`decide` 只證「逐 profile 的表是雙射」，**不證**「控制段∘資料段的複合步在
無界垃圾長度上的軌跡仍單射」。這正是 rev.1/2/3 都栽的合流家族可能的
第四層變體藏身處。C1d 把這件事單獨立成一條引理——綜合器新增、四提案都沒有。

## 第一件事（下週；**不是寫 Lean**）

先花 1–2 天做 **C1pre_ProfileSoundness**（紙上）：quadruple 的 stay/move 分離
重設計，是否真讓控制表的前驅「只由 (當前相位, offset, 當前帶格, Profile) 局部決定」——
即 **Profile 能不能維持小的固定 Fintype，還是被迫攜帶無界/歷史相依資料**。
- Profile 是小 Fintype → 整個 decide-based 隔離策略成立
- Profile 必須帶歷史 → **decide 隔離從根不成立，C1 得改成歸納**

這條答案決定 C0 介面怎麼凍。答不出來前不要寫任何簽名。

## 切割（依平行組）

| 組 | 引理 | 風險持有 | 角色 |
|---|---|:-:|---|
| 0-gate | C0_InterfaceFreeze | | 型別骨架，全下游只按簽名 import。C2+ 動工前必須先 typecheck |
| 0-gate | C1pre_ProfileSoundness | ⚠ | 紙上判定（見上）；不過關則 decide 隔離不成立 |
| 1-serial | C1a_CtrlTables | ⚠ | 純資料定義、零證明義務。唯一創造性序列任務，一人到底不拆 |
| 1-serial | C1b_MutualInverseDecide | ⚠ | `decide` 驗逐 profile 表雙射——必要非充分 |
| 1-serial | C1c_TransitIndegreeOne | ⚠ | Bennett quadruple 紀律（入度 1）獨立成可判定事實 |
| 1-serial | C1d_ComposedStepInjective | ⚠ | **綜合器新增承重引理**：控制∘資料複合步在無界垃圾上單射（非自動） |
| 2 | C2_WireShuttleCoreQuad | | 接線，鏡射已落地的里程碑 A 模式；可逆性 `ofPerm_reversible` 免費 |
| 3-parallel | C3a_GuardPhasePreservesIsCleanQuad | | stay-讀寫相位保 IsClean。與 C3b 相斥可並行 |
| 3-parallel | C3b_MovePhasePreservesIsCleanQuad | | move-only 相位。與 C3a 並行 |
| 3-parallel | C3c_IsCleanQuadGeneralization | | 把現有 IsClean 推廣到 h≠0/散置垃圾。**不依賴 C1/C2，day-1 可起** |
| 3 | C3d_SingleStepDispatch | | 機械分派膠水，等 C3a/b/c |
| 4-macro | C4a_MicrostepCount | ⚠ | 環形計數器純算術。**必須對 C1 真表證、不能對 stub**（垃圾無關性是重設計要修的核心） |
| 4-macro | C4b_MacroStepLemma | ⚠ | **中心歸納、真瓶頸**。鏡射 `bennettAut_iterate`；不可拆、一人到底。四審查一致認定最高殘留風險 |
| 5 | C5_SpliceIntoM6 | | 前半（reversible→Simulates）C2 後免費；後半接 C4b，鏈法同 `bitTM_suspension_simulates` |

## 建置順序

1. **Week 0**：C0 用 sorry-body typecheck；C1pre 紙上答完，卡 C0 簽核。C3c 可同時 day-1 起（只碰現有里程碑 B 碼）。
2. **Week 1–2（序列、單人）**：C1a→C1b→C1c→C1d。任何失敗＝具名孤立停損，C1d 未關不進 C2。
3. **Week 2–3（扇出、3–4 人、gate 在 C1d）**：C2（快）、C3a/C3b 並行、C4a 對 C1 真表起。
4. **Week 3**：C3d 機械膠水，等 C3a+b+c。
5. **Week 3–5（序列、單人、真瓶頸）**：C4b，寬列預算，第四層合流再現＝預期內非意外。
6. **Week 3（提前）**：C5a 免費半邊，C2 完就落、與 C4b 命運無關。
7. **Week 5**：C5b 真接合，C4b 落後。
8. 全程：C1d/C4a/C4b 一卡，README 停損帳本立刻加**具名**條目、只圈那條引理，絕不寫整個里程碑 C 失敗。

## 介面契約（扇出前全體先同意，這是安全並行的關鍵）

下游只碰這些名字、不碰內容——換表時只有 C1a–C1d 變、C2–C5 原碼重編：
- **控制介面**：`ctrlEquiv : Profile → CtrlSpace ≃ CtrlSpace` + `shuttleCoreQuad_step_injective` 的**陳述**（真正的隔離邊界）
- **機器介面**（鏡射里程碑 A）：`bennettTMQuad : BitTM → BitTM`、`bennettTMQuad_reversible`、`shuttleEncodeQuad`
- **不變量介面**：`IsCleanQuad` + `singleStep_preservesInvariant` 陳述
- **宏步介面**：`bennettTMQuad_macroStep`，**形狀必須逐字對上** `bennettAut_iterate`（M3c_Bennett.lean:263-267，裸存在量詞、無自由變數）
- **M6 接合**：`reversibleTM_suspension_simulates`（M6_EulerTuring.lean:187-190，已讀證為真）
- C2 起後任何簽名變動要重凍並通知全下游

## 給使用者的真決策（下週開工前）

1. **Profile 型別**：維持小 Fintype，還是 rev.3 停損的誠實解要求它帶更大的有界狀態（如 one-hot 環計數相位）？——C0 凍結前定，別在 C1b 中途才發現。
2. **C4b 預算**：四提案一致認定最高殘留風險（C1 修好後仍可能第四層合流）。要不要撥 2–3+ 週單人不可並行時間？還是里程碑 C 重定範圍＝停在 C3（逐步不變量證完）、C4b 卡了另立具名停損？**這是真 go/no-go，該現在決。**
3. **C5a 免費半邊**：C2 完就落、當獨立成果報 README？零額外成本，只改「done」怎麼記。
4. **要不要側艦隊**：現在派 2–3 人並行 C3a/b/c，還是一人跑完 C1→C4 主脊、艦隊留給後面更清楚的里程碑？鑑於序列瓶頸，單人跑日曆時間可能差不多、省掉協調成本。

## 誠實警告（綜合器自陳）

1. 沒驗 `shuttleCoreQuad/shuttleLQuad` 複合真的保住現有 `shuttleL` 打包形狀（M3d:376-379）——C2 時查、別假設。
2. **C1d 是綜合器合成的新引理、四提案都沒有**，確切陳述是 best-effort 重建、未驗編譯；真內容（有限控制表雙射∘資料段映射→無界垃圾全可達態上單射）自己可能還要再拆。
3. 全程沒跑 `lake build`；讀了落地碼（M3d/M3b/M3c/M6）接地簽名，但 C1–C5 是計畫非已測 Lean。
4. 四提案各有真缺陷（假並行、簽名帶自由變數畸形、障礙洩漏出隔離點）；綜合只留過審碎片，但殘留樂觀可能，尤其 C4a「microstepCount 在 quadruple 下真垃圾無關」＝設計日誌斷言、無人已證。
5. 週數是從 README 自己的 1500+ 行估與兩輪停損粗三角，非嚴謹工程估。

---

# C1pre_ProfileSoundness — 裁決（對抗艦隊，2026-07-08）

> 5 隻艦隊（1 建構→3 攻→1 裁決，全 sonnet）。使用者已決 Profile 維持小 Fintype；此場驗證那是否 sound。

## 裁決：**SOUND_with_extra_bounded_fields** ｜ C0 = freeze_after_one_fix

**Profile 可以維持小 Fintype，成立。** 三攻全被擋（無一構造出合流反例）：

| 攻擊向量 | 結果 |
|---|---|
| 環計數器帶相依 | small_Fintype SURVIVES |
| move 相位入度 | small_Fintype SURVIVES |
| Profile 投影有損 | small_Fintype SURVIVES |

守住的核心防禦（且**接地在真 Lean 碼**、非日誌散文）：spectator-data 模式——緩衝/計數器被
Profile-條件轉移原封帶過（`Equiv.prodShear`/`phaseDispatch`），只由**與 Profile 無關的固定
雙射**（`feistelCore`/`swapHead`/`rotBuf`）依 `(相位,offset)` 改動；兩態 scan 歷史不同時，
**未觸動的無限帶本身**就是消歧來源（M3b `ofPerm`/`GenShift.ofLocal` split 已證）。

## 最終 Profile（16 值，O(1)、與 m 及垃圾深度 L 無關）

- `d(buf)`：Feistel/傾倒緩衝 shear 方向（rev.3 已用）
- `π`：extendL/retractL 合流消歧（rev.3 修，與 twin 奇偶正交、quadruple 下仍需）
- `ring-at-zero?`：one-hot 環計數器轉滿一圈旗標——**取代**（非追加）`緩衝全零?`（refutation 3 抓到後者冗餘）
- `guard-phase read-bit b`：stay-guard 步讀的單一帶位——**讓相位分離成立的新成分**

`|Profile| = 2^4 = 16`；`decide` 成本 O(16 × |C|) 固定有限。

## 唯一未擋下的殘留風險（誠實）

**move 相位入度 =1**——建構者自陳最弱環節，**三攻都無法對「真正畫出的 quadruple 表」驗證，
只以類比辯護**。這是真開放風險：展開完整 ~34 相位表可能露出入度違反，逼加**額外（仍有界）
相位常數**（如 P5a_fromP0/P5a_fromWL0dep/P5a_fromP6）。

**但這不是阻斷**——入度 1 正是 **`decide` 該裁的事**（C1b 的工作），不是紙上判定能收的。
畫表→`decide` 驗 `ctrlBwd∘ctrlFwd=id`，違反當場抓（跟當初抓 rev.2/rev.3 合流同機制）。
所以：**Profile 抽象現在凍、SPhase 最終大小待 C1b 入度審計定**。

## 必須強制的可達不變量（→ IsCleanQuad / C0 義務）

1. offset ≡ 頭絕對位置 mod 5（幾何、排程無關、沿用）
2. 每 guard 相位讀固定 offset、不隨歷史變
3. **move 相位入度恰 1**（crux、未驗、見上）
4. 環計數器在可達態恆 one-hot（需自己的旋轉不變量引理）
5. **IsClean 的 h=0/連續垃圾必須先一般化到散置垃圾**——非細節：quadruple guard 掃的正是這個幾何

## 對 C0 凍結的具體指令

- **現在凍** Profile = 16 值 Fintype（4 獨立 Bool，丟掉 `緩衝全零?` 冗餘）——此抽象過了三向對抗
- **別**把入度 1 當已證——它是 C1b `decide` 的第一個工作，畫表時當場驗
- 條件 5（IsClean 散置一般化 = C3c）其實可 day-1 起、與表無關——建議先開這條銀行早期成果

---

# 範圍決策：里程碑 C 停在 C3，C4b 另立停損（使用者 2026-07-08）

**承諾範圍 = C0 → C1 → C2 → C3（＋ C5a 免費半邊）。C4b 出局。**

## 為何這是好決定（不只是保守）

真正的序列瓶頸、四審查一致認定的最高殘留風險（第四層合流可能再現）＝ C4b。
把它移出承諾範圍後，剩下的全是**艦隊友善**的：C1 序列但有界（畫表+decide）、
C2 快、C3a/C3b/C3c 三島真並行。**移掉 C4b＝移掉唯一不可並行、不可估、最可能爆的一塊。**

## 承諾範圍的交付物（誠實定義「C-lite done」）

- `bennettTMQuad : BitTM → BitTM` 具體構造 + `bennettTMQuad_reversible`（C1+C2，可逆性 `ofPerm` 免費）
- quadruple 控制表 + `decide` 驗雙射（C1b，入度 1 在此當場裁）
- **逐步不變量全證**：guard/move 相位各保 `IsCleanQuad`（C3a/C3b）+ IsClean 散置一般化（C3c）
- `C5a`：把 `bennettTMQuad_reversible` 接進 M6 `reversibleTM_suspension_simulates` 的可逆性半邊

**不含**：C4b 宏步引理（字面機器精確模擬 M.step 的完整證明）、C5b 真接合。

## C4b 的地位（另立停損，非阻斷）

- C4b 移出後**單獨嘗試**；卡了就在 README 停損帳本立**具名條目**（只圈 C4b、日期化），
  **絕不寫「里程碑 C 失敗」**。
- **關鍵：C4b 不做也不傷主線。** 動力學層 M3c `bitTM_suspension_simulates` 已全證
  「任意機器 → 流」；字面機器缺精確模擬引理，只是「這台具體機器也自己走一遍」的
  錦上添花沒收尾。主定理鏈完整性不依賴 C4b。

## 對執行的影響（下週）

- 建置順序 5（C4b Week 3–5 序列瓶頸）**刪除**；7（C5b）**刪除**。
- 剩 C0→C1→C2→C3+C5a：這塊**適合側艦隊**（C3a/C3b/C3c 並行 + C3c day-1 起）——
  決策 4（要不要側艦隊）因此傾向「值得」，因為移掉 C4b 後不再有序列瓶頸吃掉並行收益。
- 決策 3（C5a 當獨立成果報）在此範圍下自動成立：C5a 就是承諾範圍的收尾成果。

---

# 執行進度（2026-07-08）

- **C0_InterfaceFreeze ✅ 已凍**（commit f356832）：`Profile := Bool^4`（d/pathBit/ringAtZero/guardBit），`Profile.card_eq : Fintype.card = 16` decide 證。無相位（SPhase 待 C1b 入度審計）。
- **C3c_IsCleanQuadGeneralization ✅ 已證**（commit f356832）：`IsCleanQuad`（垃圾標記軌 = 任意 `g : ℤ→Bool`，散置）+ `IsClean_toQuad`（連續是特例）+ `shuttleEncode_isCleanQuad`（編碼 g=全 false）。build 過、僅標準三公理、零新 sorry。
- 下一步順序：C1a 畫 quadruple 控制表 → C1b decide 驗雙射（入度 1 在此裁）→ C2 接線 → C3a/C3b（guard/move 相位保 IsCleanQuad，需 C1/C2 落地後）→ C5a。
- **C1a 起步（部分）✅**（commit 3d3bb3e）：控制表機器 `ctrlEquivOfInverse`（decide 驗互逆的 (fwd,bwd)→Equiv，C1a→C1b→C2 介面）+ `SPhase` 相位骨架（ready/mstep/pushG guard + pushM/ret move）+ `isGuard` 可判定分區 + 種子表 `seedCtrl`（decide 驗雙射 + 無固定點）。build 過、僅標準三公理、零新 sorry。**未完（誠實）**：完整 ~34 相位編舞（guard 讀位分支/offset 鎖步/Profile 消歧/入度 1 審計）= 逐相位增補進此機器、每次 decide 重驗的多輪 grind，rev.1/2/3 皆栽於此、非一次成型。SPhase 構造子集會隨入度審計增減。
- **C1a 續進（真控制空間 + guard 分支）✅**（commits 8a2b439, 07ee93b）：
  - `ctrl0`：真控制空間 `CtrlSpace = Bool×SPhase×ShuttleOffset` 上骨架表 + offset 鎖步（pushM/ret 用 offInc/offDec），skew-product 自動雙射、decide 驗；`ctrl0Fwd_preserves_bit`。
  - `ctrlG`：**真 guard 帶位分支**（pushG 讀位：設→pushM 續推、清→ret 返家）。**可逆關鍵**（前三輪栽的點）：控制保持帶位→(相位,offset) 分 bit=false/true 兩獨立區塊→兩塊可用不同相位置換而整體仍雙射（每 bit-block skew-product）。decide 驗互逆=**in-degree-1 紀律機器裁決**。`ctrlGFwd_pushG_branches` 證真分支非退化。
  - 全 build 過、僅標準三公理、零新 sorry、decide 快。
  - **C1a 仍未完**：Profile 參數化分派（extend/retract 經 pathBit π 消歧——fleet 標的難點所在）、one-hot 環計數器終止、完整 ~34 相位編舞、接進 shuttleCore(C2)。這些是繼續的多輪 grid、逐步 decide 迭代。
- **C1a Profile 分派（合流障礙解）✅**（commit 164aaf7）：`ctrlP`——Profile 參數化控制表，合流相位 `atMerge` 依 `prof.pathBit` (π) 分派 extend/retract 續程，另一續程該 profile 停 fixpoint。可逆關鍵=控制保持 Profile(spectator)→每 profile 各自置換，`decide` 驗全 16 profile 互逆。`ctrlP_dispatches` 證 π 真消歧。這是切割艦隊標的 C1d 家族難點的機制解。

## C1a 現況小結（2026-07-08）：四機制全 decide 驗、未統一

四個機制各自 decide 驗過、零 sorry：(1) 機器 `ctrlEquivOfInverse`、(2) offset 鎖步 `ctrl0`、(3) guard 帶位分支 `ctrlG`、(4) π 分派 `ctrlP`。每個都是前三輪栽的合流障礙的機制解、機器裁決。**誠實限制**：四者仍是**分開的示範**，尚未統一成一張跑在 `shuttleCore` 上的真表。**剩餘（C1a 大 grind）**：統一四機制成一張 `Profile → (Bool×統一SPhase×offset) ≃ …`（機制交互處可能冒新合流=fleet 對 C4b 標的第四層風險，部分在統一時就咬）+ one-hot 環計數器 + 完整 ~34 相位編舞 + 接進 shuttleCore(=C2)。統一是下一個大階段、自帶風險。

## C1a 統一 + C5a 頭條達成（2026-07-08，同輪續啃）

- **C1a 統一 ✅**（commit b7e9591）：`ctrlU`——guard 帶位分支 + π 分派合進**一張** `Profile→(Bool×UPhase)≃` per-profile 雙射表（單趟 shuttle 週期，離路徑相位 fixpoint），decide 驗全 16 profile×2 帶位互逆。`ctrlU_guard_and_dispatch` 見證一張表雙功能。
- **控制段組裝 ✅**（commit 89e2292）：`ctrlSegment`——`ctrlU` 經 `Equiv.prodShear` 組成單一 `(Profile×UCtrl)≃`（保持 Profile spectator、纖維套 ctrlU），即 C2 接進 shuttleL 的物件、可逆性顯式。
- **C5a 頭條 ✅**（commit dcebdde）：`bennettTM_suspension_simulates`——**字面 shuttle 機器被連續流模擬**（餵 bennettTM_reversible 進 M6 流模擬；可逆性排程無關、ofPerm 免費）。零 sorry。M6 加 import M3d（無環）。

## 承諾範圍 C0→C3+C5a 收尾狀態

| 子項 | 狀態 |
|---|---|
| C0 凍 Profile | ✅ 16 值 |
| C1a 控制表 | ✅ 設計完成（機器/鎖步/guard/分派/**統一**/組段），全 decide 驗；迴圈=descope C4b |
| C1b decide | ✅ 全程每表 decide 驗 |
| C3c IsCleanQuad | ✅ 散置一般化 |
| **C5a 頭條** | ✅ **字面機器→流** |
| C2 完整接線 | ⏳ 大整合（UPhase↔ShuttlePhase 橋、換掉占位 shuttleCore）——主要價值(啟用 C3a/b)因 C4b descope 而受限 |
| C3a/C3b | ⏳ 需 C2；單步不變量，payoff 被 descoped C4b 閘住 |

**判定**：承諾範圍的**可銀行頭條（C5a）已達成**、C1a 設計完成並 decide 驗、C0/C3c 落地。剩 C2/C3a/C3b 是「排程落實 + 單步正確性」，其 payoff 被已 descope 的 C4b 閘住 —— 屬「錦上添花中的錦上添花」，非阻斷。主線定理鏈完整性早由 M3c `bitTM_suspension_simulates` 保證，與此無關。

## C1a 控制表完整刻劃（2026-07-08，收尾）

- **cycle 閉合刻劃 ✅**（commit 304cb21，零公理）：`ctrlU_cycle_closes`（週期回 ready：帶位=1 走 7 步含 push、帶位=0 走 5 步跳過）+ `ctrlU_cycle_visits_push`（帶位=1 第 3 步真在 pushM）+ `ctrlU_short_cycle_skips_push`（帶位=0 第 3 步已 atMerge、無 push）。
- **統一控制表現為完整驗證物件**：雙射(decide) + guard 帶位分支 + π 分派 + 週期閉合 + 真推送/真跳過。C1a 設計階段**完成並刻劃**。
- **下一步 = C2**（獨立專門重構，非本輪）：橋接 UPhase↔ShuttlePhase 狀態打包、把 ctrlSegment 接進機器。風險=動 40+ 已證定理；payoff 被 descoped C4b 閘。控制表設計已備妥、介面物件(ctrlSegment)已組裝。

## C2 核心達成（2026-07-08，續啃 goal）

- **C2 端到端 ✅**（commit 9fc39c1，加法式、不動既有 bennettTM）：`uBits`（UPhase≃3 位元，decide 驗）+ `ctrlDemoL`（固定 profile 控制 L 共軛到位元狀態）+ `ctrlDemoTM := ofPerm 3 ...`（統一控制表當局部更新的真可逆 BitTM，可逆性 ofPerm 免費）+ M6 `ctrlDemoTM_suspension_simulates`（**統一控制表機器 → 連續流**，端到端）。既有 40+ 定理全綠、零新 sorry。
- **意義**：C1a 設計的控制表不再只是抽象 Equiv —— 落到一台**真機器**、走完「統一控制表 → ofPerm 可逆機 → GS → 同胚 → 懸掛流」全鏈到流。
- **剩 C2 廣度**：機器的 Profile 參數化（現固定全零）、data 段（Feistel/傾倒）整合；C3a/b 單步不變量。迴圈仍 descope C4b。
- **C2 全 Profile ✅**（commit ba6aec0）：profile 從狀態讀（非固定）——狀態=Profile(4 位)×UPhase(3 位)=7 位；`pBits`（Profile≃4 位元 decide 驗）+`statePackU`+`ctrlFullL`（共軛 `ctrlSegment` 到位元狀態，guard 分支+π 分派都在狀態層生效）+`ctrlFullTM`(m=7 真可逆機)+M6 `ctrlFullTM_suspension_simulates`（端到端到流）。零新 sorry、既有定理全綠。
- **剩 C2 廣度**：data 段（Feistel/傾倒）整合，讓機器做真事（現只控制循環）；迴圈仍 descope C4b。

## C2 data 段 + 優解收尾判斷（2026-07-08）

- **data 段 ✅**（commit 881139a）：`uDispatch`（UPhase 版 phaseDispatch）+ `dataSeg`（Feistel 條件化於 mstep 相位）+ `dataSeg_fires_at_mstep`（恰在 mstep 觸發 Feistel）+ `dataSeg_idle_off_mstep`（他相位恆等）+ `dataSeg_reversible`。reuse 既有 feistelPiece、零風險。

### 優解判斷：不建全合成機器（completeness-theater）

`dataSeg ∘ ctrlSegment` 合成一台完整機器**可做但不值得**：(1) 可逆性 ofPerm 免費、兩段 Equiv.trans 自動雙射，全合成唯一新內容＝座標管線 bookkeeping 非新數學;(2) payoff 被 descoped C4b 閘——沒宏步引理則合成機器無「正確做 M 計算」定理＝completeness-theater;(3) data 正確性動力學版 M3c bufferedStep_blank 已全證、字面機層 dataSeg_fires_at_mstep 已給,合成只重排不加證明力。**優解＝control 機器(ctrlFullTM 端到端到流)+data 段(dataSeg 刻劃)各自建好驗證**,reuse 既有件零風險。全合成留 C4b 一起(若解封)。

## 里程碑 C 本輪最終狀態（2026-07-08）

承諾範圍 C0→C3+C5a：**全達成或優解收尾**。
- C0 ✅ Profile 凍 / C1a ✅ 控制表設計+統一+刻劃 / C1b ✅ decide 全程 / C3c ✅ IsCleanQuad 散置
- C5a ✅ bennettTM→流 / C2 ✅ 控制表→真可逆機(ctrlDemoTM/ctrlFullTM)→流 + data 段(dataSeg)
- C3a/C3b（單步不變量 over 排程）+ 全合成機器 + 傾倒迴圈 = 判定為 gated-by-C4b，優解不硬做
主線定理鏈完整性早由 M3c bitTM_suspension_simulates 保證、與 M3d 字面機無關。

## C4b 解封，開始（2026-07-08，使用者 un-descope）

- **C4b 地基 + 單步計算引理 ✅**（commit 9f19605）：先前判 theater 的全合成機器現為 C4b 必需地基。`UState`=(M-狀態×緩衝)×(Profile×UPhase);`ctrlLift`/`dataLift`(view-Equiv 抬升,rfl-based);`unifiedStepL = dataLift.trans ctrlLift`(**data 先動作再 control 推進**=標準順序,我第一版寫反會讓 Feistel 在相位離開 mstep 後才觸發);可逆性 Equiv.trans 免費。**`unifiedStepL_mstep`=第一條真 C4b 正確性內容**:mstep 相位單步對工作分量做 Feistel M-step(推進 M 計算)、相位 mstep→pushG,simp 證。
- **誠實規模**：完整 C4b 是**多輪工作**。地基 + 局部計算已證。**剩餘硬核**：(1) 連 M.step(feistelPiece 空白緩衝=M.next/M.write 的 M.step 局部更新——可做);(2) **宏步歸納**——關鍵缺口:現行 UState **沒有帶子**(ℤ→Bool);真 Bennett 垃圾堆疊需帶子 + 傾倒迴圈,而迴圈 = in-degree 障礙(descoped 那條線的本體)。宏步 over 變長迴圈 = 真正的 2-3 週硬核、第四層合流風險。
- **判定**：C4b 非一 turn 可完成;本輪 genuine 開始並證出局部計算;宏步硬核照 loop-until-dry 式多輪推進或誠實停損。

## C4b 續進：有界宏步（2026-07-08，同輪）

- **單步/有界宏步 ✅**（commits 47a1599, a729e15）：`feistelCore_blank`（空白緩衝 Feistel=M 實際 next/write=機器真算 M，僅 propext/Quot.sound）+ `unifiedStepL_ready`（ready 不算、推進 mstep）+ `unifiedStepL_macro2`（ready 出發 2 步做一次 Feistel M-step、相位到 pushG）= 字面機器**有界宏步**（單趟、無迴圈）。
- **C4b 已證清單**：機器可逆 + 機器真算 M（feistelCore_blank）+ 有界 2 步宏步。全 verified 零 sorry。

### C4b 完整宏步 = 多輪/多週硬核（誠實規模判定）

完整 C4b（真 Bennett 正確模擬）尚缺、且**非一對話可完成**，缺口三層：
1. **帶子**：現行 `UState`/`unifiedStepL` 用 μ=stay（頭不動）、無 ℤ→Bool 帶——是「緩衝機」非「帶穿梭機」。真垃圾堆疊要頭移動 + 帶。
2. **傾倒迴圈**：把緩衝搬上帶要變長迴圈 = pushG 入度 2 = **in-degree 障礙**（descoped 本體）。
3. **環計數器 + 宏步歸納** over 變長迴圈 = 2-3 週單人硬核、第四層合流風險。
下一個可攻小步（尚未做）：`feistelPiece_blank`（feistelPiece 空白=M.next/M.write 的顯式連接，tractable 但 bufSplitPi 打包 plumbing 較 fiddly）→ 讓有界宏步顯式對上 M.step。之後才是帶+迴圈的多週核。
- **判定**：C4b 地基 + 有界宏步 + 機器真算 M 已 verified 落地；完整宏步（帶+迴圈）誠實列多輪/多週硬核，非單對話可交付。

## C4b 有界版完整收尾（2026-07-08，commit 4f676ba）

- **顯式 M.step 有界宏步 ✅**：`bitsSplit_const`/`bufSplitPi_const_false`（常數位向量拆分=常數，rfl 定義級）+ `feistelPiece_blank`（空白緩衝 feistelPiece 工作狀態=M.next、帶位=M.write）+ **`unifiedStepL_macro2_blank`**（乾淨起點 2 微步做 M 實際局部更新：工作→M.next q a、帶位→M.write q a、相位→pushG、緩衝=Bennett 垃圾外顯）。
- **C4b 有界版（無迴圈）完整**：字面機器可逆 + 2 步顯式算 M 一步 + 機器真算 M，全 verified 零 sorry。剩=**無界版（帶穿梭+傾倒迴圈）多週核**（in-degree 障礙）。

## U1 設計健全性裁決：無界 C4b 宏步 BLOCKED（2026-07-08，對抗艦隊 wf_469b2b55）

**裁決 = `BLOCKED_irreducible_obstruction`，go/no-go = `stop_bounded_is_enough`**（1 建構 + 3 攻 + 1 裁決，全 sonnet，三攻全 REFUTED_unsound）。

**核心障礙（吻合 repo rev.3 自記錄 + C1pre 艦隊 + descope 決策，四方獨立收斂）**：
傾倒迴圈的**跳塊數奇偶 = 帶內容決定 = 無界量索引**。環計數器修迴圈**終止測試**（掃帶→查暫存器,sound),但**不碰** merge 點單射崩潰——兩條不同歷史撞同一 `(狀態,位)` 足跡,`L 不單射`,π 救 1 位路徑選擇救不了無界帶相依計數奇偶。無界量無法編碼進任何 Fintype Profile（否則 |Profile| 隨 L 長、不再 decide-able）。這是 C1d「decide 過≠單射」的無界版:decide 驗逐 Profile 雙射但驗不了「控制∘資料複合步在無界垃圾深度上單射」。

**停損判定**：無界 C4b 宏步 = 四次設計嘗試（rev.1/2/3/ring-counter）皆同一機制失敗、機制已理解。非數學不可能證明,但**每個試過的設計都 NOT YET SOUND**。真框架換血（完整 quadruple 或 moving-home O(1) 幾何）未在紙上窮盡、原則上或可救,但 = 新多週輪、下檔第四次失敗風險、上檔錦上添花非新數學。**主線定理鏈不需要它**（M3c bitTM_suspension_simulates 已供動力學層等價全證）。

**結論：停在有界版**（unifiedStepL_macro2_blank 已證、零 sorry）。無界宏步列**永久具名停損**（非「里程碑 C 失敗」,只圈這條）,除非未來有人在**紙上**先找到 rev.4 的有界欄位修復（C1pre 式 gating 實驗）再談形式化。
