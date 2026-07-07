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
