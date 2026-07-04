import FluidTuringLean.M3c_Bennett

/-!
# Module 3d — 機器級 shuttle Bennett：`bennettTM : BitTM → BitTM`

把 M3c 的動力學層 Bennett 構造下沉為**字面的位元機**：歷史寫進帶本身，
可逆性由 M3b `ofPerm` 引擎免費（README「後續工作：機器級 shuttle Bennett」
5 步攻擊計畫）。

## 佈局決策（milestone A 定案；B/C 可修但先入檔不歸零）

* **狀態打包**：`m' = M.m + ((M.m + 1) + 3)` ——
  M-狀態 `m` 位 × 緩衝 `m+1` 位（= M3c `HistRec`：舊狀態 + 舊讀位）×
  相位 3 位（8 相位）。**無獨立計數器暫存器**：掃描以帶上標記終止
  （README 步驟 4「所有掃描以標記邊界終止」），緩衝內走位用循環旋轉
  `rotBuf`（swap 頭位 → 旋轉一格，`m+1` 次後自動歸位）。
* **帶佈局**：4-軌區塊 —— 模擬帶格 `k` ↦ 帶位 `4k..4k+3` =
  （工作位、垃圾資料位、垃圾標記位、home 標記位）。
* **`L` 的架構**：`Equiv.prodShear phasePerm (fun ph ↦ σ_ph)` 共軛回滿位向量
  —— 相位置換 × 相位別資料子置換，每段都是顯式 `Equiv`，複合用
  `Equiv.trans`，Lean 逐段驗證。子置換原語：
  `feistelCore`（M3c `bufferedStep` 的狀態側版本：新狀態 = `next ⊕ r`、
  寫入位 = `write ⊕ b`、緩衝出 = `(q, a)`）、`swapHead`（緩衝位 0 ↔ 帶位，
  對合）、`rotBuf`（緩衝循環旋轉）、`condPhaseSwap`（帶位條件相位對換）。
* **`μ` 只讀新狀態的相位位** —— `ofPerm` 約束（方向只能依賴更新後狀態）。
* **非法/未用狀態**：`L` 在未 dispatch 的相位走恆等。全空間置換照樣成立，
  模擬引理（milestone C）只對可達的乾淨組態負責。

## 待決清單（milestone B/C，先成文不解）

1. **相位 FSM 可逆分支**：`prodShear` 形狀只給「資料無關的相位置換」；
   讀標記決定走向的分支要用 `condPhaseSwap`（帶位條件相位對換）複合、
   或 `Prod.comm` 共軛的反向 shear。具體轉移圖未定。
2. **垃圾堆疊拖曳排程**：撿底放頂旋轉一格、堆疊與 home 相鄰不變量；
   記錄 `m+1` 位「一位一區塊」跨 `m+1` 個垃圾區塊（傾向）vs 單區塊多位。
3. **乾淨組態謂詞**：標記連續區段 + 未標記格全 0 + 頭在 home 工作位 +
   相位 = 0 + 緩衝 = 空白。
4. **宏步引理歸納結構**：相位 × 區段不變量；爆量時先證單一相位段部分引理。
5. **`encode : M.Cfg → (bennettTM M).Cfg`**：工作帶 4-步幅嵌入 + 垃圾軌全空 +
   home 標記在原點區塊。
6. **M-step 時頭必須在工作位**（`feistelCore` 讀的帶位 = home 區塊 `4k+0`）：
   走位相位的責任，宏步不變量之一。
7. **相位表（草案，8 相位）**：0 = M-step（Feistel）→ 1..5 = 垃圾記錄逐位
   swap-out + 堆疊旋轉走位 → 6 = 回 home → 7 = 未用（恆等）。
   milestone A 的 `phasePerm` 先取單一 8-循環占位，C 再校正。

本檔 milestone A：構造 + 可逆性（零 sorry）。模擬語意**尚未主張** ——
`L` 的微步程式在 B/C 校正時可改，`(bennettTM M).Reversible` 對任何
置換 `L` 都成立，不受影響。
-/

namespace FluidTuring

noncomputable section

end

end FluidTuring
