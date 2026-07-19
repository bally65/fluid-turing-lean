# CONCEPT — `ReebBeltramiRealization` 假設因式分解（提案）

> **CONCEPT — not built。** 本文件把 `ReebBeltramiRealization`（`FluidTuringLean/M5_ReebInterface.lean:109`）因式分解成兩個具名假設的**提案**，**未經 Lean 實作**。文中任何陳述都不改變 repo 現有定理的內容或範圍。

## 現況（實檔核對 2026-07-16）

`ReebBeltramiRealization : Prop` 說：對任意緊空間 `M` 上的連續 ℝ-流 `F`，存在緊空間 `M'`、抽象向量微積分詮釋 `V`、場 `u`（`V.IsBeltrami u`）與單射 `ψ : M → M'`，使 `u` 的積分流經 `ψ` 共軛延拓 `F`。其 docstring（M5:105–108）明引 **Cardona et al. 2021 (PNAS) Thm 1 經 Etnyre–Ghrist 對應**。

因此這個假設**不是** Etnyre–Ghrist 對應本身——EG 只把「Reeb 場」翻譯成「Beltrami 場」，**不含**「任意連續流都嵌得進某 Reeb 流」的普遍性量詞。假設實際上是兩件事的合成：

## 假設 U —— Reeb 普遍性（Universality；CMPP 2021 plug 構造）

**非形式陳述**：對任意緊空間 `M` 上的連續 ℝ-流 `F`，存在緊接觸 3-流形 `(N, ξ = ker α)` 及其 Reeb 流 `R_α`，與拓撲嵌入 `ψ : M → N`，使 `R_α^t(ψ x) = ψ(F^t x)`（Reeb 流共軛延拓 `F`）。

**文獻指涉**：Cardona–Miranda–Peralta-Salas–Presas 2021, PNAS 118(19), Thm 1（repo 現行引法）；構造核心＝接觸範疇的 plug 構造／Reeb 嵌入柔性。

**⚠ CMPP 原文核對＝待辦**：PNAS Thm 1 的**字面陳述**是否直接涵蓋「∀ 任意連續流」的量詞（或字面上只構造 Turing-complete 的特定流，而完整普遍性版本在 CMPP 的姊妹論文《Universality of Euler flows and flexibility of Reeb embeddings》），**未對原文逐字核對**。本因式分解以 fluid repo 現行 docstring 的引法為準；假設 U 的精確出處（哪一篇、哪個定理、量詞範圍）寫論文前必須回原文釘死。

## 假設 E —— EG 翻譯（Etnyre–Ghrist 2000）

**非形式陳述**：緊接觸 3-流形 `(N, α)` 的 Reeb 場 `R_α`，存在相容（adapted）黎曼度量 `g`，使 `R_α` 是 `g` 下的 rotational Beltrami 場（`curl_g u = λ u`，`λ ≠ 0`，`div_g u = 0`）——即 Euler 穩態解。合成時只用「Reeb ⟹ Beltrami」方向。

**文獻指涉**：Etnyre–Ghrist 2000（Contact topology and hydrodynamics；不帶定理編號）。

## 合成關係（提案）

```
ReebBeltramiRealization  ⇐  假設 E（EG 翻譯）∘ 假設 U（CMPP 普遍性）
```

註：兩個具名假設要在 Lean 裡**非空洞地**陳述，本身就需要 mathlib 沒有的詞彙（接觸形式、Reeb 場、真 curl/div、嵌入）；在現有抽象簽名層無法區分（`reebBeltramiRealization_trivial` 已機器證明該層空洞）。

## 誠實後果

1. **就算流形版 EG 100% 蓋完（contact_geometry_lean 全線兌現），`ReebBeltramiRealization` 仍不放電**——那只放電假設 E 這一半。
2. **假設 U（普遍性／plug 構造）無人形式化過任何近似物**：mathlib 無 plug 構造、無 Reeb 嵌入柔性、無 h-principle 類機具；據所知任何證明助理中都沒有。這一半才是真正的長城。
3. 因式分解的價值＝把「可兌現的一半」（E）與「無人碰過的一半」（U）**分開標價**，堵住「蓋完 EG 就完成 fluid 假設」式 overclaim。

## 附錄：repo 內舊式「＝Etnyre–Ghrist」歸因位置（僅記錄，未改動）

- `FluidTuringLean/M5_ReebInterface.lean:16–19`（模組頭「Lemma B」段：以 EG 對應開頭描述被提升的假設）
- `FluidTuringLean/M5_ReebInterface.lean:96–98`（段落 docstring：前身 sorry 描述為 EG 2000 Thm 2.1 的 "Reeb ⟹ Beltrami" 步；被提升的 def 實際更強）
- `docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md:98`（M5 表格列：「Etnyre–Ghrist 對應」）
- `docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md:125`（鏈圖：「M5 Etnyre–Ghrist + Cardona Thm 1」）

（`M6_EulerTuring.lean:122–123` 與 `M5:105–108` 已是合成式正確引法，非舊說法。）
