import Mathlib
import FluidTuringLean.M47_SmoothStep

/-!
# Module 48 — GPAC σ 構造 Brick G4d1：玩具全 σ 組裝（`σ(enc c)=enc(step c)` 字面相等 demo）

**方向三 GPAC 線**（C^∞ 語意、unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。G4d = 把 G4a-c（M47）+
G1/G2（M44/M46）組件**拼成單一** `σ:ℝ³→ℝ³`，證 `σ(enc c)=enc(step c)` **字面相等**（格點精確）+ C^∞。

## G4d1（本磚）= 玩具右移-only 全 σ demo

**證「組件真拼得起來」**：對一個 module-local 的**真** step 函數 `gStepR`（非抽象假設），組出顯式
`sigmaR:ℝ³→ℝ³`，證 `sigmaR (gEnc c) = gEnc (gStepR c)` **三分量逐一字面相等**（`sigmaR_exact`）+ C^∞
正則憑證（`sigmaR_contDiff`，`ContDiff.prodMk` tuple）。組件全是 M47/M46 既有引理的**純組裝**；唯一新引理
`tbl2D_contDiff` = **2 行 `fun_prop`**。

- `gStepR ⟨q, L, s::rest⟩ = ⟨δq q s, δw q s :: L, rest⟩`：讀 R 首符 `s`、狀態 `q→δq q s`、寫 `δw q s` 入
  L、R 去首符（右移）。
- `sigmaR` 三分量：`q'=tbl2D`（查 2D 表）、`L'=(δw 查值 + L)/K`（push 寫符）、`R'=K·R − sfloor(K·R)`（pop）。
- **編碼決策**：σ 用 **`Prod`（ℝ×ℝ×ℝ）**，非 `Fin 3→ℝ`（`ContDiff.prodMk` 有直接建構子；Pi 版須繞
  `ContinuousLinearMap.pi`）。與 M42 leapfrog 的 `prodMk` idiom 一致。

## ★誠實範圍（禁 overclaim）★

- **`gStepR` 是玩具、module-local**：右移-only、有限 List 帶、**非**接真機（真機橋 = G4e BitTM `ℤ→Bool`）。
  `sigmaR_exact` 證的是「組件對此真 step 恆等」，**不**宣稱模擬了任意 TM。
- **plateau 前提是假設**（`hlo/hhi`：`K·R∈[s,s+w]`），由下游 **G5 tube 不變式** discharge；本磚**不**證讀
  任意帶。**注**：`sround`（G3）**不可**施於原始帶分量（`L,R∈[0,1)` 非整數格點、收縮毀編碼）；digit
  robustness 只作用於狀態暫存器（真整數）與 scaled read `K·R` 抽出的符號。
- **C^∞、非 analytic**（承 M46/M47）：`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)` = C^∞（裸 `⊤` = analytic ω、
  `smoothTransition` 對它假）。**若** Brick 6 真目標嚴格 GPAC(analytic)，exact-on-lattice 不可能、scaffold
  離題。（唯 G3 `sround` 是 real-analytic；讀/查表/窗 G1/G2/G4 仍 C^∞-only。）
- **真牆全在下游、正交**：G4d2（雙向 move、`smoothSelect` 挑臂、左移三層巢狀）、G4e（BitTM 帶橋、
  邊界 `L=[]/R=[]` 破功需 eventually-0 stream 編碼、M25 級純簿記工時中心）、φ 自治化（多月）、G5 全域 tube
  不變式、**邊際價值**（條件式仍弱於且冗餘於主線 M33 無條件）。G4d 通 ≠ 線三達成 undecidability。
-/

namespace FluidTuring

open Real

/-- 玩具組態：狀態 `q`、左半帶 `L`、右半帶 `R`（`R.head` = 讀頭符）。命名避 M3b/M21 的 `encCfg`。 -/
structure GCfg where
  q : ℕ
  L : List ℕ
  R : List ℕ

/-- 玩具右移-only 一步（module-local、非接真機）：讀 R 首符 `s`、`q→δq q s`、寫 `δw q s` 入 L、R 右移。 -/
def gStepR (δq δw : ℕ → ℕ → ℕ) : GCfg → GCfg
  | ⟨q, L, s :: rest⟩ => ⟨δq q s, δw q s :: L, rest⟩
  | c => c

/-- 組態編碼到 ℝ³（★`Prod` 非 `Fin 3→ℝ`★）：`(q, encTape L, encTape R)`。 -/
noncomputable def gEnc (K : ℕ) (c : GCfg) : ℝ × ℝ × ℝ :=
  ((c.q : ℝ), encTape K c.L, encTape K c.R)

/-- 玩具單步 σ:ℝ³→ℝ³：`q'=`查 2D 表、`L'=`push 寫符、`R'=`pop 讀頭符（右移）。 -/
noncomputable def sigmaR (δq δw : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun p => (tbl2D δq Q K w p.1 p.2.2,
            (tbl2D δw Q K w p.1 p.2.2 + p.2.1) / (K : ℝ),
            (K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2))

/-- **唯一新引理（2 行）**：`(p.1,p.2)↦tbl2D` joint 二變數 C^∞。 -/
theorem tbl2D_contDiff (δ : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => tbl2D δ Q K w p.1 p.2) := by
  unfold tbl2D slookup sstep
  fun_prop

/-- **★CRUX：玩具全 σ 格點字面相等★**：`σ(gEnc c) = gEnc(gStepR c)`（三分量逐一）——證 G4a-c 組件
真拼得起來、對真 step `gStepR` 恆等。plateau 前提 `hlo/hhi` = 假設（G5 discharge）；**不**宣稱模擬 TM。 -/
theorem sigmaR_exact (δqN δwN : ℕ → ℕ → ℕ) (Q K : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (q : ℕ) (hq : q < Q) (s : ℕ) (hs : s < K) (L rest : List ℕ) (hK : (K : ℝ) ≠ 0)
    (hlo : (s : ℝ) ≤ (K : ℝ) * encTape K (s :: rest))
    (hhi : (K : ℝ) * encTape K (s :: rest) ≤ (s : ℝ) + w) :
    sigmaR (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ)) Q K w (gEnc K ⟨q, L, s :: rest⟩)
      = gEnc K (gStepR δqN δwN ⟨q, L, s :: rest⟩) := by
  simp only [sigmaR, gEnc, gStepR]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact tbl2D_exact (fun a b => (δqN a b : ℝ)) Q K hw0 hw1 q hq s hs hlo hhi
  · change (tbl2D (fun a b => (δwN a b : ℝ)) Q K w (q : ℝ) (encTape K (s :: rest)) + encTape K L)
        / (K : ℝ) = encTape K (δwN q s :: L)
    rw [tbl2D_exact (fun a b => (δwN a b : ℝ)) Q K hw0 hw1 q hq s hs hlo hhi]
    simp only [encTape]
  · change (K : ℝ) * encTape K (s :: rest) - sfloor K w ((K : ℝ) * encTape K (s :: rest))
        = encTape K rest
    rw [sfloor_exact_on_plateau K hw0 hw1 s hs hlo hhi]
    exact moveR_exact K hK s rest

/-- **玩具 σ 的 C^∞ tuple 正則憑證**（`ContDiff.prodMk`；ODE 場可用的光滑向量場）。 -/
theorem sigmaR_contDiff (δq δw : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaR δq δw Q K w) := by
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)
  · exact (tbl2D_contDiff δq Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  · exact (((tbl2D_contDiff δw Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)).add
      contDiff_snd.fst).div_const K
  · exact (contDiff_const.mul contDiff_snd.snd).sub
      ((sfloor_contDiff K w).comp (contDiff_const.mul contDiff_snd.snd))

end FluidTuring
