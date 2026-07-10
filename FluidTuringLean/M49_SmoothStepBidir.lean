import Mathlib
import FluidTuringLean.M48_SmoothStepAssemble

/-!
# Module 49 — GPAC σ 構造 Brick G4d2：雙向 move（玩具全 σ、左移三層巢狀）

**方向三 GPAC 線**（C^∞ 語意、unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。G4d2 = 把 G4d1（M48）
右移-only 全 σ 擴成**雙向**（左/右移）。轉移表多一欄 `move∈{L,R}`（編碼 `M∈{0,1}`、由 move-table
`tbl2D` 查得字面 0/1）；每條移動帶分量 = `smoothSelect(M, 左移臂, 右移臂)`（`M=0→_left(0≤0)`、
`M=1→_right(1≤1)` 緊界精確 discharge）。

## 交付（全顯式、格點字面相等、C^∞、零 sorry、標準三公理）

- **`moveL_R_exact`（★左移三層巢狀難點★）**：`(l₀+(s'+(K·enc(s::R')−s))/K)/K = enc(l₀::s'::R')` ——
  **一行 `field_simp;ring`**（純代數、無 `Nat.digits`、需 `K≠0`）。直接反駁「左移巢狀是真機唯一新難點/
  可能多輪」的恐懼。
- **`smoothSelect_contDiff`（唯一新義務）**：`smoothSelect` 對 selector + 兩臂 joint C^∞（M44 只出 1-D
  `HasDerivAt`）。自然家在 M44，本磚就地補以免動既有鏈。
- **`sigmaRL_exact`（★CRUX★）**：雙向玩具 `σ(gEnc c)=gEnc(gStepRL c)` 字面相等（`cases move`、
  `smoothSelect_left/right` 挑臂、各臂 M47 純代數 `moveR_exact`/`moveL_R_exact`/`encTape`）。
- `sigmaRL_contDiff`：雙向 σ C^∞（`ContDiff.prodMk` + `smoothSelect_contDiff`）。

## ★誠實範圍（禁 overclaim）★

- **玩具、非真機**：`gStepRL` module-local、有限 List 帶、**要求兩堆疊皆非空**（`L=l₀::L'、R=s::R'`）。
  左端邊界（`L=[]`、`enc[]=0`、無頭可讀、List 編碼無法左移過原點）= **明寫假設**，真機橋（BitTM `ℤ→Bool`
  ↔ base-K 實數、`L=[]/R=[]` 需 eventually-0 雙向 stream 編碼）= G4e、多 session、M25 級純簿記。
  `sigmaRL_exact` 是**單步-單組態**、兩堆疊非空。
- **G4d2 多一條 plateau 義務**：G4d1 只讀 R（`hsloR/hshiR`）；G4d2 也讀 L 首符 `l₀`（新增 `hsloL/hshiL`：
  `K·enc(l₀::L')∈[l₀,l₀+w]`）⟹ 下游 **G5 tube 不變式須維持兩半帶皆可讀**。這是 G4d2 相對 G4d1 唯一真新增
  的證明工程負擔（歸納不變式工作量、非 paper-block）。exactness 條件於此四個 headroom 假設。
- **C^∞、非 analytic**（承 M46-M48）：`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`=C^∞（裸 `⊤`=analytic ω、
  `smoothTransition/sfloor/tbl2D/smoothSelect` 對它假）。若 Brick 6 真目標嚴格 GPAC(analytic)，exact-on-lattice
  不可能、scaffold 離題（唯 G3 `sround` real-analytic）。此語意分歧 leverage 最高、宜先釘死。
- **真牆全在下游、正交**：G4e BitTM 橋、G4d3（多符號 |Γ|>2 + ODE 場 Jacobian `HasFDerivAt`，`ContDiff`
  不提供）、φ 自治化（多月）、G5 全域 tube、**邊際價值**（條件式仍弱於且冗餘於主線 M33 無條件）。
  **G4d2 landing ≠ 線三達成 undecidability。**
-/

namespace FluidTuring

open Real

/-- **左移 R-分量三層巢狀（純 encTape 代數）**：`(l₀+(s'+(K·enc(s::R')−s))/K)/K = enc(l₀::s'::R')`。 -/
theorem moveL_R_exact (k : ℕ) (hk : (k : ℝ) ≠ 0) (l₀ s' s : ℕ) (R' : List ℕ) :
    ((l₀ : ℝ) + (((s' : ℝ)) + ((k : ℝ) * encTape k (s :: R') - (s : ℝ))) / (k : ℝ)) / (k : ℝ)
      = encTape k (l₀ :: s' :: R') := by
  simp only [encTape]; field_simp; ring

/-- **`smoothSelect` joint C^∞**（新；M44 只有 1-D `HasDerivAt`）：selector + 兩臂皆 C^∞ ⟹ 選擇 C^∞。 -/
theorem smoothSelect_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {sel a b : X → ℝ}
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sel)
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => smoothSelect (sel x) (a x) (b x)) := by
  unfold smoothSelect
  exact ha.add (((Real.smoothTransition.contDiff (n := ⊤)).comp hs).mul (hb.sub ha))

/-- **玩具雙向 step（module-local）**：`L,R` 皆非空。`move=true→右移`（=G4d1）、`false→左移`。 -/
def gStepRL (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) : GCfg → GCfg
  | ⟨q, l₀ :: L', s :: R'⟩ =>
      if move q s
      then ⟨δq q s, δw q s :: l₀ :: L', R'⟩
      else ⟨δq q s, L', l₀ :: δw q s :: R'⟩
  | c => c

/-- **玩具雙向 σ:ℝ³→ℝ³**：`L,R` 分量各以 `smoothSelect(M, 左移臂, 右移臂)` 挑臂。 -/
noncomputable def sigmaRL (δq δw moveR : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun p =>
    ( tbl2D δq Q K w p.1 p.2.2,
      smoothSelect (tbl2D moveR Q K w p.1 p.2.2)
        ((K : ℝ) * p.2.1 - sfloor K w ((K : ℝ) * p.2.1))
        ((tbl2D δw Q K w p.1 p.2.2 + p.2.1) / (K : ℝ)),
      smoothSelect (tbl2D moveR Q K w p.1 p.2.2)
        (((sfloor K w ((K : ℝ) * p.2.1))
            + (tbl2D δw Q K w p.1 p.2.2
                + ((K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2))) / (K : ℝ)) / (K : ℝ))
        ((K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2)) )

/-- **★CRUX G4d2★：雙向玩具 σ 格點字面相等**：`σ(gEnc c)=gEnc(gStepRL c)`（`cases move`、
`smoothSelect_left/right` 挑臂、各臂 M47 純代數）。四 plateau 前提（兩半帶）= 假設、G5 discharge。 -/
theorem sigmaRL_exact (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q K : ℕ)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hK : (K : ℝ) ≠ 0)
    (q : ℕ) (hq : q < Q) (s : ℕ) (hs : s < K) (l₀ : ℕ) (hl₀ : l₀ < K)
    (L' R' : List ℕ)
    (hsloR : (s : ℝ) ≤ (K : ℝ) * encTape K (s :: R'))
    (hshiR : (K : ℝ) * encTape K (s :: R') ≤ (s : ℝ) + w)
    (hsloL : (l₀ : ℝ) ≤ (K : ℝ) * encTape K (l₀ :: L'))
    (hshiL : (K : ℝ) * encTape K (l₀ :: L') ≤ (l₀ : ℝ) + w) :
    sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w
        (gEnc K ⟨q, l₀ :: L', s :: R'⟩)
      = gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩) := by
  simp only [sigmaRL, gEnc, gStepRL]
  have hMove : tbl2D (fun a b => if moveB a b then (1:ℝ) else 0) Q K w (q:ℝ)
        (encTape K (s::R')) = if moveB q s then (1:ℝ) else 0 :=
    tbl2D_exact _ Q K hw0 hw1 q hq s hs hsloR hshiR
  have hDq : tbl2D (fun a b => (δqN a b:ℝ)) Q K w (q:ℝ) (encTape K (s::R')) = (δqN q s : ℝ) :=
    tbl2D_exact _ Q K hw0 hw1 q hq s hs hsloR hshiR
  have hDw : tbl2D (fun a b => (δwN a b:ℝ)) Q K w (q:ℝ) (encTape K (s::R')) = (δwN q s : ℝ) :=
    tbl2D_exact _ Q K hw0 hw1 q hq s hs hsloR hshiR
  have hReadR : sfloor K w ((K:ℝ) * encTape K (s::R')) = (s:ℝ) :=
    sfloor_exact_on_plateau K hw0 hw1 s hs hsloR hshiR
  have hReadL : sfloor K w ((K:ℝ) * encTape K (l₀::L')) = (l₀:ℝ) :=
    sfloor_exact_on_plateau K hw0 hw1 l₀ hl₀ hsloL hshiL
  rw [hMove, hDq, hDw, hReadR, hReadL]
  cases hmv : moveB q s
  · simp only [Bool.false_eq_true, if_false]
    rw [smoothSelect_left (le_refl (0:ℝ)), smoothSelect_left (le_refl (0:ℝ))]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact moveR_exact K hK l₀ L'
    · exact moveL_R_exact K hK l₀ (δwN q s) s R'
  · simp only [if_true]
    rw [smoothSelect_right (le_refl (1:ℝ)), smoothSelect_right (le_refl (1:ℝ))]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [encTape]
    · exact moveR_exact K hK s R'

/-- **雙向 σ C^∞**（`ContDiff.prodMk` + `smoothSelect_contDiff`）。 -/
theorem sigmaRL_contDiff (δq δw moveR : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaRL δq δw moveR Q K w) := by
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D δq Q K w p.1 p.2.2) :=
    (tbl2D_contDiff δq Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hw' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D δw Q K w p.1 p.2.2) :=
    (tbl2D_contDiff δw Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => tbl2D moveR Q K w p.1 p.2.2) :=
    (tbl2D_contDiff moveR Q K w).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hsfL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => sfloor K w ((K : ℝ) * p.2.1)) :=
    (sfloor_contDiff K w).comp (contDiff_const.mul contDiff_snd.fst)
  have hRpop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => (K : ℝ) * p.2.2 - sfloor K w ((K : ℝ) * p.2.2)) :=
    (contDiff_const.mul contDiff_snd.snd).sub
      ((sfloor_contDiff K w).comp (contDiff_const.mul contDiff_snd.snd))
  refine ContDiff.prodMk hq (ContDiff.prodMk ?_ ?_)
  · exact smoothSelect_contDiff hM
      ((contDiff_const.mul contDiff_snd.fst).sub hsfL)
      ((hw'.add contDiff_snd.fst).div_const K)
  · exact smoothSelect_contDiff hM
      ((hsfL.add ((hw'.add hRpop).div_const K)).div_const K) hRpop

end FluidTuring
