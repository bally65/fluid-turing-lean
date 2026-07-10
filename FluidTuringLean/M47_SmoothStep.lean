import Mathlib
import FluidTuringLean.M46_SmoothRead

/-!
# Module 47 — GPAC σ 構造 Brick G4a-c：單步 σ 的格點精確組件（value-lookup / 2D 表 / Horner 帶算術）

**方向三 GPAC 線**（C^∞ 語意、unblock Brick 6，見 `docs/GPAC_ROADMAP.md`）。G4 = 組單步 σ，證
`σ(enc c)=enc(step c)` **字面相等**（格點精確）。本磚交付**格點精確組件**（G4a-c，皆顯式 + 格點字面相等、
零 sorry、標準三公理）；**全 σ 組裝（G4d）+ BitTM 帶橋（G4e）留多 session**。

## 交付

- **G4a（value-carrying smooth lookup）**：
  `slookup v k w u = v 0 + ∑_{j<k−1}(v(j+1)−v j)·sstep(j+w,1−w,u)`（telescoping-increments 形，非 naive
  指示子——避 off-by-one）。`sfloor`（M46）= `v=id` 特例。**`slookup_exact_on_plateau`（★CRUX★）**：
  `u∈[i,i+w] ⟹ slookup=v i` **字面相等**；`_contDiff`/`_hasDerivAt`。
  `stateNext δrow k w R := slookup δrow k w (k·R)`：**read∘lookup 融為一次**——讀帶 `R` 首符 `s`、查表得
  `δrow s`（`stateNext_exact` 格點字面相等）。
- **G4b（2D 表）**：`tbl2D`（巢狀兩層 slookup）+ `tbl2D_exact`：`(q,s)→δ q s` 格點精確（純由兩條 exactness 組合）。
- **G4c（Horner 分數帶編碼、★無 Nat.digits★）**：`encTape k (d::ds)=(d+encTape k ds)/k`；
  `moveR_exact`（`k·enc(d::ds)−d=enc ds`，去首符=左移）+ `write_exact`（改首符）——皆**純 `field_simp;ring`**。

## ★誠實範圍（禁 overclaim）★

- **plateau 前提是假設、非本磚自證**：`slookup_exact` 的 `k·R∈[s,s+w]`（讀帶 headroom）由 **G5 tube
  不變式** discharge；G4a 誠實當假設，**不**宣稱「已能讀任意帶」或「模擬了 TM」。
- **C^∞、非 analytic**（承 M46）：`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)` = C^∞（`⊤` 裸寫 = analytic ω、
  smoothTransition 對它假）。若 Brick 6 真目標嚴格 GPAC(analytic)，exact-on-lattice 不可能、scaffold 離題。
- **編碼**：多分量向量 `(q,L,R)`；base `K=4k` 綁 G2 讀餘量 `tail<(k−1)/(K−1)<1/4≤w` 與 G3 basin `δ<1/4`。
- **真牆全在下游、正交**：G4d 全 σ 組裝（`σ:ℝ^d→ℝ^d`、正則憑證是 `ContDiff`/`HasFDerivAt` 非純量 HasDerivAt）、
  G4e BitTM `ℤ→Bool` 帶 ↔ base-k 實數橋（M25/M3b 級純簿記、工時中心）、φ 自治化（M41 多月）、
  plateau-readability 全域不變式（G5 tube）、邊際價值（弱於且冗餘於主線 M33 無條件）。
-/

namespace FluidTuring

open Real

/-! ## G4a：value-carrying smooth lookup（read∘lookup 融合） -/

/-- **值載光滑查表**：`slookup v k w u = v 0 + ∑_{j<k−1}(v(j+1)−v j)·sstep(j+w,1−w,u)`。telescoping 形。 -/
noncomputable def slookup (v : ℕ → ℝ) (k : ℕ) (w u : ℝ) : ℝ :=
  v 0 + ∑ j ∈ Finset.range (k - 1), (v (j + 1) - v j) * sstep ((j : ℝ) + w) (1 - w) u

/-- **★CRUX：value-lookup 格點精確★**：`u∈[i,i+w]`（`i<k`、`0<w<1`）⟹ `slookup=v i` **字面相等**。 -/
theorem slookup_exact_on_plateau (v : ℕ → ℝ) (k : ℕ) {w : ℝ} (_hw0 : 0 < w) (hw1 : w < 1)
    (i : ℕ) (hi : i < k) {u : ℝ} (hlo : (i : ℝ) ≤ u) (hhi : u ≤ (i : ℝ) + w) :
    slookup v k w u = v i := by
  rw [slookup]
  have hg : (0 : ℝ) < 1 - w := by linarith
  have hterm : ∀ j ∈ Finset.range (k - 1),
      (v (j + 1) - v j) * sstep ((j : ℝ) + w) (1 - w) u
        = if j < i then v (j + 1) - v j else 0 := by
    intro j _
    by_cases hj : j < i
    · rw [if_pos hj, sstep_one hg (by
        have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
        linarith), mul_one]
    · rw [if_neg hj, sstep_zero hg (by
        have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.le_of_not_lt hj
        linarith), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfilter : (Finset.range (k - 1)).filter (· < i) = Finset.range i := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [hfilter, Finset.sum_range_sub v i]
  ring

/-- value-lookup C^∞。 -/
theorem slookup_contDiff (v : ℕ → ℝ) (k : ℕ) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (slookup v k w) := by
  apply ContDiff.add contDiff_const
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (sstep_contDiff _ _)

/-- value-lookup 顯式導數。 -/
theorem slookup_hasDerivAt (v : ℕ → ℝ) (k : ℕ) {w : ℝ} (hw1 : w < 1) (u : ℝ) :
    HasDerivAt (slookup v k w)
      (∑ j ∈ Finset.range (k - 1),
        (v (j + 1) - v j) *
          (deriv Real.smoothTransition ((u - ((j : ℝ) + w)) / (1 - w)) * (1 / (1 - w)))) u := by
  have hg : (1 : ℝ) - w ≠ 0 := (show (0 : ℝ) < 1 - w by linarith).ne'
  have hsum : HasDerivAt
      (fun u => ∑ j ∈ Finset.range (k - 1), (v (j + 1) - v j) * sstep ((j : ℝ) + w) (1 - w) u)
      (∑ j ∈ Finset.range (k - 1),
        (v (j + 1) - v j) *
          (deriv Real.smoothTransition ((u - ((j : ℝ) + w)) / (1 - w)) * (1 / (1 - w)))) u := by
    have hb : (fun u => ∑ j ∈ Finset.range (k - 1),
          (v (j + 1) - v j) * sstep ((j : ℝ) + w) (1 - w) u)
        = ∑ j ∈ Finset.range (k - 1),
          fun u => (v (j + 1) - v j) * sstep ((j : ℝ) + w) (1 - w) u := by
      funext u; rw [Finset.sum_apply]
    rw [hb]
    exact HasDerivAt.sum fun j _ => (sstep_hasDerivAt ((j : ℝ) + w) (1 - w) u hg).const_mul _
  exact hsum.const_add (v 0)

/-- **read∘lookup 融合的 state 更新**：讀帶 `R` 首符查表得 `δrow s`。 -/
noncomputable def stateNext (δrow : ℕ → ℝ) (k : ℕ) (w R : ℝ) : ℝ :=
  slookup δrow k w ((k : ℝ) * R)

/-- **★read∘lookup 格點字面相等★**：`k·R∈[s,s+w]` ⟹ `stateNext=δrow s`。 -/
theorem stateNext_exact (δrow : ℕ → ℝ) (k : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (s : ℕ)
    (hs : s < k) {R : ℝ} (hlo : (s : ℝ) ≤ (k : ℝ) * R) (hhi : (k : ℝ) * R ≤ (s : ℝ) + w) :
    stateNext δrow k w R = δrow s :=
  slookup_exact_on_plateau δrow k hw0 hw1 s hs hlo hhi

/-! ## G4b：2D 轉移表（巢狀兩層 lookup） -/

/-- **2D 表**：`(q, s)` 二維查表（外層選狀態列、內層讀符號）。 -/
noncomputable def tbl2D (δ : ℕ → ℕ → ℝ) (Q k : ℕ) (w q R : ℝ) : ℝ :=
  slookup (fun i => slookup (δ i) k w ((k : ℝ) * R)) Q w q

/-- **2D 表格點精確**：`(q,s)→δ q s`（純由兩條 exactness 組合）。 -/
theorem tbl2D_exact (δ : ℕ → ℕ → ℝ) (Q k : ℕ) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (q : ℕ) (hq : q < Q) (s : ℕ) (hs : s < k) {R : ℝ}
    (hlo : (s : ℝ) ≤ (k : ℝ) * R) (hhi : (k : ℝ) * R ≤ (s : ℝ) + w) :
    tbl2D δ Q k w (q : ℝ) R = δ q s := by
  rw [tbl2D, slookup_exact_on_plateau (fun i => slookup (δ i) k w ((k : ℝ) * R)) Q hw0 hw1 q hq
    (le_refl _) (by linarith)]
  exact slookup_exact_on_plateau (δ q) k hw0 hw1 s hs hlo hhi

/-! ## G4c：Horner 分數帶編碼 + 格點精確 move/write（純代數、無 Nat.digits） -/

/-- **Horner 分數 base-k 半帶編碼**：`encTape k (d::ds) = (d + encTape k ds)/k`。 -/
noncomputable def encTape (k : ℕ) : List ℕ → ℝ
  | [] => 0
  | d :: ds => ((d : ℝ) + encTape k ds) / (k : ℝ)

/-- **左移（去首符）格點精確**：`k·enc(d::ds) − d = enc ds`。純 `field_simp;ring`。 -/
theorem moveR_exact (k : ℕ) (hk : (k : ℝ) ≠ 0) (d : ℕ) (ds : List ℕ) :
    (k : ℝ) * encTape k (d :: ds) - (d : ℝ) = encTape k ds := by
  simp only [encTape]; field_simp; ring

/-- **寫首符格點精確**：`enc(s::ds) + (s'−s)/k = enc(s'::ds)`。純 `field_simp;ring`。 -/
theorem write_exact (k : ℕ) (hk : (k : ℝ) ≠ 0) (s s' : ℕ) (ds : List ℕ) :
    encTape k (s :: ds) + ((s' : ℝ) - (s : ℝ)) / (k : ℝ) = encTape k (s' :: ds) := by
  simp only [encTape]; field_simp; ring

end FluidTuring
