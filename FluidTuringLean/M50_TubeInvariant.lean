import Mathlib
import FluidTuringLean.M49_SmoothStepBidir

/-!
# Module 50 — GPAC σ 構造 Brick G5：tube 不變式（headroom ⟹ plateau 前提自動成立）

**方向三 GPAC 線**（C^∞ 語意，見 `docs/GPAC_ROADMAP.md`）。G5 = 把 G4d1/G4d2（M48/M49）的 plateau
**假設**（`hlo/hhi`：`K·enc(頭::rest)∈[頭,頭+w]`）**discharge 成定理**：良編碼（所有 digits `< k`）+
headroom base（`K` 充分大使 tail 界 `(k−1)/(K−1) ≤ w`）⟹ 兩半帶**永遠可讀**，且 `gStepRL` **保持**
良編碼 ⟹ **玩具 TM 的 N 步精確模擬**（`σ^[n](gEnc c) = gEnc(step^[n] c)` 字面相等）。

## 交付（全顯式、字面相等、零 sorry、標準三公理）

- `digitsLt`/`wfCfg`（良編碼謂詞）；`encTape_nonneg` + **`encTape_le_headroom`**（尾巴界 `(k−1)/(K−1)`、
  不動點 `V=((k−1)+V)/K` 的歸納）；
- **`read_plateau_of_headroom`（★G5 核心★）**：良編碼 ⟹ `hlo ∧ hhi` 打包成立（經 `moveR_exact`
  把 plateau 義務化簡為「尾值 `∈[0,w]`」）；
- `gStepRL_wf`（單步保良編碼；需轉移表良性 `hQ/hW`）+ `gStepRL_iterate_wf`（N 步不變式）；
- **`sigmaRL_exact_of_wf`**：M49 的 4 條 plateau 假設**全部 discharge**（只剩良編碼 + headroom base）；
- **`sigmaRL_iterate_exact`（★HEADLINE★）**：`σ^[n](gEnc c) = gEnc(step^[n] c)` **N 步字面相等**
  （條件於軌道兩堆疊恆非空 `hne`——List 版誠實邊界、G4e stream 編碼解）。

## ★誠實範圍（禁 overclaim）★

- **仍是玩具**：`gStepRL` module-local、非真機（G4e）；N 步定理條件於**兩堆疊恆非空**（左端邊界=
  List 編碼內稟、`hne` 明寫假設）+ 轉移表良性（`hQ/hW`：表值落在 `[0,Q)×[0,k)`——真通用機須另證）。
- **headroom 參數**：`(k−1)/(K−1) ≤ w < 1`；取 `K=4k` 給 `(k−1)/(4k−1) < 1/4`，故 `w∈[1/4,1)` 全可。
  `s < K` 由 `s < k ≤ K`（表格上界 `K` ≠ 字母表大小 `k` 的解耦——`δ` 表在 `[k,K)` 段是墊料）。
- **這是離散迭代精確模擬**（`σ^[n]` 的值層），**非**連續流、**非** undecidability（G6 需真機 G4e）、
  **非** tube-Lipschitz（Brick 5 `tracks_ideal` 的 H1 是另一堵牆）。C^∞ 非 analytic（承 M46-49）。
-/

namespace FluidTuring

open Real

/-! ## 良編碼謂詞 + headroom 界 -/

/-- 良 digits：所有元素 `< k`。 -/
def digitsLt (k : ℕ) (ds : List ℕ) : Prop := ∀ d ∈ ds, d < k

/-- 良組態：狀態 `< Q`、兩半帶 digits `< k`。 -/
def wfCfg (Q k : ℕ) (c : GCfg) : Prop := c.q < Q ∧ digitsLt k c.L ∧ digitsLt k c.R

/-- 帶編碼非負（無條件）。 -/
theorem encTape_nonneg (K : ℕ) : ∀ ds : List ℕ, 0 ≤ encTape K ds := by
  intro ds
  induction ds with
  | nil => simp [encTape]
  | cons d ds ih =>
    simp only [encTape]
    exact div_nonneg (add_nonneg (Nat.cast_nonneg d) ih) (Nat.cast_nonneg K)

/-- **headroom 界（緊界 = 不動點 `V=((k−1)+V)/K`）**：良 digits ⟹ `encTape ≤ (k−1)/(K−1)`。 -/
theorem encTape_le_headroom (k K : ℕ) (hk : 1 ≤ k) (hK : 1 < K) :
    ∀ ds : List ℕ, digitsLt k ds → encTape K ds ≤ ((k : ℝ) - 1) / ((K : ℝ) - 1) := by
  have hKr : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  intro ds
  induction ds with
  | nil =>
    intro _
    simp only [encTape]
    exact div_nonneg hk1 hK1.le
  | cons d ds ih =>
    intro hlt
    have hd : (d : ℝ) ≤ (k : ℝ) - 1 := by
      have h1 : d < k := hlt d List.mem_cons_self
      have h2 : (d : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h1
      linarith
    have hih : encTape K ds ≤ ((k : ℝ) - 1) / ((K : ℝ) - 1) :=
      ih (fun x hx => hlt x (List.mem_cons_of_mem d hx))
    have hih' : encTape K ds * ((K : ℝ) - 1) ≤ (k : ℝ) - 1 := by
      rw [← le_div_iff₀ hK1]; exact hih
    simp only [encTape]
    rw [div_le_div_iff₀ hK0 hK1]
    nlinarith [encTape_nonneg K ds]

/-- **★G5 核心：headroom ⟹ plateau 前提★**：良 digits 尾 + `(k−1)/(K−1) ≤ w` ⟹ M48/M49 的
`hlo ∧ hhi` 打包成立（經 `moveR_exact` 化簡為「尾值 `∈[0,w]`」——與頭符 `s` 無關）。 -/
theorem read_plateau_of_headroom (k K : ℕ) (hk : 1 ≤ k) (hK : 1 < K) (s : ℕ) (rest : List ℕ)
    (hrest : digitsLt k rest) {w : ℝ} (hw : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w) :
    (s : ℝ) ≤ (K : ℝ) * encTape K (s :: rest) ∧
      (K : ℝ) * encTape K (s :: rest) ≤ (s : ℝ) + w := by
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    linarith
  have key : (K : ℝ) * encTape K (s :: rest) = (s : ℝ) + encTape K rest := by
    have h := moveR_exact K hK0 s rest
    linarith
  constructor
  · rw [key]; linarith [encTape_nonneg K rest]
  · rw [key]; linarith [encTape_le_headroom k K hk hK rest hrest, hw]

/-! ## 良編碼保持（單步 + N 步不變式） -/

/-- **單步保良編碼**：轉移表良性（`hQ/hW`）⟹ `gStepRL` 保 `wfCfg`。 -/
theorem gStepRL_wf (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k) :
    ∀ c : GCfg, wfCfg Q k c → wfCfg Q k (gStepRL δq δw move c) := by
  rintro ⟨q, L, R⟩ hc
  match L, R with
  | [], R => exact hc
  | l₀ :: L', [] => exact hc
  | l₀ :: L', s :: R' =>
    obtain ⟨hq, hL, hR⟩ := hc
    have hs : s < k := hR s List.mem_cons_self
    have hl : l₀ < k := hL l₀ List.mem_cons_self
    have hLtail : digitsLt k L' := fun d hd => hL d (List.mem_cons_of_mem l₀ hd)
    have hRtail : digitsLt k R' := fun d hd => hR d (List.mem_cons_of_mem s hd)
    simp only [gStepRL]
    split
    · -- 右移：⟨δq q s, δw q s :: l₀ :: L', R'⟩
      refine ⟨hQ q s hq hs, ?_, hRtail⟩
      intro d hd
      rcases List.mem_cons.mp hd with h | hd'
      · subst h; exact hW q s hq hs
      rcases List.mem_cons.mp hd' with h | hd''
      · subst h; exact hl
      · exact hLtail d hd''
    · -- 左移：⟨δq q s, L', l₀ :: δw q s :: R'⟩
      refine ⟨hQ q s hq hs, hLtail, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with h | hd'
      · subst h; exact hl
      rcases List.mem_cons.mp hd' with h | hd''
      · subst h; exact hW q s hq hs
      · exact hRtail d hd''

/-- **N 步不變式**：良組態沿軌道恆良。 -/
theorem gStepRL_iterate_wf (δq δw : ℕ → ℕ → ℕ) (move : ℕ → ℕ → Bool) (Q k : ℕ)
    (hQ : ∀ q s, q < Q → s < k → δq q s < Q)
    (hW : ∀ q s, q < Q → s < k → δw q s < k)
    (c : GCfg) (hc : wfCfg Q k c) :
    ∀ n : ℕ, wfCfg Q k ((gStepRL δq δw move)^[n] c) := by
  intro n
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact gStepRL_wf δq δw move Q k hQ hW _ ih

/-! ## plateau 假設 discharge + N 步精確模擬 -/

/-- **★M49 的 4 條 plateau 假設全部 discharge★**：良組態 + headroom base ⟹ `sigmaRL_exact`
無 plateau 假設版（只剩良編碼 + `(k−1)/(K−1) ≤ w`）。 -/
theorem sigmaRL_exact_of_wf (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (q l₀ s : ℕ) (L' R' : List ℕ)
    (hwf : wfCfg Q k ⟨q, l₀ :: L', s :: R'⟩) :
    sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w
        (gEnc K ⟨q, l₀ :: L', s :: R'⟩)
      = gEnc K (gStepRL δqN δwN moveB ⟨q, l₀ :: L', s :: R'⟩) := by
  obtain ⟨hq, hL, hR⟩ := hwf
  have hs : s < k := hR s List.mem_cons_self
  have hl : l₀ < k := hL l₀ List.mem_cons_self
  have hRtail : digitsLt k R' := fun d hd => hR d (List.mem_cons_of_mem s hd)
  have hLtail : digitsLt k L' := fun d hd => hL d (List.mem_cons_of_mem l₀ hd)
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    linarith
  obtain ⟨hloR, hhiR⟩ := read_plateau_of_headroom k K hk hK s R' hRtail hwhead
  obtain ⟨hloL, hhiL⟩ := read_plateau_of_headroom k K hk hK l₀ L' hLtail hwhead
  exact sigmaRL_exact δqN δwN moveB Q K hw0 hw1 hK0 q hq s (lt_of_lt_of_le hs hkK)
    l₀ (lt_of_lt_of_le hl hkK) L' R' hloR hhiR hloL hhiL

/-- 兩堆疊非空（List 版誠實邊界；G4e stream 編碼解）。 -/
def bothNonempty (c : GCfg) : Prop := c.L ≠ [] ∧ c.R ≠ []

/-- **★G5 HEADLINE：玩具 TM 的 N 步精確模擬★**：良組態 + headroom base + 軌道兩堆疊恆非空 ⟹
`σ^[n](gEnc c) = gEnc(step^[n] c)` **字面相等**（M48/M49 的單步精確抬到任意 N 步）。 -/
theorem sigmaRL_iterate_exact (δqN δwN : ℕ → ℕ → ℕ) (moveB : ℕ → ℕ → Bool) (Q k K : ℕ)
    (hk : 1 ≤ k) (hkK : k ≤ K) (hK : 1 < K)
    (hQ : ∀ q s, q < Q → s < k → δqN q s < Q)
    (hW : ∀ q s, q < Q → s < k → δwN q s < k)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hwhead : ((k : ℝ) - 1) / ((K : ℝ) - 1) ≤ w)
    (c : GCfg) (hwf : wfCfg Q k c) (n : ℕ)
    (hne : ∀ i, i < n → bothNonempty ((gStepRL δqN δwN moveB)^[i] c)) :
    (sigmaRL (fun a b => (δqN a b : ℝ)) (fun a b => (δwN a b : ℝ))
        (fun a b => if moveB a b then (1 : ℝ) else 0) Q K w)^[n] (gEnc K c)
      = gEnc K ((gStepRL δqN δwN moveB)^[n] c) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun i hi => hne i (Nat.lt_succ_of_lt hi))]
    have hwfm : wfCfg Q k ((gStepRL δqN δwN moveB)^[m] c) :=
      gStepRL_iterate_wf δqN δwN moveB Q k hQ hW c hwf m
    have hnem : bothNonempty ((gStepRL δqN δwN moveB)^[m] c) := hne m (Nat.lt_succ_self m)
    rcases hcm : (gStepRL δqN δwN moveB)^[m] c with ⟨q', L2, R2⟩
    rw [hcm] at hwfm hnem
    match L2, R2 with
    | [], _ => exact absurd rfl hnem.1
    | _ :: _, [] => exact absurd rfl hnem.2
    | l₀ :: L', s :: R' =>
      exact sigmaRL_exact_of_wf δqN δwN moveB Q k K hk hkK hK hw0 hw1 hwhead
        q' l₀ s L' R' hwfm

end FluidTuring
