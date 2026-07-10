import FluidTuringLean.M13_SmoothSwitch
import FluidTuringLean.M10_BlowupUndecidable

/-!
# Module 34 — 字面有限時間 blowup 不可判定（reduction-level）

**動機（審計後，2026-07-10）**：M33 封頂實際證的是**緊空間到達性**——緊空間**無字面爆破**。
本塊把 headline 升級到**字面有限時間 blowup**：用 M13 的**真平滑 Riccati 爆破** `smoothSwitchSol`
（`z' = h(t) z²`、有限時間 `Tendsto … atTop`），組一個實值軌跡族 `blowupFamily`，使其**字面爆破
⟺ code 停機**，故字面 blowup 偵測**無演算法可判定**。

**誠實界線（範圍）**：
- `smoothSwitchSol` 的爆破是**真的**（真 C^∞、真 Riccati、真有限時間 `Tendsto atTop`，M13 全證）。
- `blowupFamily` 這個**族**由停機謂詞 case-split 組裝（reduction-level，同 M10
  `finite_time_blowup_undecidable` 的誠實框架）——它證「字面爆破偵測 ≥ 停機」。
- **真·單一自治耦合向量場**（懸掛流 × Riccati 座標、`z'=g(X)z²`、**含逆向**「不停機 ⟹ z 有界不爆」）
  = M10 已標的 **paper-blocked** 部分（mathlib 缺耦合 ODE 爆破分析 / analog computation）。正向
  「停機 ⟹ 真平滑爆破」在 M13 `halts_imp_smooth_blowup` 已證；逆向的自治 ODE 有界性分析超出 mathlib。
  故 reduction-level 是本方向的**誠實無條件天花板**。
-/

namespace FluidTuring

open Nat.Partrec

/-- **有限時間 blowup**：某有限時刻 `T` 前，函數 `→ +∞`（極大存在區間有界的解逃逸）。 -/
def BlowsUpInFiniteTime (f : ℝ → ℝ) : Prop :=
  ∃ T : ℝ, Filter.Tendsto f (nhdsWithin T (Set.Iio T)) Filter.atTop

/-- `smoothSwitchSol t₀` 字面有限時間爆破（在 `t₀+1`）——M13 真平滑 Riccati。 -/
theorem smoothSwitchSol_blowsUp (t₀ : ℝ) : BlowsUpInFiniteTime (smoothSwitchSol t₀) :=
  ⟨t₀ + 1, smoothSwitchSol_tendsto_atTop t₀⟩

/-- 常數函數**不**有限時間爆破（趨於有限值、非 `atTop`）。 -/
theorem const_not_blowsUp (a : ℝ) : ¬ BlowsUpInFiniteTime (fun _ ↦ a) := by
  rintro ⟨T, hT⟩
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds hT

open Classical in
/-- **字面 blowup 軌跡族**（reduction-level）：`code` 停機 ⟹ 真平滑 Riccati 爆破，否則常數不爆。 -/
noncomputable def blowupFamily (n : ℕ) (code : Code) : ℝ → ℝ :=
  if (code.eval n).Dom then smoothSwitchSol 1 else fun _ ↦ 1

/-- **軌跡族字面爆破 ⟺ 停機**。 -/
theorem blowupFamily_blowsUp_iff (n : ℕ) (code : Code) :
    BlowsUpInFiniteTime (blowupFamily n code) ↔ (code.eval n).Dom := by
  by_cases hc : (code.eval n).Dom
  · have he : blowupFamily n code = smoothSwitchSol 1 := if_pos hc
    rw [he]
    exact ⟨fun _ ↦ hc, fun _ ↦ smoothSwitchSol_blowsUp 1⟩
  · have he : blowupFamily n code = fun _ ↦ 1 := if_neg hc
    rw [he]
    exact ⟨fun h ↦ absurd h (const_not_blowsUp 1), fun h ↦ absurd h hc⟩

/-- **★字面有限時間 blowup 不可判定★（reduction-level）**：存在實值軌跡族 `blowupFamily n`，其
**真·有限時間 blowup**（`BlowsUpInFiniteTime`，M13 真平滑 Riccati `Tendsto atTop`）逐 code
等價 `code.eval n` 停機，故**無演算法判定該軌跡是否有限時間爆破**。

= M13 真爆破原子 + M10 `finite_time_blowup_undecidable` 還原框架。把 M33 的「到達性」headline
升到**字面爆破**（reduction-level）；真·單一自治耦合向量場含逆向有界性 = paper-blocked（見檔頭）。 -/
theorem literal_blowup_undecidable (n : ℕ) :
    ¬ ComputablePred (fun code : Code => BlowsUpInFiniteTime (blowupFamily n code)) :=
  finite_time_blowup_undecidable (blowupFamily n) BlowsUpInFiniteTime n
    (blowupFamily_blowsUp_iff n)

end FluidTuring
