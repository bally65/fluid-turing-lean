import Mathlib.Computability.Halting

/-!
# Module 10 — 有限時間 blowup 偵測不可判定（M9 的 blowup 側姊妹）

**動機**：本專案已把「停機 → 流軌道可達性」機器化（M9 `halts_imp_orbitReaches`）——那是
在**緊空間、時間演化有界**的世界裡的不可判定性。文獻另有一條**微分/局部**側的結果：
把停機編進「連續時間系統會不會在**有限時間 blowup**（解逃逸、極大存在區間有界）」。

**已知文獻（真結果、非本檔證）**：
- Graça–Buescu–Campagnolo 2009（Trans. AMS 361(6)）：判定可計算解析 ODE 初值問題是否
  有限時間 blowup（極大區間有界）vs 全域存在 = **演算法不可判定**（停機還原）。
- Huynh 2024（arXiv:2410.01455）：顯式構造光滑向量場，**「有限時間 blowup ⟺ 通用 TM 停機」**。

這些用**特製解析/光滑向量場**（不是物理 PDE 如 Navier–Stokes；真 NS 版卡在與 Tao
blowup 綱領同一道 supercriticality 牆）。**mathlib 缺**「TM → 光滑向量場、blowup⟺停機」
的 analog-computation 構造（多月工程）。

**本模組做的（誠實界線）**：把上述結果的**不可判定性還原邏輯**機器化——複用 mathlib
已證的 `ComputablePred.halting_problem`（停機不可判定），把 Graça/Huynh 的「blowup ⟺ 停機」
**當明寫假設**（同主定理的方案 A 條件化手法）。**機器證出**：只要某族連續時間系統的
「有限時間 blowup」與「停機」逐點吻合，則**無演算法判定 blowup**。真幾何/真 ODE 構造
（讓假設成立）是外部、paper-blocked 的部分——**不冒充**。據查，proof assistant 裡
形式化「undecidability of finite-time blowup」尚無先例，此為本專案交叉點的新貢獻雛形。
-/

namespace FluidTuring

open Nat.Partrec

/-- **★有限時間 blowup 偵測不可判定（條件還原）★**：給定一族由圖靈機 code `c` 索引的
連續時間軌跡 `sys c : ℝ → X`，與「有限時間 blowup」謂詞 `blowsUp`；**若**（Graça/Huynh
的 ODE 構造所實現的）`blowsUp (sys c) ⟺ 機器 c 於輸入 n 停機`，**則**沒有可計算謂詞
判定 blowup。

證明 = 該謂詞逐點等於停機謂詞（`funext`+`propext`），複用 mathlib 已證的
`ComputablePred.halting_problem`。M9 是「停機→可達性」（積分/全域側）；本定理是
「停機⟺blowup→不可判定」（微分/局部側）。 -/
theorem finite_time_blowup_undecidable {X : Type} (sys : Code → ℝ → X)
    (blowsUp : (ℝ → X) → Prop) (n : ℕ)
    (hreduce : ∀ c : Code, blowsUp (sys c) ↔ (c.eval n).Dom) :
    ¬ ComputablePred (fun c : Code => blowsUp (sys c)) := by
  have hcoe : (fun c : Code => blowsUp (sys c)) = (fun c : Code => (c.eval n).Dom) :=
    funext fun c => propext (hreduce c)
  rw [hcoe]
  exact ComputablePred.halting_problem n

/-- 對稱推論：「有限時間 blowup 的**否定**（全域存在 / 不爆）」同樣不可判定——
其可計算性會蘊含停機的可計算性。（`ComputablePred` 對補集封閉。） -/
theorem global_existence_undecidable {X : Type} (sys : Code → ℝ → X)
    (blowsUp : (ℝ → X) → Prop) (n : ℕ)
    (hreduce : ∀ c : Code, blowsUp (sys c) ↔ (c.eval n).Dom) :
    ¬ ComputablePred (fun c : Code => ¬ blowsUp (sys c)) := by
  intro hcomp
  exact finite_time_blowup_undecidable sys blowsUp n hreduce
    (hcomp.not.of_eq (fun _ ↦ not_not))

end FluidTuring
