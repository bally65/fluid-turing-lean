import FluidTuringLean.M3e_FixedTM
import FluidTuringLean.M6_EulerTuring

/-!
# Module 8 — 固定頭字面機 → 連續流（C-δ splice 層）

方案 C 的 splice 層：把 M3e 建的固定頭可逆 BitTM 餵進 M6 已證的
`reversibleTM_suspension_simulates`（任意可逆 BitTM → 連續流），得字面機的流。

**對抗設計艦隊 wf_a19b206c-eb0 三驗一致點名**：unconditional 半（可逆 BitTM → 流）
**立即可建**（literal copy of `bennettTM_suspension_simulates`），因 `ofPerm_reversible`
免費給可逆性。本模組先落地走位引擎 `trackWalkTM` 的流連接，確認 splice 路徑對固定頭
家族成立；未來完整宏步機器（走位可達性歸納 + deposit soundness 收尾後）同法接流。
-/

namespace FluidTuring

/-- **軌選擇走位機器 → 連續流**（C-δ splice 路徑確認）：`trackWalkTM t`（固定頭字面機的
走位引擎、`ofPerm` 建的真可逆 BitTM）的組態動力學被緊空間上連續 ℝ-流經單射編碼模擬。
= 可逆性（`ofPerm_reversible` 免費）→ `reversibleTM_suspension_simulates` 一次接上流。
確認固定頭家族的 splice 路徑；完整宏步機器同法接流。 -/
theorem trackWalkTM_suspends (t : Fin 4) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X)
      (F : ContinuousFlowOn X) (enc : (trackWalkTM t).Cfg → X),
      Simulates F (trackWalkTM t).step enc :=
  reversibleTM_suspension_simulates (trackWalkTM t) (trackWalkTM_reversible t)

end FluidTuring
