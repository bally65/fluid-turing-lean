import FluidTuringLean.M29_MtrFlow

/-!
# Module 30 — 通用 TM2 組態的停機介面（M_tr 本體 4b-5b-B 起手）

4b-5b-B = 兌現 M29 `hcorr`（reduced TM0-Bool 機器的 `eval` 停機 ⟺ `code.eval` 停機）。
mathlib **不預先組合**化約鏈，且 `TM2to1.tr_eval_dom` 用泛型 `TM2.init`、M16 用具體
`PartrecToTM2.init`——需在**組態層**（`tr_respects`）手接，且從具體 init 手建 `TrCfg`。

本塊起手：把 M16 的通用機器停機（`tm2_univ_wiring`，`totalize` 形式）抬到**組態層 `eval`**：
暴露具體 TM2 組態 `c0 code = PartrecToTM2.init cu [encode code]`、`StateTransition.eval` 形式，
逐 code 對應 `code.eval n₀`。⟹ `hcorr` 歸約到「化約鏈從此具體 TM2 組態保停機」。

**注意（審計後）**：`tm2_config_halts_iff_code` 是**獨立引理、不在封頂 `fluid_blowup_undecidable`
的證明樹上**——M33 為了暴露通用碼 `cu`（供 supports/init-label 穿線）**重推導**了同樣的 `cu` 橋
（`exists_code` + `tr_eval` + `hcu`），未直接引用本引理。本引理保留為該接線的清晰記錄/獨立版本。
-/

namespace FluidTuring

open Nat.Partrec Turing.PartrecToTM2

/-- **通用 TM2 組態停機介面**：存在具體 TM2 組態族 `c0`（= `PartrecToTM2.init cu [encode code]`），
其 `StateTransition.eval (TM2.step tr)` 停機逐 code 對應 `code.eval n₀` 停機。
= M16 `tm2_univ_wiring` 的組態層 `eval` 版（`totalize_halts_iff_eval_dom` 抬升）。 -/
theorem tm2_config_halts_iff_code (n₀ : ℕ) :
    ∃ c0 : Nat.Partrec.Code → Cfg',
      ∀ code : Nat.Partrec.Code,
        (StateTransition.eval (Turing.TM2.step tr) (c0 code)).Dom ↔ (code.eval n₀).Dom := by
  have hf : Partrec fun m : ℕ ↦
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code m) n₀ :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const n₀)
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨fun code ↦ init cu [Encodable.encode code], fun code ↦ ?_⟩
  rw [← totalize_halts_iff_eval_dom, tm2_halts_iff_code_eval_dom]
  have hv := hcu (Encodable.encode code ::ᵥ List.Vector.nil)
  simp only [List.Vector.head_cons, Denumerable.ofNat_encode] at hv
  have hv' : cu.eval [Encodable.encode code] = pure <$> code.eval n₀ := hv
  rw [hv']
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
    obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).mp hb
    exact Part.dom_iff_mem.mpr ⟨a, ha⟩
  · intro h
    exact Part.dom_iff_mem.mpr ⟨pure ((code.eval n₀).get h), Part.mem_map _ (Part.get_mem h)⟩

end FluidTuring
