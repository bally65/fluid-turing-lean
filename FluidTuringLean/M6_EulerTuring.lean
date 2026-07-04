import FluidTuringLean.M3b_ReversibleTM
import FluidTuringLean.M5_ReebInterface

/-!
# Module 6 — 主定理：Euler 穩態解的圖靈完備性（Euler-only 誠實版）

**範圍決策（2026-07-04，使用者選定方向 B）**：本模組只主張
**Euler 穩態解**（Beltrami 場）的圖靈完備性，對應
Cardona–Miranda–Peralta-Salas–Presas 2021（PNAS）的原始設定。

**明確不主張**（v0.3 前身草案中被判定為錯誤或嚴重超譯的斷言，永久移除）：

1. ~~「調和場 `Δ_H X = 0` ⟹ Navier–Stokes 黏滯耗散為零」~~ —— 假。
   NS 耗散率是 `ν ∫ |∇u|²`，非 `ν ∫ |Δu|²`；由 Weitzenböck
   `Δ_H = ∇*∇ + Ric`，「調和 ⟹ 平行（`∇X = 0`）」只在 Ricci-flat
   流形成立，一般 Hodge-admissible 3-流形上 `Ric ≠ 0`、耗散非零。
2. ~~「圖靈完備性對任意黏滯性 ν > 0 免疫」~~ —— 超譯。
   Beltrami 場是 Euler 穩態，通常不是 NS 穩態（`νΔu ≠ 0` 無外力不可抵銷）。

依硬規則 5：此「不可證／為假」判定不因後續壓力反轉。若未來要碰 NS，
合法途徑只有：(A) 限制 Ricci-flat（如平坦 T³）或 (C) forced-NS 外力吸收
`νΔu` —— 需重新開範圍決策，不得靜默放寬本檔假設。

sorry 數：1（`euler_flow_turing_complete`，PAPER-BLOCKED:
Cardona–Miranda–Peralta-Salas–Presas 2021, Theorem 1）。
-/

namespace FluidTuring

/-- 流 `F` 經由單射編碼 `enc` 模擬離散動力系統 `step`：
每個組態的一步轉移都被某正時間的流實現。
（「圖靈完備」= 對通用圖靈機的組態轉移成立此謂詞；
mathlib 尚無通用機定理，故以「模擬任意可編碼離散系統」表述，
與 Cardona et al. 經 generalized shift 模擬任意 TM 的路線一致。） -/
def Simulates {M : Type*} [TopologicalSpace M] (F : ContinuousFlowOn M)
    {Γ : Type*} (step : Γ → Γ) (enc : Γ → M) : Prop :=
  Function.Injective enc ∧
    ∀ c : Γ, ∃ t : ℝ, 0 < t ∧ F.φ t (enc c) = enc (step c)

/-- 迭代引理：模擬單步 ⟹ 軌道以正時間實現**任意 `n+1` 步**轉移
（時間沿流群律相加）。把「一步模擬」升級成「整條軌道模擬」。 -/
theorem Simulates.iterate {M : Type*} [TopologicalSpace M] {F : ContinuousFlowOn M}
    {Γ : Type*} {step : Γ → Γ} {enc : Γ → M}
    (h : Simulates F step enc) (c : Γ) (n : ℕ) :
    ∃ t : ℝ, 0 < t ∧ F.φ t (enc c) = enc (step^[n + 1] c) := by
  induction n with
  | zero => simpa using h.2 c
  | succ m ih =>
      obtain ⟨t₁, ht₁, hφ₁⟩ := ih
      obtain ⟨t₂, ht₂, hφ₂⟩ := h.2 (step^[m + 1] c)
      exact ⟨t₂ + t₁, by linarith, by
        rw [F.map_add, hφ₁, hφ₂]
        exact congrArg enc (Function.iterate_succ_apply' step (m + 1) c).symm⟩

/-- **主定理（Euler-only，PAPER-BLOCKED sorry）** —— 誠實範圍陳述：

> 對任意可編碼組態空間 `Γ` 上的轉移函數 `step`，存在緊緻空間 `M`、
> 其上的向量微積分詮釋 `V`、及 Beltrami 場 `u`（= Euler 穩態解，
> 見 M5 `IsBeltrami`），使 `u` 的積分流模擬 `step`。

紙面證明鏈：TM → generalized shift → 康托爾編碼（M3）→ 圓環面上的
area-preserving diffeo → 懸掛（M4）→ S³ 上的 Reeb 場（M5, Lemma B）
→ Beltrami 場 = Euler 穩態解。

分類：`paper-blocked`，依賴 [Cardona–Miranda–Peralta-Salas–Presas 2021,
"Constructing Turing complete Euler flows in dimension 3", PNAS 118(19),
Theorem 1]，經由 M5 的 Etnyre–Ghrist 對應。前四模組的離散→連續管線
（編碼、懸掛）已在 M1–M4 零 sorry 建立；缺口全部集中在接觸幾何詮釋層。 -/
theorem euler_flow_turing_complete {Γ : Type} [Encodable Γ] (step : Γ → Γ) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (V : VectorCalculus3 M) (u : V.Vec) (enc : Γ → M),
      V.IsBeltrami u ∧ Simulates (V.flowOf u) step enc := by
  sorry

/-! ## 已證的離散→連續下半層（零 sorry）

主定理的下半層不必等接觸幾何：M4 的映射環面給出**全證**的版本 ——
任何緊緻空間上的可逆離散動力系統，都被某緊緻空間上的連續 ℝ-流模擬。
主定理與此的差距**只剩**「該流可取為 Euler 穩態（Beltrami）流」，
即 M5 的接觸幾何詮釋層。 -/

/-- 懸掛流模擬離散系統（無條件、已證）：對任何 `f : X → X`，
映射環面上的懸掛時間-1 映射在切片 `t = 0` 上實現 `f`。 -/
theorem suspension_simulates {X : Type*} (f : X → X) (x : X) :
    MappingTorus.suspFlow 1 (MappingTorus.mk f (x, 0)) = MappingTorus.mk f (f x, 0) :=
  MappingTorus.suspFlow_one_realizes x

universe u

/-- **下半層主定理（全證、零 sorry）**：緊緻空間 `X` 上的任何同胚 `e`，
都存在緊緻空間 `M` 上的連續 ℝ-流（`ContinuousFlowOn`，聯合連續 + 群律）
經單射編碼模擬 `e` 的離散動力學。

構造：`M = X` 的映射環面、流 = 懸掛流、編碼 = 切片嵌入 `x ↦ [x, 0]`。
單射性用 M4 的完整不變量；緊緻性用 `X × [0,1]` 滿射像；
聯合連續性用開商映射（不需 Whitehead 定理）。 -/
theorem suspension_flow_simulates {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (e : X ≃ₜ X) :
    ∃ (M : Type u) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (F : ContinuousFlowOn M) (enc : X → M),
      Simulates F (⇑e) enc := by
  refine ⟨MappingTorus ⇑e, inferInstance, MappingTorus.compactSpace e.toEquiv,
    { φ := MappingTorus.suspFlow
      continuous := MappingTorus.continuous_suspFlow_uncurried e
      map_zero := MappingTorus.suspFlow_zero
      map_add := MappingTorus.suspFlow_add },
    fun x ↦ MappingTorus.mk ⇑e (x, 0), ?_, fun c ↦ ⟨1, one_pos, ?_⟩⟩
  · exact MappingTorus.mk_slice_injective e.toEquiv
  · exact MappingTorus.suspFlow_one_realizes c

/-! ### 實例：雙邊 full shift（generalized shift 的骨幹） -/

/-- 雙邊 full shift `σ : (ℤ → Bool) ≃ₜ (ℤ → Bool)`，`(σ s) n = s (n+1)`。
可逆（左移的逆是右移）、雙向連續（乘積拓撲）。 -/
def fullShift : (ℤ → Bool) ≃ₜ (ℤ → Bool) where
  toFun s n := s (n + 1)
  invFun s n := s (n - 1)
  left_inv s := funext fun n ↦ by simp
  right_inv s := funext fun n ↦ by simp
  continuous_toFun := continuous_pi fun n ↦ continuous_apply (n + 1)
  continuous_invFun := continuous_pi fun n ↦ continuous_apply (n - 1)

/-- **全證實例**：雙邊 full shift 被緊緻空間上的連續流模擬。
這正是 Cardona et al. 構造鏈「generalized shift → 流」一步的
拓撲動力學核心（缺的只是把流實現成 Euler/Beltrami 的幾何）。 -/
theorem fullShift_suspension_simulates :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (F : ContinuousFlowOn M) (enc : (ℤ → Bool) → M),
      Simulates F (⇑fullShift) enc :=
  suspension_flow_simulates fullShift

/-! ### Generalized shift（Moore 1990）→ 流：全證推論

M3 的 `GenShift` 把「有限視窗局部規則」結構化；可逆者經 `toHomeomorph`
變成 `(ℤ → Bool)` 的自同胚，直接餵入 `suspension_flow_simulates`。 -/

/-- `fullShift` 是 generalized shift 的平凡實例：空視窗、平移量常數 `1`、不改寫。 -/
def fullShiftGS : GenShift where
  window := ∅
  shiftAmt _ := 1
  rewrite s := s
  shiftAmt_local _ := rfl
  rewrite_local _ i hi := absurd hi (Finset.notMem_empty i)
  rewrite_off _ _ _ := rfl

@[simp] theorem fullShiftGS_apply : fullShiftGS.apply = ⇑fullShift := rfl

theorem fullShiftGS_reversible : fullShiftGS.Reversible := fullShift.bijective

/-- **推論（全證、零 sorry）**：任何**可逆** generalized shift（Moore 1990）
都被緊緻空間上的連續 ℝ-流經單射編碼模擬。這把 Cardona et al. 構造鏈的
「generalized shift → 流」一步從 full shift 骨幹升級到完整的局部規則類；
與主定理的差距只剩幾何實現（M5 接觸幾何詮釋層）與
TM → 可逆 GS 的 Bennett 可逆化（後續工作，見 M3）。 -/
theorem genShift_suspension_simulates (Φ : GenShift) (h : Φ.Reversible) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M)
      (F : ContinuousFlowOn M) (enc : (ℤ → Bool) → M),
      Simulates F Φ.apply enc :=
  suspension_flow_simulates (Φ.toHomeomorph h)

/-! ### 可逆圖靈機（M3b）→ 流：全證推論

M3b 的 `BitTM.toGenShift` 把機器單步實現為 generalized shift，
可逆性沿雙射編碼 `encCfg` 搬運；此處再經 `genShift_suspension_simulates`
把**機器本身的組態動力學**（不只編碼側）接到連續流。 -/

/-- **推論（全證、零 sorry）**：任何**可逆**位元圖靈機（M3b `BitTM`，
`step` 雙射）的組態動力學，都被緊緻空間上的連續 ℝ-流經單射編碼模擬。
編碼 = `enc ∘ encCfg`（機器組態 → 康托爾序列 → 映射環面）。
與主定理的差距只剩：幾何實現（M5 接觸幾何詮釋層，paper-blocked）與
不可逆機器的 Bennett 可逆化（M3b 里程碑 B，部分完成、缺口誠實標示）。 -/
theorem reversibleTM_suspension_simulates (M : BitTM) (h : M.Reversible) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X)
      (F : ContinuousFlowOn X) (enc : M.Cfg → X),
      Simulates F M.step enc := by
  obtain ⟨X, iT, iC, F, enc, hinj, hsim⟩ :=
    genShift_suspension_simulates M.toGenShift (h.toGenShift)
  refine ⟨X, iT, iC, F, enc ∘ ⇑M.encCfg, hinj.comp M.encCfg.injective, fun c ↦ ?_⟩
  obtain ⟨t, ht, hφ⟩ := hsim (M.encCfg c)
  refine ⟨t, ht, ?_⟩
  have hstep : M.toGenShift.apply (M.encCfg c) = M.encCfg (M.step c) := by
    rw [M.toGenShift_apply]
    exact congrArg (fun x ↦ M.pack (M.step x)) (M.encCfg.left_inv c)
  calc F.φ t ((enc ∘ ⇑M.encCfg) c)
      = enc (M.toGenShift.apply (M.encCfg c)) := hφ
    _ = enc (M.encCfg (M.step c)) := by rw [hstep]
    _ = (enc ∘ ⇑M.encCfg) (M.step c) := rfl

/-- **具體實例（全證）**：受控反閘機 `cnotTM`（M3b，`decide` 驗證局部可逆）
被緊緻空間上的連續 ℝ-流模擬。整條「具體機器 → 局部可逆檢查 → 雙射 →
generalized shift → 同胚 → 懸掛流」管線的端到端見證。 -/
theorem cnotTM_suspension_simulates :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X)
      (F : ContinuousFlowOn X) (enc : BitTM.cnotTM.Cfg → X),
      Simulates F BitTM.cnotTM.step enc :=
  reversibleTM_suspension_simulates BitTM.cnotTM BitTM.cnotTM_reversible

end FluidTuring
