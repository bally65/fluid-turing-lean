import FluidTuringLean.M3b_ReversibleTM

/-!
# Module 3c — Bennett 可逆化（動力學層）：history conveyor

M3b 的 `bennett_not_surjective` 證死了抽象 history 構造（`X × List X`）永不滿射：
`(x₀, [])` 沒有前像，因為 `List` 有「空歷史」這個角點。本模組把歷史容器換成
**雙向無限記錄流** `ℤ → V`（輸送帶），在動力學層把 Bennett 缺口封死：

* `histConveyor`：任何 `X × V` 上的雙射 `G` 升級成 `X × (ℤ → V)` 上的**雙射**。
  一步 = 讀流位 `0` 當緩衝入、`G` 更新、記錄從流位 `-1` 吐出、整條流下移一格。
  「空歷史」點不存在 —— 每點都有無限的過去容量，滿射由顯式逆映射直接成立。
* `BitTM.bufferedStep`：**Feistel 輪** —— 任意（不可逆）位元機的單步配一格緩衝
  `(r, b)` 變成顯式雙射：新狀態 := `next ⊕ r`（逐位）、寫入位 := `write ⊕ b`、
  緩衝出 := 被丟棄的 `(q, t 0)`。緩衝出原封不動，一切可由它重建 ⟹ 可逆；
  緩衝空白（`blankRec`）時第一分量精確 = `M.step`（`bufferedStep_blank`）。
* `BitTM.bennettAut`：`histConveyor M.bufferedStep` —— 任意位元機的組態動力學
  升級成 `Cfg × 歷史流` 上的雙射。`bennettAut_iterate`：從空白歷史出發
  `n` 步 conveyor = `n` 步機器（**無時間膨脹**），歷史分量誠實外顯為存在量詞。
* `BitTM.bennettHomeo`：`Cfg × 歷史流` 是緊 Hausdorff（有限離散 × 康托爾型乘積），
  正向連續（`continuous_bufferedStep`：每個輸出座標只讀有限筆離散資料）⟹
  自同胚。可直接餵 M6 懸掛管線（`bitTM_suspension_simulates`）。

## 與機器級 shuttle 構造的關係（誠實界線）

本模組在**動力學層**完成 Bennett 1973 的核心（history-keeping 可逆化 + 精確模擬 +
垃圾誠實外顯）：產物是緊空間自同胚，**不是** `BitTM`。字面的
`bennettTM : BitTM → BitTM`（歷史寫進帶的奇偶軌、讀寫頭走位到歷史前沿）需要
shuttle 控制流，是後續工作 —— 其可逆性那一半已由 M3b `ofPerm` 引擎付清，
剩模擬正確性的走位工程；見 README 攻擊計畫。

本檔零 sorry。
-/

namespace FluidTuring

noncomputable section

/-! ## Bool 對合小引理 -/

private theorem xor_xor_cancel_right (a b : Bool) : xor (xor a b) a = b := by
  cases a <;> cases b <;> rfl

private theorem xor_xor_cancel_left (a b : Bool) : xor a (xor b a) = b := by
  cases a <;> cases b <;> rfl

/-! ## 抽象層：history conveyor -/

section Conveyor

variable {X V : Type*}

/-- conveyor 正向：讀流位 `0` 當緩衝入、`G` 更新、記錄寫到流位 `-1`、
整條流下移一格。 -/
def conveyorFwd (G : (X × V) ≃ (X × V)) (p : X × (ℤ → V)) : X × (ℤ → V) :=
  ((G (p.1, p.2 0)).1,
   fun k ↦ if k = -1 then (G (p.1, p.2 0)).2 else p.2 (k + 1))

/-- conveyor 逆向：記錄從流位 `-1` 收回、`G.symm` 還原、緩衝放回流位 `0`、
整條流上移一格。 -/
def conveyorBwd (G : (X × V) ≃ (X × V)) (p : X × (ℤ → V)) : X × (ℤ → V) :=
  ((G.symm (p.1, p.2 (-1))).1,
   fun k ↦ if k = 0 then (G.symm (p.1, p.2 (-1))).2 else p.2 (k - 1))

theorem conveyorBwd_conveyorFwd (G : (X × V) ≃ (X × V)) (p : X × (ℤ → V)) :
    conveyorBwd G (conveyorFwd G p) = p := by
  obtain ⟨x, η⟩ := p
  simp only [conveyorFwd, conveyorBwd, reduceIte, Prod.mk.eta, Equiv.symm_apply_apply]
  refine Prod.ext rfl (funext fun k ↦ ?_)
  dsimp only
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_pos rfl]
  · rw [if_neg hk, if_neg (by omega : ¬k - 1 = -1)]
    exact congrArg η (by omega)

theorem conveyorFwd_conveyorBwd (G : (X × V) ≃ (X × V)) (p : X × (ℤ → V)) :
    conveyorFwd G (conveyorBwd G p) = p := by
  obtain ⟨y, θ⟩ := p
  simp only [conveyorFwd, conveyorBwd, reduceIte, Prod.mk.eta, Equiv.apply_symm_apply]
  refine Prod.ext rfl (funext fun k ↦ ?_)
  dsimp only
  rcases eq_or_ne k (-1) with rfl | hk
  · rw [if_pos rfl]
  · rw [if_neg hk, if_neg (by omega : ¬k + 1 = 0)]
    exact congrArg θ (by omega)

/-- **History conveyor**：`X × V` 上的雙射 `G` 升級成 `X × (ℤ → V)` 上的雙射。
過去（負側）只寫不讀、未來（非負側）源源供應新鮮緩衝。 -/
def histConveyor (G : (X × V) ≃ (X × V)) : (X × (ℤ → V)) ≃ (X × (ℤ → V)) where
  toFun := conveyorFwd G
  invFun := conveyorBwd G
  left_inv := conveyorBwd_conveyorFwd G
  right_inv := conveyorFwd_conveyorBwd G

@[simp] theorem histConveyor_apply (G : (X × V) ≃ (X × V)) (p : X × (ℤ → V)) :
    histConveyor G p = conveyorFwd G p := rfl

/-- 歷史流「未來側新鮮」：非負座標全是 `v₀`（尚未寫入記錄的空白）。 -/
def FreshFrom (v₀ : V) (η : ℤ → V) : Prop := ∀ k : ℤ, 0 ≤ k → η k = v₀

theorem freshFrom_const (v₀ : V) : FreshFrom v₀ fun _ ↦ v₀ := fun _ _ ↦ rfl

/-- conveyor 一步（新鮮側）：工作分量走 `f`、新鮮性保持、垃圾誠實外顯。 -/
theorem histConveyor_step {f : X → X} {v₀ : V} {G : (X × V) ≃ (X × V)}
    (hG : ∀ x, (G (x, v₀)).1 = f x) (x : X) {η : ℤ → V} (hη : FreshFrom v₀ η) :
    ∃ η' : ℤ → V, histConveyor G (x, η) = (f x, η') ∧ FreshFrom v₀ η' := by
  have h0 : η 0 = v₀ := hη 0 le_rfl
  refine ⟨fun k ↦ if k = -1 then (G (x, η 0)).2 else η (k + 1), ?_, fun k hk ↦ ?_⟩
  · refine Prod.ext ?_ rfl
    change (G (x, η 0)).1 = f x
    rw [h0]
    exact hG x
  · dsimp only
    rw [if_neg (by omega : ¬k = -1)]
    exact hη (k + 1) (by omega)

/-- conveyor `n` 步（新鮮側）：工作分量精確走 `f^[n]` —— 無時間膨脹。 -/
theorem histConveyor_iterate {f : X → X} {v₀ : V} {G : (X × V) ≃ (X × V)}
    (hG : ∀ x, (G (x, v₀)).1 = f x) (n : ℕ) :
    ∀ (x : X) (η : ℤ → V), FreshFrom v₀ η →
      ∃ η' : ℤ → V, (⇑(histConveyor G))^[n] (x, η) = (f^[n] x, η') ∧ FreshFrom v₀ η' := by
  induction n with
  | zero => exact fun x η hη ↦ ⟨η, rfl, hη⟩
  | succ n ih =>
      intro x η hη
      obtain ⟨η₁, hstep, hfresh₁⟩ := histConveyor_step hG x hη
      obtain ⟨η', hit, hfresh'⟩ := ih (f x) η₁ hfresh₁
      refine ⟨η', ?_, hfresh'⟩
      rw [Function.iterate_succ_apply, hstep, hit, Function.iterate_succ_apply]

section Topology

variable [TopologicalSpace X] [TopologicalSpace V]

/-- conveyor 正向連續：工作分量與記錄輸出經 `G` 連續，其餘座標是平移投影。 -/
theorem continuous_conveyorFwd (G : (X × V) ≃ (X × V)) (hG : Continuous ⇑G) :
    Continuous (conveyorFwd G) := by
  have hread : Continuous fun p : X × (ℤ → V) ↦ G (p.1, p.2 0) :=
    hG.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
  unfold conveyorFwd
  refine (continuous_fst.comp hread).prodMk (continuous_pi fun k ↦ ?_)
  rcases eq_or_ne k (-1) with rfl | hk
  · have h2 : Continuous fun p : X × (ℤ → V) ↦ (G (p.1, p.2 0)).2 := hread.snd
    simpa using h2
  · have h2 : Continuous fun p : X × (ℤ → V) ↦ p.2 (k + 1) :=
      (continuous_apply (k + 1)).comp continuous_snd
    simpa [hk] using h2

theorem continuous_histConveyor (G : (X × V) ≃ (X × V)) (hG : Continuous ⇑G) :
    Continuous ⇑(histConveyor G) :=
  continuous_conveyorFwd G hG

/-- 緊 Hausdorff 上 conveyor 是自同胚（逆向連續免費：緊到 T2 的連續雙射）。 -/
def histConveyorHomeo [CompactSpace X] [T2Space X] [CompactSpace V] [T2Space V]
    (G : (X × V) ≃ (X × V)) (hG : Continuous ⇑G) :
    (X × (ℤ → V)) ≃ₜ (X × (ℤ → V)) :=
  Continuous.homeoOfEquivCompactToT2 (f := histConveyor G) (continuous_histConveyor G hG)

@[simp] theorem histConveyorHomeo_apply [CompactSpace X] [T2Space X] [CompactSpace V]
    [T2Space V] (G : (X × V) ≃ (X × V)) (hG : Continuous ⇑G) :
    ⇑(histConveyorHomeo G hG) = ⇑(histConveyor G) := rfl

end Topology

end Conveyor

/-! ## 位元機的 Bennett 可逆化 -/

namespace BitTM

variable (M : BitTM)

/-- Bennett 記錄：一步被丟棄的資訊 `(舊狀態, 讀入位)`。 -/
abbrev HistRec : Type := (Fin M.m → Bool) × Bool

/-- 空白記錄（緩衝的「乾淨」值）。 -/
def blankRec : M.HistRec := (fun _ ↦ false, false)

/-- Feistel 帶緩衝單步的正向：緩衝入 `(r, b)`，新狀態 := `next ⊕ r`（逐位）、
寫入位 := `write ⊕ b`、帶照常平移；緩衝出 := 被丟棄的 `(q, t 0)`。 -/
def bufferedFwd (p : M.Cfg × M.HistRec) : M.Cfg × M.HistRec :=
  ((fun j ↦ xor (M.next p.1.1 (p.1.2 0) j) (p.2.1 j),
    fun k ↦ if k + (M.move p.1.1 (p.1.2 0)).toInt = 0
      then xor (M.write p.1.1 (p.1.2 0)) p.2.2
      else p.1.2 (k + (M.move p.1.1 (p.1.2 0)).toInt)),
   (p.1.1, p.1.2 0))

/-- Feistel 帶緩衝單步的逆向：緩衝出原封帶著 `(q, a)`，方向、寫入位、
整條帶全部由它重建。 -/
def bufferedBwd (p : M.Cfg × M.HistRec) : M.Cfg × M.HistRec :=
  ((p.2.1, fun k ↦ if k = 0 then p.2.2 else p.1.2 (k - (M.move p.2.1 p.2.2).toInt)),
   (fun j ↦ xor (p.1.1 j) (M.next p.2.1 p.2.2 j),
    xor (p.1.2 (-(M.move p.2.1 p.2.2).toInt)) (M.write p.2.1 p.2.2)))

theorem bufferedBwd_bufferedFwd (p : M.Cfg × M.HistRec) :
    M.bufferedBwd (M.bufferedFwd p) = p := by
  obtain ⟨⟨q, t⟩, r, b⟩ := p
  simp only [bufferedFwd, bufferedBwd]
  refine Prod.ext (Prod.ext rfl (funext fun k ↦ ?_)) (Prod.ext (funext fun j ↦ ?_) ?_)
  · dsimp only
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl]
    · rw [if_neg hk, if_neg (by omega : ¬k - (M.move q (t 0)).toInt +
        (M.move q (t 0)).toInt = 0)]
      exact congrArg t (by omega)
  · dsimp only
    exact xor_xor_cancel_right (M.next q (t 0) j) (r j)
  · dsimp only
    rw [if_pos (by omega : -(M.move q (t 0)).toInt + (M.move q (t 0)).toInt = 0)]
    exact xor_xor_cancel_right (M.write q (t 0)) b

theorem bufferedFwd_bufferedBwd (p : M.Cfg × M.HistRec) :
    M.bufferedFwd (M.bufferedBwd p) = p := by
  obtain ⟨⟨P, s⟩, q, a⟩ := p
  simp only [bufferedFwd, bufferedBwd, reduceIte]
  refine Prod.ext (Prod.ext (funext fun j ↦ ?_) (funext fun k ↦ ?_)) rfl
  · dsimp only
    exact xor_xor_cancel_left (M.next q a j) (P j)
  · dsimp only
    rcases eq_or_ne (k + (M.move q a).toInt) 0 with hz | hz
    · rw [if_pos hz]
      have hb : xor (M.write q a)
          (xor (s (-(M.move q a).toInt)) (M.write q a)) = s (-(M.move q a).toInt) :=
        xor_xor_cancel_left (M.write q a) (s (-(M.move q a).toInt))
      rw [hb]
      exact congrArg s (by omega)
    · rw [if_neg hz, if_neg hz]
      exact congrArg s (by omega)

/-- **Feistel 帶緩衝單步**：任意（不可逆）位元機單步配一格記錄緩衝後的
顯式雙射。可逆的機制：被 `M.step` 丟棄的 `(q, t 0)` 原封不動從緩衝吐出，
方向與寫入位可由它重算，帶的平移可逆。 -/
def bufferedStep : (M.Cfg × M.HistRec) ≃ (M.Cfg × M.HistRec) where
  toFun := M.bufferedFwd
  invFun := M.bufferedBwd
  left_inv := M.bufferedBwd_bufferedFwd
  right_inv := M.bufferedFwd_bufferedBwd

/-- 空白緩衝上的 bufferedStep：工作分量精確 = `M.step`，記錄分量吐出被丟棄的
`(q, t 0)`。Feistel 的 XOR 在空白緩衝上是恆等。 -/
theorem bufferedStep_blank (c : M.Cfg) :
    M.bufferedStep (c, M.blankRec) = (M.step c, (c.1, c.2 0)) := by
  obtain ⟨q, t⟩ := c
  refine Prod.ext (Prod.ext (funext fun j ↦ ?_) (funext fun k ↦ ?_)) rfl
  · exact Bool.xor_false (M.next q (t 0) j)
  · change (if k + (M.move q (t 0)).toInt = 0 then xor (M.write q (t 0)) false
      else t (k + (M.move q (t 0)).toInt)) = _
    rw [Bool.xor_false]
    rfl

/-! ### Bennett 自同構與模擬引理 -/

/-- **Bennett 可逆化（動力學層）**：任意位元機的組態動力學升級成
`Cfg × 歷史流` 上的**雙射**。 -/
def bennettAut : (M.Cfg × (ℤ → M.HistRec)) ≃ (M.Cfg × (ℤ → M.HistRec)) :=
  histConveyor M.bufferedStep

/-- 空白歷史流。 -/
def blankHist : ℤ → M.HistRec := fun _ ↦ M.blankRec

/-- **模擬引理（無時間膨脹）**：從空白歷史出發，`n` 步 `bennettAut` 的工作分量
精確 = `n` 步 `M.step`；歷史分量存在（Bennett 垃圾誠實外顯）且未來側保持新鮮。 -/
theorem bennettAut_iterate (c : M.Cfg) (n : ℕ) :
    ∃ η : ℤ → M.HistRec,
      (⇑M.bennettAut)^[n] (c, M.blankHist) = (M.step^[n] c, η) ∧
        FreshFrom M.blankRec η :=
  histConveyor_iterate (fun c' ↦ congrArg Prod.fst (M.bufferedStep_blank c')) n c
    M.blankHist (freshFrom_const _)

/-! ### 拓撲：Bennett 自同胚 -/

/-- 帶座標 `k` 的輸出只讀離散資料 `(q, a, b, t (k-1), t k, t (k+1))`
（方向 `∈ {-1,0,1}` 故至多讀三個帶座標）。 -/
private def tapeRead (k : ℤ)
    (x : (Fin M.m → Bool) × Bool × Bool × Bool × Bool × Bool) : Bool :=
  match M.move x.1 x.2.1 with
  | .left => if k - 1 = 0 then xor (M.write x.1 x.2.1) x.2.2.1 else x.2.2.2.1
  | .stay => if k = 0 then xor (M.write x.1 x.2.1) x.2.2.1 else x.2.2.2.2.1
  | .right => if k + 1 = 0 then xor (M.write x.1 x.2.1) x.2.2.1 else x.2.2.2.2.2

private theorem tapeRead_eq (k : ℤ) (p : M.Cfg × M.HistRec) :
    (if k + (M.move p.1.1 (p.1.2 0)).toInt = 0 then xor (M.write p.1.1 (p.1.2 0)) p.2.2
      else p.1.2 (k + (M.move p.1.1 (p.1.2 0)).toInt)) =
    M.tapeRead k (p.1.1, p.1.2 0, p.2.2, p.1.2 (k - 1), p.1.2 k, p.1.2 (k + 1)) := by
  rcases hmv : M.move p.1.1 (p.1.2 0) with _ | _ | _ <;>
    simp only [tapeRead, hmv, Dir.toInt]
  · rw [show k + (-1 : ℤ) = k - 1 from by ring]
  · rw [show k + (0 : ℤ) = k from by ring]

/-- `bufferedFwd` 連續：每個輸出座標只讀有限筆離散資料（狀態、讀入位、緩衝）
加至多三個帶座標。 -/
theorem continuous_bufferedFwd : Continuous M.bufferedFwd := by
  have heval : ∀ n : ℤ, Continuous fun p : M.Cfg × M.HistRec ↦ p.1.2 n :=
    fun n ↦ (continuous_apply n).comp (continuous_snd.comp continuous_fst)
  have hq : Continuous fun p : M.Cfg × M.HistRec ↦ p.1.1 :=
    continuous_fst.comp continuous_fst
  unfold bufferedFwd
  refine Continuous.prodMk (Continuous.prodMk ?_ (continuous_pi fun k ↦ ?_))
    (hq.prodMk (heval 0))
  · exact (continuous_of_discreteTopology
      (f := fun x : (Fin M.m → Bool) × Bool × (Fin M.m → Bool) ↦
        fun j ↦ xor (M.next x.1 x.2.1 j) (x.2.2 j))).comp
      (hq.prodMk ((heval 0).prodMk (continuous_fst.comp continuous_snd)))
  · have hfac : (fun p : M.Cfg × M.HistRec ↦
        if k + (M.move p.1.1 (p.1.2 0)).toInt = 0 then xor (M.write p.1.1 (p.1.2 0)) p.2.2
          else p.1.2 (k + (M.move p.1.1 (p.1.2 0)).toInt)) =
        fun p ↦ M.tapeRead k (p.1.1, p.1.2 0, p.2.2, p.1.2 (k - 1), p.1.2 k, p.1.2 (k + 1)) :=
      funext fun p ↦ M.tapeRead_eq k p
    rw [hfac]
    exact (continuous_of_discreteTopology (f := M.tapeRead k)).comp
      (hq.prodMk ((heval 0).prodMk ((continuous_snd.comp continuous_snd).prodMk
        ((heval (k - 1)).prodMk ((heval k).prodMk (heval (k + 1)))))))

theorem continuous_bufferedStep : Continuous ⇑M.bufferedStep :=
  M.continuous_bufferedFwd

/-- **Bennett 自同胚**：`Cfg × 歷史流` 是緊 Hausdorff（有限離散 × 康托爾型乘積），
正向連續 ⟹ 自同胚（逆向連續免費）。 -/
def bennettHomeo : (M.Cfg × (ℤ → M.HistRec)) ≃ₜ (M.Cfg × (ℤ → M.HistRec)) :=
  histConveyorHomeo M.bufferedStep M.continuous_bufferedStep

@[simp] theorem coe_bennettHomeo : ⇑M.bennettHomeo = ⇑M.bennettAut := rfl

end BitTM

end

end FluidTuring
