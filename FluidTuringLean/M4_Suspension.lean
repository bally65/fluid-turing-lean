import FluidTuringLean.M3_Encoding

/-!
# Module 4 — 懸掛構造與映射環面

離散跳躍 → 連續流：給定 `f : X → X`，映射環面
`MappingTorus f = (X × ℝ) / ⟨(x, t+1) ~ (f x, t)⟩`
上有自然的懸掛半流 `suspFlow s [x, t] = [x, t + s]`，
每整數時間走一步 `f`。

已證：流的 well-definedness、群律（`0` 恆等、加法合成）、
每個時間切片映射連續（商拓撲）、以及「時間 1 實現 `f`」。

本檔零 sorry。
-/

namespace FluidTuring

/-- 映射環面的黏合關係：`(x, t+1) ~ (f x, t)`。 -/
inductive SuspRel {X : Type*} (f : X → X) : X × ℝ → X × ℝ → Prop
  | shift (x : X) (t : ℝ) : SuspRel f (x, t + 1) (f x, t)

/-- 映射環面：`X × ℝ` 對 `SuspRel` 的商。
（`Quot` 自動取生成的等價關係；拓撲為商拓撲。） -/
def MappingTorus {X : Type*} (f : X → X) : Type _ := Quot (SuspRel f)

namespace MappingTorus

variable {X : Type*} {f : X → X}

instance [TopologicalSpace X] : TopologicalSpace (MappingTorus f) :=
  instTopologicalSpaceQuot

/-- 商投影。 -/
def mk (f : X → X) (p : X × ℝ) : MappingTorus f := Quot.mk _ p

/-- 懸掛流的時間 `s` 映射：`[x, t] ↦ [x, t + s]`。 -/
def suspFlow (s : ℝ) : MappingTorus f → MappingTorus f :=
  Quot.map (fun p ↦ (p.1, p.2 + s)) (by
    rintro _ _ ⟨x, t⟩
    have h : t + 1 + s = t + s + 1 := by ring
    simpa [h] using SuspRel.shift (f := f) x (t + s))

@[simp]
theorem suspFlow_mk (s : ℝ) (x : X) (t : ℝ) :
    suspFlow s (mk f (x, t)) = mk f (x, t + s) := rfl

/-- 群律：時間 `0` 是恆等。 -/
theorem suspFlow_zero (q : MappingTorus f) : suspFlow 0 q = q := by
  induction q using Quot.inductionOn with
  | h p => exact congrArg (Quot.mk _) (congrArg (fun z ↦ (p.1, z)) (add_zero p.2))

/-- 群律：時間相加即合成。 -/
theorem suspFlow_add (s s' : ℝ) (q : MappingTorus f) :
    suspFlow (s + s') q = suspFlow s (suspFlow s' q) := by
  induction q using Quot.inductionOn with
  | h p =>
      exact congrArg (Quot.mk _) (congrArg (fun z ↦ (p.1, z)) (by ring))

/-- 商拓撲下，每個時間切片映射連續。 -/
theorem continuous_suspFlow [TopologicalSpace X] (s : ℝ) :
    Continuous (suspFlow (f := f) s) :=
  continuous_quot_map _ (continuous_fst.prodMk (continuous_snd.add continuous_const))

/-- 懸掛流在整數時間實現離散跳躍：`suspFlow 1 [x, 0] = [f x, 0]`。 -/
theorem suspFlow_one_realizes (x : X) :
    suspFlow 1 (mk f (x, 0)) = mk f (f x, 0) := by
  have h : (0 : ℝ) + 1 = 0 + 1 := rfl
  calc suspFlow 1 (mk f (x, 0)) = mk f (x, 0 + 1) := rfl
  _ = mk f (f x, 0) := Quot.sound (by simpa using SuspRel.shift (f := f) x 0)

end MappingTorus

/-! ## 可逆離散系統的映射環面：完整不變量、切片單射、緊緻性

`f` 可逆（`e : X ≃ X`）時，映射環面有完整不變量
`torusRep (x, t) = (e^⌊t⌋ x, fract t)`：兩點同類 ⟺ 不變量相等。
由此得切片嵌入單射與（`X` 緊緻時）整個環面的緊緻性。 -/

namespace MappingTorus

section Equiv

variable {X : Type*} (e : X ≃ X)

/-- 群作用套疊引理（ℕ 版）：時間平移 `n` 對應離散跳 `n` 步。 -/
theorem mk_add_nat (n : ℕ) (x : X) (t : ℝ) :
    mk ⇑e (x, t + n) = mk ⇑e ((e ^ n) x, t) := by
  induction n generalizing x t with
  | zero => simp
  | succ m ih =>
      have h1 : t + ((m + 1 : ℕ) : ℝ) = (t + 1) + (m : ℕ) := by push_cast; ring
      calc mk ⇑e (x, t + ((m + 1 : ℕ) : ℝ))
          = mk ⇑e (x, (t + 1) + (m : ℕ)) := by rw [h1]
      _ = mk ⇑e ((e ^ m) x, t + 1) := ih x (t + 1)
      _ = mk ⇑e (⇑e ((e ^ m) x), t) := Quot.sound (SuspRel.shift _ _)
      _ = mk ⇑e ((e ^ (m + 1)) x, t) := by rw [pow_succ']; rfl

/-- 群作用套疊引理（ℤ 版，`e` 可逆才有負向）。 -/
theorem mk_add_int (m : ℤ) (x : X) (t : ℝ) :
    mk ⇑e (x, t + m) = mk ⇑e ((e ^ m) x, t) := by
  obtain n | n := m
  · simpa [zpow_natCast] using mk_add_nat e n x t
  · have key := mk_add_nat e (n + 1) ((e ^ (Int.negSucc n)) x)
      (t + ((Int.negSucc n : ℤ) : ℝ))
    have harg : (t + ((Int.negSucc n : ℤ) : ℝ)) + ((n + 1 : ℕ) : ℝ) = t := by
      push_cast [Int.negSucc_eq]; ring
    have hcomp : (e ^ (n + 1 : ℕ)) ((e ^ (Int.negSucc n)) x) = x := by
      have hmul : (e ^ (n + 1 : ℕ) : Equiv.Perm X) * e ^ (Int.negSucc n) = 1 := by
        rw [← zpow_natCast, ← zpow_add]
        norm_num [Int.negSucc_eq]
      calc (e ^ (n + 1 : ℕ)) ((e ^ (Int.negSucc n)) x)
          = ((e ^ (n + 1 : ℕ) : Equiv.Perm X) * e ^ (Int.negSucc n)) x := rfl
      _ = (1 : Equiv.Perm X) x := by rw [hmul]
      _ = x := rfl
    rw [harg, hcomp] at key
    exact key.symm

/-- 完整不變量：`(x, t) ↦ (e^⌊t⌋ x, fract t)`。 -/
noncomputable def torusRep (p : X × ℝ) : X × ℝ :=
  ((e ^ ⌊p.2⌋) p.1, Int.fract p.2)

theorem torusRep_eq_of_rel {p q : X × ℝ} (h : SuspRel ⇑e p q) :
    torusRep e p = torusRep e q := by
  obtain ⟨x, t⟩ := h
  unfold torusRep
  have h1 : (e ^ ⌊t + 1⌋) x = (e ^ ⌊t⌋) (⇑e x) := by
    rw [Int.floor_add_one, zpow_add_one]; rfl
  have h2 : Int.fract (t + 1) = Int.fract t := Int.fract_add_one t
  rw [Prod.ext_iff]
  exact ⟨h1, h2⟩

/-- **完整不變量刻劃**：`mk p = mk q ⟺ torusRep p = torusRep q`。 -/
theorem mk_eq_mk_iff (p q : X × ℝ) :
    mk ⇑e p = mk ⇑e q ↔ torusRep e p = torusRep e q := by
  constructor
  · intro h
    exact congrArg (Quot.lift (torusRep e) fun _ _ hab ↦ torusRep_eq_of_rel e hab) h
  · obtain ⟨x, t⟩ := p
    obtain ⟨y, s⟩ := q
    intro h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    have hx : mk ⇑e (x, t) = mk ⇑e ((e ^ ⌊t⌋) x, Int.fract t) := by
      conv_lhs => rw [show t = Int.fract t + (⌊t⌋ : ℝ) from (Int.fract_add_floor t).symm]
      exact mk_add_int e ⌊t⌋ x (Int.fract t)
    have hy : mk ⇑e (y, s) = mk ⇑e ((e ^ ⌊s⌋) y, Int.fract s) := by
      conv_lhs => rw [show s = Int.fract s + (⌊s⌋ : ℝ) from (Int.fract_add_floor s).symm]
      exact mk_add_int e ⌊s⌋ y (Int.fract s)
    rw [hx, hy]
    exact congrArg (mk ⇑e) (Prod.ext_iff.mpr ⟨h1, h2⟩)

/-- 切片嵌入單射：`x ↦ [x, 0]` 不黏合相異點。 -/
theorem mk_slice_injective : Function.Injective fun x : X ↦ mk ⇑e (x, 0) := by
  intro a b h
  have hrep := (mk_eq_mk_iff e (a, 0) (b, 0)).1 h
  unfold torusRep at hrep
  simpa using hrep

/-- `X` 緊緻 ⟹ 映射環面緊緻（`X × [0,1]` 的連續滿射像）。 -/
theorem compactSpace [TopologicalSpace X] [CompactSpace X] :
    CompactSpace (MappingTorus ⇑e) := by
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  constructor
  have hsurj : Function.Surjective
      (fun p : X × Set.Icc (0 : ℝ) 1 ↦ mk ⇑e (p.1, (p.2 : ℝ))) := by
    intro q
    induction q using Quot.inductionOn with
    | h p =>
        obtain ⟨x, t⟩ := p
        refine ⟨((e ^ ⌊t⌋) x,
          ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩), ?_⟩
        have h := mk_add_int e ⌊t⌋ x (Int.fract t)
        rw [Int.fract_add_floor] at h
        exact h.symm
  rw [← Set.range_eq_univ.mpr hsurj]
  exact isCompact_range (continuous_quot_mk.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end Equiv

/-! ## 同胚情形：開商映射與懸掛流的聯合連續性

`e : X ≃ₜ X` 時商投影是**開**映射（飽和化 = 可數個同胚像的聯集），
而開商映射與 `id_ℝ` 的乘積仍是商映射 —— 由此得懸掛流對 `(s, q)`
的聯合連續性，不需要 Whitehead 定理。 -/

section Homeomorph

variable {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X)

theorem continuous_perm_zpow (m : ℤ) : Continuous ⇑(e.toEquiv ^ m) := by
  obtain n | n := m
  · simpa [zpow_natCast, Equiv.Perm.coe_pow] using e.continuous.iterate n
  · have h : (e.toEquiv ^ (Int.negSucc n)) = (e.symm.toEquiv ^ (n + 1)) := by
      rw [zpow_negSucc, ← inv_pow]; rfl
    rw [h, Equiv.Perm.coe_pow]
    exact e.symm.continuous.iterate (n + 1)

/-- `e` 的整數次冪是同胚。 -/
def permZpowHomeo (m : ℤ) : X ≃ₜ X where
  toEquiv := e.toEquiv ^ m
  continuous_toFun := continuous_perm_zpow e m
  continuous_invFun := by
    change Continuous ⇑(e.toEquiv ^ m).symm
    have h : (e.toEquiv ^ m).symm = e.toEquiv ^ (-m) := by
      rw [zpow_neg]; rfl
    rw [h]
    exact continuous_perm_zpow e (-m)

/-- 商投影是開映射：開集的飽和化是 `ℤ` 個同胚像的聯集。 -/
theorem isOpenMap_mk : IsOpenMap (Quot.mk (SuspRel ⇑e)) := by
  intro U hU
  have hzpow : ∀ (a b : ℤ) (x : X),
      (e.toEquiv ^ (a + b)) x = (e.toEquiv ^ a) ((e.toEquiv ^ b) x) := by
    intro a b x
    rw [zpow_add]; rfl
  have hsat : Quot.mk (SuspRel ⇑e) ⁻¹' (Quot.mk (SuspRel ⇑e) '' U) =
      ⋃ m : ℤ, (Prod.map ⇑(e.toEquiv ^ m) (· - (m : ℝ))) '' U := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨u, huU, hu⟩
      have hrep := (mk_eq_mk_iff e.toEquiv u p).1 hu
      simp only [torusRep, Prod.mk.injEq] at hrep
      obtain ⟨h1, h2⟩ := hrep
      refine ⟨⌊u.2⌋ - ⌊p.2⌋, u, huU, ?_⟩
      have hfst : (e.toEquiv ^ (⌊u.2⌋ - ⌊p.2⌋)) u.1 = p.1 := by
        have hm : ⌊u.2⌋ - ⌊p.2⌋ = -⌊p.2⌋ + ⌊u.2⌋ := by ring
        rw [hm, hzpow, h1, ← hzpow, neg_add_cancel, zpow_zero]
        rfl
      have hsnd : u.2 - ((⌊u.2⌋ - ⌊p.2⌋ : ℤ) : ℝ) = p.2 := by
        have h2' : u.2 - (⌊u.2⌋ : ℝ) = p.2 - (⌊p.2⌋ : ℝ) := by
          rw [Int.self_sub_floor, Int.self_sub_floor]
          exact h2
        push_cast
        linarith
      exact Prod.ext_iff.mpr ⟨hfst, hsnd⟩
    · rintro ⟨m, u, huU, rfl⟩
      refine ⟨u, huU, ?_⟩
      have h := mk_add_int e.toEquiv m u.1 (u.2 - (m : ℝ))
      have harg : u.2 - (m : ℝ) + (m : ℝ) = u.2 := by ring
      rw [harg] at h
      exact h
  have hopen : IsOpen (Quot.mk (SuspRel ⇑e) ⁻¹' (Quot.mk (SuspRel ⇑e) '' U)) := by
    rw [hsat]
    exact isOpen_iUnion fun m ↦
      ((permZpowHomeo e m).isOpenMap.prodMap (isOpenMap_sub_right (m : ℝ))) U hU
  exact isQuotientMap_quot_mk.isOpen_preimage.mp hopen

/-- **懸掛流的聯合連續性**：`(s, q) ↦ suspFlow s q` 連續。 -/
theorem continuous_suspFlow_uncurried :
    Continuous fun q : ℝ × MappingTorus ⇑e ↦ suspFlow q.1 q.2 := by
  have hquot : Topology.IsQuotientMap (Prod.map (id : ℝ → ℝ)
      (Quot.mk (SuspRel ⇑e) : X × ℝ → MappingTorus ⇑e)) :=
    (IsOpenMap.id.prodMap (isOpenMap_mk e)).isQuotientMap
      (continuous_id.prodMap continuous_quot_mk)
      (Function.surjective_id.prodMap Quot.mk_surjective)
  refine hquot.continuous_iff.mpr ?_
  change Continuous fun q : ℝ × (X × ℝ) ↦
    Quot.mk (SuspRel ⇑e) (q.2.1, q.2.2 + q.1)
  exact continuous_quot_mk.comp
    ((continuous_snd.fst).prodMk ((continuous_snd.snd).add continuous_fst))

end Homeomorph

end MappingTorus

end FluidTuring
