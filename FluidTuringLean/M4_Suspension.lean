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

end FluidTuring
