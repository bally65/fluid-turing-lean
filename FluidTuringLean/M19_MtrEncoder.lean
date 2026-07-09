import FluidTuringLean.M18_MtrControl

/-!
# Module 19 — TM2 全組態 → 位帶編碼 `encStacks`（(ii) B2a 子塊 3）

`M_tr` 模擬 mathlib `Turing.PartrecToTM2.tr` 的一個 TM2 步。TM2 組態
（`Turing.TM2.Cfg`）= 控制 `l : Option Λ'` + 局部變數 `var : σ'` + **堆疊** `stk : K' → List Γ'`。
控制 + 變數塞進 M_tr 的有限狀態（M18）；本塊處理**堆疊 → 位帶**：

`K' = {main, rev, aux, stack}`（4 堆疊）、皆用單一字母 `Γ'`（4 符號、M17 `Γ'BitEquiv` → 2 位）。
每堆疊 = 2 內容軌 + 1 頂標記軌 = 3 軌；4 堆疊 = 12 軌，用 M17 `multiTrackEnc` 交錯成單一
`ℤ → Bool`。

**本塊交付 = `encStacks` + 組態忠實性（`encStacks_injective`）**：位帶**唯一決定**全 4 堆疊
——把 M17 單堆疊 round-trip（`stackDecode_stackContent`）抬到 4 堆疊全組態。這是不可逆
`M_tr` 正確性歸納的地基。

**範圍決策**：`M_tr.step` 的**定義**（BitTM 走位 + 位編輯）併入子塊 4（與其 macrostep 正確性
同處），因為裸 def 不證任何事（硬規則 #2：不要術語流暢但內容稀薄的偽推導）。子塊 3 = 可證的
靜態編碼忠實性。
-/

namespace FluidTuring

open Turing Turing.ToPartrec Turing.PartrecToTM2

/-- 4 堆疊索引 `K' ≃ Fin 4`（顯式列舉、供軌位分配）。 -/
def kEquiv : K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun
    | 0 => .main
    | 1 => .rev
    | 2 => .aux
    | 3 => .stack
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- 一堆疊的 3 條軌：role 0/1 = 內容 2 位（`stackContent`），role 2 = 頂標記軌
（`stackMark`，唯一 1 在深度 = `len`）。 -/
def stackTracks (s : List Γ') (role : Fin 3) : ℤ → Bool :=
  if role = 0 then fun j ↦ (stackContent s j).1
  else if role = 1 then fun j ↦ (stackContent s j).2
  else stackMark s.length

/-- 12 軌：軌 `t` → 堆疊 `t/3`（經 `kEquiv.symm`）的 role `t%3`。 -/
def allTracks (S : K' → List Γ') (t : Fin 12) : ℤ → Bool :=
  stackTracks (S (kEquiv.symm ⟨t.val / 3, by have := t.isLt; omega⟩))
    ⟨t.val % 3, by have := t.isLt; omega⟩

/-- **TM2 堆疊 → 位帶**：4 堆疊 × 3 軌，用 `multiTrackEnc` 交錯成單一 `ℤ → Bool`。 -/
def encStacks (S : K' → List Γ') : ℤ → Bool := multiTrackEnc (n := 11) (allTracks S)

/-! ## 軌評估 + 標記單射（忠實性的零件） -/

/-- `stackTracks` 逐 role 展開。 -/
theorem stackTracks_zero (s : List Γ') : stackTracks s 0 = fun j ↦ (stackContent s j).1 := by
  simp [stackTracks]

theorem stackTracks_one (s : List Γ') : stackTracks s 1 = fun j ↦ (stackContent s j).2 := by
  simp [stackTracks]

theorem stackTracks_two (s : List Γ') : stackTracks s 2 = stackMark s.length := by
  simp [stackTracks]

/-- **標記軌單射**：`stackMark a = stackMark b → a = b`（唯一 1 的位置 = 深度）。 -/
theorem stackMark_injective {a b : ℕ} (h : stackMark a = stackMark b) : a = b := by
  have h2 := congrFun h (a : ℤ)
  simp only [stackMark, decide_eq_decide] at h2
  exact_mod_cast h2.mp trivial

/-- `allTracks` 在堆疊 `k`、role `r` 的軌位 `3 * (kEquiv k) + r` 取回 `stackTracks (S k) r`。 -/
theorem allTracks_eval (S : K' → List Γ') (k : K') (r : Fin 3)
    (h : 3 * (kEquiv k).val + r.val < 12) :
    allTracks S ⟨3 * (kEquiv k).val + r.val, h⟩ = stackTracks (S k) r := by
  have hi := (kEquiv k).isLt
  have hr := r.isLt
  have e1 : (3 * (kEquiv k).val + r.val) / 3 = (kEquiv k).val := by omega
  have e2 : (3 * (kEquiv k).val + r.val) % 3 = r.val := by omega
  unfold allTracks
  rw [show (⟨(3 * (kEquiv k).val + r.val) / 3, by omega⟩ : Fin 4) = kEquiv k from Fin.ext e1,
      show (⟨(3 * (kEquiv k).val + r.val) % 3, by omega⟩ : Fin 3) = r from Fin.ext e2,
      Equiv.symm_apply_apply]

/-! ## ★組態忠實性★ -/

/-- **軌族由編碼帶唯一決定**（`multiTrackEnc_injective` 的 12 軌實例）。 -/
theorem allTracks_injective {S S' : K' → List Γ'} (h : encStacks S = encStacks S') :
    allTracks S = allTracks S' :=
  multiTrackEnc_injective h

/-- **★encStacks 忠實性★**：位帶**唯一決定**全 4 堆疊組態。M17 單堆疊 round-trip
（`stackDecode_stackContent`）抬到 4 堆疊——不可逆 `M_tr` 正確性歸納的地基：組態由其位帶
編碼唯一決定。 -/
theorem encStacks_injective {S S' : K' → List Γ'} (h : encStacks S = encStacks S') : S = S' := by
  have hA := allTracks_injective h
  funext k
  have hi := (kEquiv k).isLt
  -- 三軌相等
  have b0 : 3 * (kEquiv k).val + (0 : Fin 3).val < 12 := by simp; omega
  have b1 : 3 * (kEquiv k).val + (1 : Fin 3).val < 12 := by simp; omega
  have b2 : 3 * (kEquiv k).val + (2 : Fin 3).val < 12 := by simp; omega
  have t0 := congrFun hA ⟨3 * (kEquiv k).val + (0 : Fin 3).val, b0⟩
  have t1 := congrFun hA ⟨3 * (kEquiv k).val + (1 : Fin 3).val, b1⟩
  have t2 := congrFun hA ⟨3 * (kEquiv k).val + (2 : Fin 3).val, b2⟩
  rw [allTracks_eval, allTracks_eval] at t0 t1 t2
  rw [stackTracks_zero, stackTracks_zero] at t0
  rw [stackTracks_one, stackTracks_one] at t1
  rw [stackTracks_two, stackTracks_two] at t2
  -- 長度相等（標記單射）
  have hlen : (S k).length = (S' k).length := stackMark_injective t2
  -- 內容相等（兩位軌）
  have hcont : stackContent (S k) = stackContent (S' k) := by
    funext j
    exact Prod.ext (congrFun t0 j) (congrFun t1 j)
  -- round-trip 復原
  calc S k = stackDecode (S k).length (stackContent (S k)) := (stackDecode_stackContent _).symm
    _ = stackDecode (S' k).length (stackContent (S' k)) := by rw [hlen, hcont]
    _ = S' k := stackDecode_stackContent _

end FluidTuring
