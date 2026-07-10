import FluidTuringLean.M19_MtrEncoder

/-!
# Module 21 — M_tr 全組態編碼器 `encCfg` + 忠實性（M_tr 本體 4a）

M20 頂石把整個流體端不可判定性歸約到「造一個位元機 `M_tr` 使 `M_tr.step` 模擬通用 TM2
`stepAux` 樹走」。本塊 = M_tr 建構本體的**第一塊（4a）**：TM2 全組態 `Cfg'` 的編碼器 +
忠實性，接合 M18（有限控制）+ M19（位帶）。

`Cfg' = TM2.Cfg (fun _ : K' ↦ Γ') Λ' (Option Γ')` = 控制 `l : Option Λ'` + 變數
`var : Option Γ'` + 堆疊 `stk : K' → List Γ'`。編碼：

- **堆疊 → 位帶**：M19 `encStacks`（4 堆疊交錯，`encStacks_injective` 忠實）。
- **控制/變數 → 有限狀態**：`l` 落在**可達有限標籤集** `ctrlLabels cu`（M18 `trLabels` +
  `none`），`var ∈ Option Γ'`（5 值）——皆有限、位元可編碼（`ctrlFin`）。

**本塊交付**：`encCfg` + `encCfg_injective`（全組態忠實：組態由 `(label, var, 位帶)` 唯一決定，
位帶真編所有 4 堆疊）+ `ctrlLabels` / `l_mem_ctrlLabels`（可達組態的控制落在有限集 = M_tr 的
`Fin m` 控制地基）+ `ctrlFin`（控制 ≃ Fin card）。

**範圍界線**：本塊 `encCfg` 的目標把 `label/var` 保留為 `Option Λ' × Option Γ'`（**真忠實**，
不失資訊），並**另外**證控制落在有限集 → 可壓進 `Fin m → Bool`。把 `label` 實際壓進位元向量
（`ctrlLabels`/`Option Γ'` → `Fin m → Bool`）+ 接 M_tr 動力學 = 4b。
-/

namespace FluidTuring

open Turing Turing.ToPartrec Turing.PartrecToTM2

/-- **M_tr 全組態編碼器**：`Cfg' → (控制 label, 變數, 位帶)`。位帶 = M19 `encStacks`
（4 堆疊交錯）；`label/var` 此塊保留原型（真忠實），有限壓縮見 `ctrlLabels`/`ctrlFin`。 -/
def encCfg (c : Cfg') : Option Λ' × Option Γ' × (ℤ → Bool) :=
  (c.l, c.var, encStacks c.stk)

/-- **★全組態忠實性★**：組態由其編碼 `(label, var, 位帶)` **唯一決定**——位帶真編所有 4
堆疊（`encStacks_injective`），`label/var` 直通。這是 M_tr 正確性歸納的組態級地基（M19 堆疊
忠實性抬到含控制的全組態）。 -/
theorem encCfg_injective : Function.Injective encCfg := by
  rintro ⟨l, v, S⟩ ⟨l', v', S'⟩ h
  simp only [encCfg, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hS⟩ := h
  obtain rfl := encStacks_injective hS
  rfl

/-! ## 控制的有限性（M_tr 的 `Fin m` 控制地基） -/

/-- **可達控制標籤集**：`M_tr` 控制的 `l : Option Λ'` 落在此有限集——`none`（停機）加上
`trLabels cu`（M18：固定通用碼 `cu` 的可達 TM2 label，`Finset Λ'`）。 -/
def ctrlLabels (cu : Code) : Finset (Option Λ') := insert none ((trLabels cu).image some)

/-- **控制標籤 ∈ 有限集（條件式）**：**若** `c.l` 的標籤 ∈ `trLabels cu`（明寫**假設**），則
`c.l ∈ ctrlLabels cu`。**注意**：本引理**不**證「執行必停在 `trLabels`」——那是 forward-closure
（`Supports`，M18/M33 另證）；本引理只是「標籤可達（假設）⟹ 塞得進有限集」的封裝。 -/
theorem l_mem_ctrlLabels (cu : Code) (c : Cfg')
    (hl : ∀ x ∈ c.l, x ∈ trLabels cu) : c.l ∈ ctrlLabels cu := by
  rcases hc : c.l with _ | x
  · simp [ctrlLabels]
  · simp only [ctrlLabels, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨x, hl x hc, rfl⟩

/-- **控制標籤 ↔ `Fin (card)`**：可達控制的位元編碼（M_tr 的 `Fin m` 控制分量、含 `var` 一併
成有限狀態）。鏡射 M18 `trLabelEquivFin`、加 `none` 停機槽。 -/
noncomputable def ctrlFin (cu : Code) : ↥(ctrlLabels cu) ≃ Fin (ctrlLabels cu).card :=
  (Fintype.equivFin _).trans (finCongr (Fintype.card_coe _))

end FluidTuring
