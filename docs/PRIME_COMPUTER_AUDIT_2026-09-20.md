# fluid_turing_lean × PrimeReachBridge v0.1 — 稽核報告

---

## 1. 一句話裁決

**NO-GO**：`reach_at_k`（`FluidTuringLean/M59_SmoothUndecidable.lean:134`）本來就對**所有** `BitTM`、所有 `v`、`T`、`vhalt`、`k` 全稱量化且**零側假設**，所以塞一台質數機進去是**全稱實例化**，不是新定理；而現有鏈唯一製造內容的那一步 —— `exact ComputablePred.halting_problem n hcomp`（M59:200）—— 正是質數版必須刪掉的（`Nat.decidablePrime`，mathlib `Mathlib/Data/Nat/Prime/Defs.lean:162`），成品是 Δ₁ ⟺ Δ₁ 的重新編碼。

**但有 GO-SMALL**：同一筆錢可以買到三件嚴格更強、更便宜、且其中一件與流體無關因此有 repo 外消費者的東西（§4）。

---

## 2. 外部分析的對帳表

| # | 它的主張 | 裁決 | 一行收據 |
|---|---|---|---|
| C1 | M57 建立 BitTM 逐步模擬，限於 `Tape Bool` | **PARTIAL** | M57:174 的陳述裡**沒有** `BitTM.step`；真正接上的是 M59:71 |
| C2 | M59 的橋是 generic、可插新機器 | **TRUE** | M59:134 五個顯式 binder、零假設、無 `Mtr` |
| C3 | `sigmaM` 是 `noncomputable`，擋住直接執行 | **TRUE** | M59:122；`.lake/build/ir/.../M59_SmoothUndecidable.c` 裡 `sigmaM` 符號 = 0 |
| C4 | `pop_not_contractive` 擋連續流自我修正；且它 scope 有限 | **TRUE** | M56:76；M56:41-43 自陳一般論證「**未**在此重新形式化」 |
| C5 | M33 不是真 Navier–Stokes | **TRUE** | M33:37 的陳述裡沒有 fluid/Euler/NS/Beltrami/blowup 任何一個字 |
| C6 | 不可當 decider；primality 可判定；`Nat.Prime`／instance／`prime_def_le_sqrt` 都在 | **TRUE** | Prime/Defs.lean:41、:162、:124 逐字核對過 |
| C7 | 快照 = public main f8bc051、2026-07-20 | **TRUE**（可驗，前提錯） | `.git/refs/heads/main` = `f8bc051…2947`；commit object `author … 1784524253 +0800` = 2026-07-20 13:10:53 |
| C8 | 缺 (a) 質數機＋停機證明、(b) 編譯成 BitTM 並保答案、(c) 再重用 M57–M59 | **PARTIAL**（(b) 錯） | 見下 |

### 它 WRONG 的地方

1. **(b) 不是缺的工作。** `Mtr`（M27:47）是 TM0→BitTM 編譯器，`Mtr_step_run`（M27:89）、`Mtr_track`（M28:67）、`Mtr_halts_iff`（M28:113）就是它的正確性證明。這一整疊已經在倉庫裡。
2. **「M57 建立 BitTM 模擬」在陳述層是假的。** M57:174 `gStepRL3_simulates_BitTM` 的 RHS 是由 `M.next`/`M.write`/`M.move` 三個**欄位**加 `tapeStep`（M25:41）現組的 Tape 層單步。`BitTM.step`（M3b:144，型別在 `ℤ → Bool` 上）只在 M59:71 `bitStep_commute` 被接上，k 步版在 M59:98／:83。M57 檔頭 :16 自己把 `BitTM.step` 的帶說成 `Turing.Tape Bool` —— 對照 M3b:140 那句是假的，外部分析照抄了。
3. **`Tape Bool` 限制被誤定位成「假設」。** `bitEnc`（M57:146）是**全函數、零側條件**；限制是定義域的**型別**，根源是 `encInf`（M55:73）走 `ListBlank` 商的有限 base-K 和。而且對「把 n 編成帶子」這件事它**一毛錢都不花**。
4. **把不可執行只歸給 `sigmaM`。** 連輸入編碼器都不可算：`bitVecToNat`（M57:59，走 Classical `Fintype.equivFin`）、`natToBitVec`（M57:75，`Function.invFun`），因此 `bitEnc`、`δqOf/δwOf/moveOf`（M57:162-167）全部不出 code。基點 x₀ 的第一座標在 Lean 裡連個數字都寫不出來。
5. **一個 σ 兩個目標集在 σ 線上不可得。** `Mtr` 把每個 TM0 停機塌成單一控制字 `encHalt S`（M27:35-38 ＋ M26:60）；而且 σ 隨碼變 —— `SU` 由 `codeSupp cu Cont'.halt` 造（M59:227）→ `ctrlCard` → `Mtr.m` → σ。換碼換 σ。
6. **引錯引理（但前幾輪的糾正也錯了一半）。** `Nat.prime_def_le_sqrt`（Defs.lean:124）寫的是 `m ≤ Nat.sqrt p`，不是它說的 `d*d > n`；它自己寫的迴圈不變量「2 ≤ a < d」的字面對應是 `prime_def_lt'`（Defs.lean:114）。**但**在此 pin 底下 `Primrec Nat.sqrt` **已經證好**（`Mathlib/Computability/Primrec/List.lean:779`，底層 `Nat.Primrec'.sqrt` 在 :704），加上 `Primrec.nat_div`（Basic.lean:710），所以走 sqrt 路線在 Primrec 層是直接可得、而且給 O(√n) 界。前面幾輪四次把 sqrt 斥為「繞路」，在這條軸上是錯的。

### 它 MISSED 的 on-ramp（最重要的一項，整個審查也漏了）

**`bitTM_bennett_characterization`，`FluidTuringLean/M37_ReachCharacterization.lean:51-58`**（不可判定孿生在 `M20_FlowCapstone.lean:69`）：

```lean
theorem bitTM_bennett_characterization (M : BitTM)
    (Hcfg : Set M.Cfg) (init : Nat.Partrec.Code → M.Cfg) (n : ℕ)
    (hHclosed : ∀ code, init code ∈ Hcfg → M.step (init code) ∈ Hcfg)
    (hmachine : ∀ code, (∃ k : ℕ, M.step^[k + 1] (init code) ∈ Hcfg) ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (_ : CompactSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : (M.Cfg × (ℤ → M.HistRec)) → Mt),
      ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code, M.blankHist))
          ∈ enc '' {p | p.1 ∈ Hcfg}) ↔ (code.eval n).Dom
```

四個後果，逐一打掉審查自己下的結構結論：

- **它對任意 `M : BitTM` 參數化**，和 `reach_at_k` 一樣。不經 `Mtr`、不經 TM0、不經 `codeSupp`。所有關於「`Mtr` 把停機塌成一個字」的限制在這裡不適用。
- **目標是任意 `Hcfg : Set M.Cfg`**，不是狀態超平面。**兩個互斥答案區是自然形狀**，帶上留下的見證因數**也可以表達**。C2／D2／六個設計全部背的「只讀第一座標、吐不出因數」是 σ 線的特性，不是倉庫的特性。
- **輸出是真的 `ContinuousFlowOn` 加 `∃ t : ℝ, 0 < t`** —— 連續時間。外部分析原話講的就是「smooth flow orbit」；六個候選設計**全部**終點在 `sigmaM`（離散自映射）然後寫一段道歉。流版本一直在那裡。
- Bennett 可逆化對任意 BitTM 免費：`bennettAut`（M3c:255）、`bennettAut_iterate`（M3c:263）、`bennettHomeo`（M3c:319）。`hHclosed` 比看起來弱 —— 它只要求「若起始組態已在 `Hcfg`，走一步還在」，不是 `Hcfg` 的一般前向封閉。

它仍帶 `init : Nat.Partrec.Code → M.Cfg` 與 `(code.eval n).Dom`，所以需要和 M59 同一個 index 泛化（§4 B1）—— 但審查告訴讀者那個泛化只能解鎖一個離散映射；它同時解鎖了流，而且目標更有表達力。

**其他漏掉的 on-ramp**：`wfCfgB_bitEnc`（M59:108）對任意 `v`、`T` 無條件（wf 側整個免費）；`vhalt` 是 binder，所以兩個目標字在手寫 BitTM 上免費；σ 線缺兩個便宜定理 —— M36 式補集推論、M37 式 characterization（`grep -cE "characterization|REPred" M59_SmoothUndecidable.lean` = **0**，而所需的 iff 已經在 M59:179 造好、又在 :199 被 `rw [key] at hcomp` 丟掉）。

---

## 3. 真正的死點

### FATAL —— 價值，不是可行性

- `reach_at_k`（M59:134）零假設 ⟹ 實例化不增強度；`ComputablePred.halting_problem`（M59:200）是唯一產生內容的一步，質數版刪掉它。
- **實證，我自己重數過**：「把具體機器插進通用定理」這一招倉庫跑過五次，消費者數是 `cnotTM_suspension_simulates` = 1、`ctrlDemoTM_suspension_simulates` = 1、`ctrlFullTM_suspension_simulates` = 1、`trackWalkTM_suspends` = 1、`bennettTM_suspension_simulates` = 2（全為自身宣告＋docstring），對照 `reach_at_k` = 7、`fluid_blowup_undecidable` = 7、`fluid_reach_characterization` = 3。五片終端葉子，零下游消費者。這會是第六片。
- `grep -rniE "prime|primality"` 掃 `FluidTuringLean/`＋`docs/`＋`README.md` = **0 hits**。倉庫裡沒有任何東西在等它。
- 你自己的路線圖已經裁決過這個類型：`docs/GPAC_ROADMAP.md:142`「玩具家族＝有限組態可判定死路」、:243／:256「邊際價值仍弱於且冗餘於主線 M33 無條件」。

### EXPENSIVE —— index 轉置，外部分析完全沒提

整條 characterization 鏈都綁死在「程式變／輸入固定」：`mtr_flow_characterization`（M37:89）、`bitTM_bennett_characterization`（M37:51）、`sigmaM_reach_undecidable_of`（M59:164），三者都是 `init : Nat.Partrec.Code → Cfg` ＋ `(code.eval n).Dom`。質數要的是「程式固定／輸入變」。機械，但它的 (c)「reuse M57-M59」一個字都沒提。

### EXPENSIVE —— 手寫 trial-division BitTM（Route A）

字母表是 `Bool`，而空白就是那兩個符號之一（mathlib `Tape.lean:20`），**沒有 marker 符號**；`TM0.Stmt` 是 move 或 write 二選一。倉庫從沒手寫過 TM0 機器；唯一一次機器級 BitTM 認真嘗試是 `M3d_BennettTM.lean`，1195 行，headline `bennettTM`（M3d:855）到今天還自陳「milestone A 只主張構造存在＋可逆；模擬語意＝待決清單」（M3d:853-854）。

### ROUTINE —— D5 循環性，而且比 M34 更隱形

`reach_at_k` 把 `v`、`T`、`vhalt` 全留白，所以作者可以寫 `if Nat.Prime n then vP else vC`，兩條 iff 在 k = 0 就過。倉庫自己有這形狀的合法例子：`blowupFamily`（M34:41）＋真 iff `blowupFamily_blowsUp_iff`（M34:45）。不對稱是關鍵：M34 的 case-split 在**不可判定**述詞上、結論是**下界**（保住）；質數版 split 在**可判定**述詞上、要的是**上界**（被摧毀）。而且 M34 還得寫 `open Classical in`（M34:40），質數版**連這個都不用**，因為 `Nat.decidablePrime` 可計算 —— 所以 `#print axioms` 會顯示標準三公理、完全看不見。

### 已解散的假死點（原本怕的四件，沒有一件是真的）

- **「編碼塞不進橋」** —— 不存在。`wfCfgB_bitEnc`（M59:108）對任意 `v`、`T` 無條件，`digitsLtB_two_map`（M57:105）因字母表是 Bool 而無條件，`reach_at_k` 自己的證明用 `norm_num` 關掉 M58 全部數值側條件（M59:139-143）。
- **「每個 n 要一台機器」** —— 不會。`sigmaM`（M59:122）只依賴 `M`；M59:179-181 倉庫自己就把 σ 綁在 lambda 外面。通用機路線上連起始狀態字都與輸入無關（`univTM1Cfg` 的標籤是 `trNormal cu Cont'.halt`，M31:21-25；`hinit_q` 的證明本體從不提 `code`，M59:245-249）。
- **「沒有東西可以跑」** —— 離散側真的編譯出來了：`bitStepTape`／`encPair` 的符號在 `.lake/build/ir/FluidTuringLean/M59_SmoothUndecidable.c`，`BitTM_step` 在 `M3b_ReversibleTM.c:610`；而 `sigmaM`／`bitEnc`／`bitVecToNat` 一個符號都沒有。三行推論就能把 σ 層 iff 換成可 `decide` 的離散述詞（§4 B3）。
- **「M56 封死連續流」** —— 只封死「精確」。M53 已經有能跑的 ε 版：`cpuField`（M53:72）是**單一自治 C^∞ 向量場**，`cpuField_contDiff`（M53:132），`cpuWindow_advances`（M53:175）一個時鐘窗把組態推進一個 TM 步，殘差 `Real.exp (-C)` 誠實外顯。
  **但我要對這一條下修正**：M53 跑的是 module-local **玩具** `sigmaRL`／`gEnc`／`gStepRL`（有限 `List` 帶、兩堆疊非空、良編碼假設），**不是** `sigmaM`／BitTM，而且 M53 自己的檔頭（M53:30-36）明寫「玩具、非真機……**禁**宣稱線三 undecidability」。正確說法是「連續流有 ε 版本，在玩具 σ 上」，不是「`sigmaM` 有連續流版本」。

### 一條值得問、但我不敢斷言的軸（M38）

`continuous_detector_isClopen`（M38:36）＋對偶 `no_continuous_detector_of_not_isClopen`（M38:61）說：非 clopen 集沒有連續 2 值偵測器。M38 的 docstring（M38:30-35）明寫這是自治耦合的**真結構障礙**，理由是**停機盆是 Σ₁ 非遞迴 ⟹ 非 clopen**。也就是說：**目標可判定，正是這個障礙論證跑不動的情形** —— 「質數可判定所以沒價值」在這一條軸上是反過來的，而六個設計、兩份價值批判與一次 FATAL 裁決都沒問。

**但這不是免費午餐，我沒有證，你也不要引用成已成立**：緊積空間上 clopen ⟺ 只看有限多格。若機器在整個緊組態空間（含非最終空白的垃圾帶）上**全停**，兩個答案盆互為開集補集 ⟹ 皆 clopen ⟹ M38 障礙確實不成立；但任意 `ℤ → Bool` 上機器不保證停，而跑多久又隨 n 無界。要用這條，必須先找到一個緊不變子空間並證全停。這是**一個該問的問題**，不是一個已到手的優勢。

---

## 4. 建議路線

放棄 PrimeReachBridge 作為下一個目標。下面按價值／成本排序；**B0–B2 與質數完全無關，B4 與這個 repo 完全無關**。

### B0 — `sigmaRL3_confinement_undecidable`（3 行，最便宜）

```lean
theorem sigmaRL3_confinement_undecidable (n : ℕ) :
    ∃ σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      ∃ (base : Nat.Partrec.Code → ℝ × ℝ × ℝ) (Target : Set (ℝ × ℝ × ℝ)),
        ¬ ComputablePred (fun code => ¬ ∃ k : ℕ, σ^[k] (base code) ∈ Target)
```

接 `sigmaRL3_reachability_undecidable`（M59:211）＋ `ComputablePred.not`。證明照抄 `M36_Corollaries.lean:26-28` 的三行。σ 線缺 M36 這個補集推論，只有流線有。

### B1 — `sigmaM_reach_iff_of`（~25 行，純重構，**行數淨減**）

把 M59:179-198 那個被丟掉的 `have key` 抬到定理層，index 型別換成 `{ι}`：

```lean
theorem sigmaM_reach_iff_of {Λ ι : Type*} [Inhabited Λ]
    (M0 : Turing.TM0.Machine Bool Λ) (S : Finset Λ) (hClosed : …)
    (init : ι → Turing.TM0.Cfg Bool Λ) (hinit_q : ∀ i, (init i).q ∈ S) (i : ι) :
    (∃ k : ℕ, (sigmaM (Mtr M0 S))^[k]
        (gEncB 8 (bitEnc (encCtrl S (ctrlOfLabel S (init i).q)) (init i).Tape))
      ∈ {x | x.1 = (bitVecToNat (ctrlCard S) (encHalt S) : ℝ)})
    ↔ (StateTransition.eval (Turing.TM0.step M0) (init i)).Dom
```

接 `reach_at_k`（M59:134）、`encTB0_fst_ne_encHalt`→ 正確名 `encTM0_fst_ne_encHalt`（M28:44）、`offset_exists`（M59:150）、`Mtr_halts_iff`（M28:113）。`sigmaM_reach_undecidable_of`（M59:164）隨後變成 4 行推論，所以這塊是把重複證明文字**刪掉**。它同時是任何「程式固定／輸入變」目標（Collatz、Goldbach、任何東西）的結構閘門。

### B2 — σ 層 characterization ＋ 四合一 Σ₁ 定位（~2 塊，零新數學，**嚴格強於現有頭條**）

鏡射 `fluid_reach_characterization`（M37:118）與 `fluid_reach_full_characterization`（M37:189）：

```lean
theorem sigmaRL3_reach_characterization (n : ℕ) :
    ∃ σ, ContDiff ℝ ⊤ σ ∧ ∃ base Target,
      ∀ code : Nat.Partrec.Code, (∃ k, σ^[k] (base code) ∈ Target) ↔ (code.eval n).Dom
```

接 B1 ＋ M59:216-249 已寫好的通用碼組裝；四合一版再接 `ComputablePred.halting_problem`（`Mathlib/Computability/Halting.lean:65`）、`halting_problem_re`（:61）。成品可以講的句子：**「存在一個顯式 C^∞ 的 ℝ³ 自映射，其軌道可達性 many-one 等於停機問題，且恰落在 Σ₁\Δ₁」** —— 比現在的 M59:211 強，零新數學，零誠實風險。M37:6-9 就是你自己寫下的這個模式的動機。

### B3 — `reach_at_k_tape`（3 行）＋ repo 的第一次消防演習

```lean
theorem reach_at_k_tape (M : BitTM) (v vhalt : Fin M.m → Bool) (T : Tape Bool) (k : ℕ) :
    ((sigmaM M)^[k] (gEncB 8 (bitEnc v T))).1 = (bitVecToNat M.m vhalt : ℝ)
      ↔ ((bitStepTape M)^[k] (v, T)).1 = vhalt
```

風險近零：`reach_at_k` **自己的證明** M59:143-145 已經 `rw` 到那裡並 `change` 成這個述詞。RHS 是編譯出來的 C 碼（`bitStepTape` 在 `.c` 裡）且是 `Decidable`（`Fintype.decidablePiFintype`）。配已存在的 `cnotTM`（M3b:478，已經 `by decide` 關掉，M3b:483-485），倉庫拿到它**從來沒有過**的第一次橋樑演習 —— 現在 `FluidTuringLean/*.lean` 沒有任何 `Float`、沒有 `#eval`、沒有 `Decidable` harness。這就是你自己的 drill.sh 教條：這座橋沒有人點過火。
**只用 kernel `decide`**；`native_decide` 會加 `Lean.ofReduceBool`，直接打臉 `README.md:9` 的標準三公理宣稱。

### B4 — `PrimrecPred Nat.Prime`（獨立 mathlib PR，與本 repo 無關）

缺口我重驗過：Mathlib/ 裡同時出現 `Primrec` 與 `Nat.Prime` 的檔案 = 0。材料全在：`Nat.prime_def_lt'`（Prime/Defs.lean:114）、`PrimrecRel.forall_lt`（Primrec/List.lean:**507**，不是 :452 的 `PrimrecPred.forall_lt`）、`Primrec.nat_mod`（Basic.lean:728）、`Primrec.nat_le`（Basic.lean:610）。若要 O(√n)：`Primrec Nat.sqrt` 已證好（List.lean:779）＋ `Primrec.nat_div`（Basic.lean:710）。
這塊有 repo 外消費者、是 mathlib 形狀、與流體無關 —— 它是整份文件裡唯一通過 vortex 測試的新數學。

### B5 — 真的想要一個有名字的程式的話：不要選質數

先做 index 泛化（B1 一半，M37:51 與 M37:89 也要），然後選 **Collatz**。mathlib 在此 pin 完全沒有 Collatz，所以要自己定義；但成品是「**兩個都還開著**的敘述之間的等價」，而不是 Δ₁⟺Δ₁。若你要的是外部分析真正在講的「流」形狀，on-ramp 是 **M37:51，不是 M59** —— 那裡目標是任意 `Hcfg : Set M.Cfg`，兩個答案區與帶上見證因數都是自然形狀。

### 從敗選設計搶救、不論做哪一塊都該帶走的三個習慣

1. **具名見證，不要 ∃ 包裝。** ∃ 包裝只有在 payload 本身防作弊時才誠實：`¬ComputablePred` 是；對可判定謂詞的 iff 不是 —— σ := `id`、`base n := if Nat.Prime n then p else q`、`Target := {p}`，三行就滿足整個命題。把 σ／Target／base 提成 top-level def，`n` 在定理裡只出現一次（在 `tapeOf n` 裡），反循環就變成 `#check` 得出來的，不是承諾出來的。
2. **排除區間要證成定理，不要留成側條件。** `small_silent (n) (hn : n < 2) (k) : … ≠ vP ∧ … ≠ vC`。而且合數側右式必須是 `2 ≤ n ∧ ¬ Nat.Prime n` —— 光寫 `¬ Nat.Prime n` 在 n = 0, 1 是**假的**（`Nat.not_prime_zero` Defs.lean:48、`not_prime_one` :57）。
3. **免費的 scope 句，你已經有了卻沒在用。** `sfloor_not_analytic`（M60:78）已經機器證明這套 scaffold **永遠升不到 analytic**（`sigmaM` 經 `sfloor`，M46:75 → M58:90），而 `sround_analytic`（M60:100）說障礙精確定位在「精確讀符」。六個設計的誠實範圍段都只說「顯式 C^∞」，沒有一個引用這條 kernel 背書的不可能性。免費拿。

---

## 5. 誠實範圍（要貼進模組檔頭的原文）

**若你最後還是蓋了質數橋**，下面這段必須逐字出現：

> **★誠實範圍★**
>
> 1. **本定理不產生任何可計算性內容。** `Nat.Prime n` 可判定（mathlib `Nat.decidablePrime`，`Mathlib/Data/Nat/Prime/Defs.lean:162`），而 `∃k, σ^[k](base n) ∈ Target` 經 `reach_at_k` 恰等價於它，兩邊都在 Δ₁。`reach_at_k`（`M59_SmoothUndecidable.lean:134`）本來就對所有 `BitTM` 全稱量化且零假設，本模組做的是**全稱實例化**；現有鏈唯一製造內容的一步是 `ComputablePred.halting_problem`（M59:200），而質數版必須刪掉它。**這是一個 characterization，不是不可判定性結果**，也不是關於質數的新知識——質性內容全部由 `Nat.prime_def_lt'` 流進來，沒有一滴流出去。
> 2. **本構造一步也跑不動。** `sigmaM`（M59:122）`noncomputable` 有兩個各自充分的原因：`sigmaRL3`（M58:90）每個分支除以 `(K : ℝ)`，且經 `smoothSelect`（M44:24）呼叫 `Real.smoothTransition`。**連輸入編碼器也不可算**：`bitVecToNat`（M57:59，Classical `Fintype.equivFin`）、`natToBitVec`（M57:75，`Function.invFun`），故 `bitEnc`（M57:146）與 `δqOf/δwOf/moveOf`（M57:162-167）都不出 code。基點 x₀ 的第一座標在 Lean 裡寫不出數字，n = 2 也印不出來。可以說「我們跑了機器、答案靠一條字面等式定理搬過去」；**不可以**說「我們跑了那個光滑映射」。
> 3. **不是流體、不是 Euler、不是 NS，甚至不是流。** `sigmaM` 是 ℝ³ 上的離散自映射。`README.md:89`「These results are **not** claims about real Navier–Stokes or physical fluids.」原封適用。
> 4. **目標只讀第一座標**（M59:177 的 `{x | x.1 = …}`），帶不可見，因此本橋能宣布合數、**永遠吐不出因數**。
> 5. **質數側與合數側是兩個不同的 σ**（`SU` 由 `codeSupp cu Cont'.halt` 造，M59:227 → `ctrlCard` → `Mtr.m` → σ；且 `Mtr` 把所有停機塌成單一字 `encHalt S`，M27:35-38 ＋ M26:60）。「一個 σ、兩個集合 U_prime / U_composite」**不是**本模組交付的東西。
> 6. **反循環是紀律，不是 kernel 幫你擋的。** `#print axioms` 在這裡是瞎的：`Nat.decidablePrime` 可計算，所以 `if Nat.Prime n then _ else _` 造的假橋會顯示標準三公理而順利過關（倉庫自己有這形狀的合法例子 `blowupFamily`，M34:41，而它還得寫 `open Classical in`；質數版連那個都不用，更隱形）。真正的保證是：σ 與 Target 綁在 `∀ n` 外面、機器與答案字的 telescope 裡沒有 `ℕ`、`tapeOf` 被 spec 引理逐點釘死、`runBound` 不提 `Nat.Prime`。這四件要人讀簽名去檢查。
> 7. **這套 scaffold 永遠只能到 C^∞。** `sfloor_not_analytic`（M60:78）已證 `sfloor` 非 analytic，而 `sigmaM` 經 `sfloor`（M46:75 → M58:90）。
> 8. 本模組名稱不得被引為 headline。

**若你做的是建議路線 B2**（我推薦的那條），誠實範圍只需要兩句：「本定理是既有封頂 `sigmaRL3_reachability_undecidable`（M59:211）內部 reduction iff 的外顯，非新內容來源，模式沿用 M37；σ 為 C^∞ 而非 analytic（`sfloor_not_analytic`，M60:78），且 `sigmaM` 與其編碼器皆 `noncomputable`，本定理不蘊含任何可執行性。」

---

## 6. 還沒查的

- **沒有跑 `lake build`**（任務禁止）。§4 每一塊磚的行數是讀簽名估的，「應該會過」沒有一個是機器背書的。
- **0 sorry／標準三公理未驗。** 我沒跑 `#print axioms`。`FluidTuringLean/*.lean` 裡 45 處 `\bsorry\b` 全在 docstring 散文裡（如 M5:21、M6:44），零個在 tactic 位置 —— 但「散文說零 sorry」不是證據。
- **git 快照：其實可驗，而且對上了。** `git` 二進位被 Xcode 授權擋住（`/usr/bin/python3` 同樣，exit 69），但 `.git` 可以直接讀：`refs/heads/main` = `f8bc05117de9c074be103576210b14e9818b2947`，commit object 解壓後 `author liweiting <aa5986737@gmail.com> 1784524253 +0800` = 2026-07-20 13:10:53，`refs/remotes/origin/main` 同 hash。工作樹 85 個追蹤檔中 **2 個**有未提交修改（`README.md`、`docs/RELEASE_NOTES_v0.9.md`），**66 個 `.lean` 全部與快照 byte-identical**，所以外部分析的每一條技術主張都可以無快照保留地對這棵樹評估。**沒查的是**：本機物件庫是否等於 GitHub 今天送的東西（需要網路）。
- **一個未修的 repo bug**：`docs/RELEASE_NOTES_v0.9.md:28` 說「`README.md` on `main` has been corrected」—— main 的 README blob 裡**沒有**那個更正，更正只存在於未提交的工作樹編輯。
- **mathlib 行號來源**：`fluid_turing_lean/.lake/packages` 裡**沒有** mathlib（只有 Cli／LeanSearchClient／Qq／aesop／batteries／importGraph／plausible／proofwidgets）。所有 mathlib 引用讀自 `contact_geometry_lean/.lake/packages/mathlib`，兩邊 `lake-manifest.json` 的 mathlib `inputRev` 都是 `v4.32.0-rc1`（我對過）。
- **`.c` 檔是某次舊 build 的產物**，我沒有重建，所以它反映的是那次 build 當時的原始碼，不必然是這棵工作樹。
- **質數盆是否 clopen：沒證，不要引用。** §3 末段已說明機制與缺口。
- **仍未讀的模組約 15 個**（本輪補讀了 M20:69、M36 全、M37:51、M38 全、M53、M60、M3c 簽名）：M3_Encoding、M4_Suspension、M9、M18、M19、M21、M22、M24、M35、M39、M40、M41、M42、M43、M48、M51、M52。其中 M39→M40→M41→M51→M52 是連續流線的中段，我只從 M53 的檔頭間接看到它們。
- **一項對前輪的更正**：`sigmaM` 在 **M59:122**、`sigmaM_contDiff` 在 **:126**（我用 `grep -n` 重驗）。某一輪 recheck 說是 :121/:125 並指 orchestrator 弄錯 —— 弄錯的是那一輪。同樣重驗：`have key` 在 :179、`rw [key]` 在 :199、`halting_problem` 在 :200、`offset_exists` 在 :150。


---

## 附錄 A — 設計評分

- **A-partrec** avg=6.0
  - 致命: honesty — does the artifact, standing alone without its docstring, tell the truth about itself?: The deliverable theorem is cheat-satisfiable, and the design's own anti-circularity guard cannot be applied to it. L9 states `∃ σ, ContDiff ℝ ⊤ σ ∧ ∃ base Target, ∀ n, (∃ k, σ^[k] (base n) ∈ Target) ↔ Nat.Prime n`. Take σ := id (`contDiff_id`), base n := if Nat.Prime n then (1,0,0) else (0,0,0) (computable — `Nat.decidablePrime`, mathlib Prime/Defs.lean:162, so not even `Classical.choice` is added), Target := {x | x.1 = 1}. Three lines, standard three axioms, and every one of L1–L8 is unnecessary. The statement therefore records NONE of the work; it is strictly weaker than the prose claim it will be quoted as. The existing M59 headline is immune to exactly this because its ∃-wrapped payload is `¬ ComputablePred` (M59_SmoothUndecidable.lean:211-214, re-read verbatim), which no cheat witness satisfies — the moment you swap the payload to an iff with a decidable RHS, the ∃-wrapper stops being harmless and becomes the whole problem. Worse, the design diagnoses this precisely ("a bridge author can define any of them by `if Nat.Prime n then _ else _` … GUARD: a reviewer checks this from the signatures alone. Do not accept a version where the target word or the machine takes `n` as an argument") and then writes a deliverable in which σ, base, Target and `cP` are all existentially bound inside the proof — `cP` arrives via `obtain ⟨cP, hcP⟩ := exists_code …`, so it is proof-local and has no signature. There are no signatures to check. Non-circularity is therefore PROMISED, not machine-checkable, in the exact statement the design says is the point. Two smaller accuracy slips inside the honesty paragraph itself, which is the one paragraph whose job is accuracy: (i) L2 cites `Part.assert_dom` as the lemma giving `.Dom ↔ Nat.Prime n` — no such lemma exists at this pin (mathlib Mathlib/Data/Part.lean has `assert_pos`:417, `assert_neg`:421, and one-directional `assert_defined`:575); the fact is true definitionally, but it is stated as a citation and not tagged unverified while other items are, which is the repo owner's own logged failure mode 「把推論寫成引文」. (ii) Honest-scope §4 says "even the repo's own fluid theorems are conditional on hypotheses the repo itself proves vacuous (`reebBeltramiRealization_trivial`, M5_ReebInterface.lean:144)"; README.md:9-20 states both headline theorems are **unconditional**, and M5:141-145 is a self-audit showing the abstract SIGNATURE layer is vacuous — not a caveat hanging over the headline. It is an underclaim rather than an overclaim, but it misdescribes the owner's own work in the document that exists to describe it correctly. || value-per-token: The deliverable is worth approximately nothing, and three independent lines of evidence say so. (1) LOGICAL: `reach_at_k` (M59:134) is `∀ (M : BitTM) (v vhalt) (T) (k)` with ZERO side hypotheses, so N9 is universal instantiation. The one line in the whole chain that creates content is M59:207 `exact ComputablePred.halting_problem n hcomp`, reached because the plugged-in predicate is undecidable; `Nat.Prime` is decidable (`Nat.decidablePrime`, Prime/Defs.lean:162), so the prime bridge is precisely the existing headline with its payload line deleted — Δ₁ ⟺ Δ₁. (2) EMPIRICAL, which I re-counted myself: the "plug a concrete machine into the generic theorem" move has been executed five times in this repo (`cnotTM_suspension_simulates` M6:216, `bennettTM_…` :229, `ctrlDemoTM_…` :239, `ctrlFullTM_…` :248, `trackWalkTM_suspends` M8:22) and every one has 1-2 references, all self/docstring — ZERO downstream consumers, against 7 for `reach_at_k`. N9 would be the sixth terminal leaf of an already-measured shape. (3) THE OWNER ALREADY RULED: docs/GPAC_ROADMAP.md:142 「玩具家族=有限組態可判定死路」, with 「邊際價值弱於 M33 無條件」 recurring at :87, :102, :119, :134, :173, :243. Compounding it: the result is not mathlib-shaped (bespoke `BitTM`), cannot be exercised for any n (both σ and the base point are noncomputable — M58:90 division by `(K:ℝ)`, M57:59 Classical `Fintype.equivFin`), and the headline shape the external analysis actually wants (one σ, U_prime + U_composite) is unreachable here at all, since `Mtr`'s width is `ctrlCard S` and `SU` derives from `codeSupp cu` (M59:223), so a second program gives a different σ. The design concedes every one of these in its own §1-§6 and still presents N5/N9 as the deliverable.
- **D-minimal-honest** avg=6.0
  - 致命: lean-feasibility: will every link actually compile against mathlib rev 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56 (v4.32.0-rc1), and is any link secretly a research problem?: No fatal flaw: nothing here is a research problem and no cited API is missing. But two defects are real at the compile level, and the second is the one that would eat the schedule.

(1) L2's stated signature does not typecheck. `Part.assert (p : Prop) (f : p → Part α) : Part α` (Mathlib/Data/Part.lean:378), so `Part.assert (Nat.Prime n) fun _ => (0 : ℕ)` is a type error — the second argument must land in `Part ℕ` (`fun _ => Part.some 0`). The design writes the bad form twice (CHAIN L2 and the NEW BRICKS list) while an earlier probe had it right, so it is drift, not ignorance. Consequence beyond the typo: `REPred` unfolds to a `PUnit`-valued assert (RE.lean:157), so retyping needs `Partrec.map` (Partrec.lean:407) PLUS a `Part.ext`-level step proving `(Part.assert p fun _ => Part.some ()).map (fun _ => 0) = Part.assert p fun _ => Part.some 0`. "~5 lines" is optimistic; 5–15 is honest.

(2) L10 CANNOT BE STATED as the design presents it, and it is the design's only anti-circularity guard ("ship it in the same file as L9 or do not ship L9"). In L9 `base` is existentially bound INSIDE the theorem (`∃ (base : ℕ → ℝ×ℝ×ℝ) (Target : …), ∀ n, …`), so there is no `base` for `prime_base_fst_const (n) : (base n).1 = (base 0).1` to talk about. To get one you must choice-extract two existentials that M59 only ever `obtain`s inside a tactic proof — `tm1to1_enc` (M23_TM1to1Bool.lean:50, `∃ n enc dec, …`) and `exists_code` (Config.lean:267) — into top-level noncomputable defs, then turn M59:224-230's `set M1/M2/S0/S1/S2/SU` block into definitions. That is ~30-60 lines, not "1–3 lines". Worse, it drags in an instance-hygiene trap the design's generic "L7 組裝摩擦" note does not name: M59 gets its `DecidableEq`/`Fintype` instances from a bare `classical` at M59:223, which works because everything downstream lives in one tactic block; once `SU_P` is a top-level def built from `Finset.biUnion`/`trSupp`, the `Classical.decEq` instance must be fixed at definition site (`open Classical in` per def) and every later lemma must elaborate to the SAME instance or the `Finset` terms stop being defeq and `hinit_q`/`hClosed` stop copying verbatim. That is precisely where a first run dies. (Once `base` is a top-level def, the `rfl` itself is plausible: mathlib `TM1to0.trCfg`/`TM1to1.trCfg` carry the label past the tape, and `univTM1Cfg cu v`'s label component is `(some (trNormal cu Cont'.halt)).map …` with `v` entering only the tape — M31_TM2to1Univ.lean:18-24, verified.)

Minor, but it is a citation error in the one brick that is new mathematics: the design cites `PrimrecRel.forall_lt` at Primrec/List.lean:452 and calls :452 "二元版". At this pin :452 is `PrimrecPred.forall_lt` (unary); the binary `PrimrecRel.forall_lt` is at :507. The lemma the design needs exists, at a different line than it says. || Honesty / anti-overclaim: does the shipped statement say only what it proves, is non-circularity machine-checkable rather than promised, are n=0,1 and both answer-directions handled, and would this repo's owner sign the honest-scope paragraph as written?: Not fatal, but one affirmatively false protection claim plus one missing disclosure — and both sit inside the honesty apparatus itself, which is where they cost the most. (1) FALSE GUARD. L9's note says "the quantifier order is itself the anti-circularity guard: σ and Target are bound OUTSIDE ∀ n, so neither can branch on `Nat.Prime n`". σ and Target, yes; `base : ℕ → ℝ×ℝ×ℝ` is *also* bound outside `∀ n` and is still a function of n, so it can branch pointwise — which is precisely the shape the repo already ships legitimately at FluidTuringLean/M34_LiteralBlowup.lean:41 (`if (code.eval n).Dom then smoothSwitchSol 1 else fun _ ↦ 1`) and which README.md:88 singles out as the reduction-level case ("the trajectory is selected by the answer rather than computing it"). honest_scope §6 half-retracts this, but still lists 量詞位置 as a real guarantee. Worse, the design thereby *understates its own true strength*: on this route `base n = gEncB 8 (bitEnc … (univTM0Cfg enc dec enc0 cP [n]))` is not author-chosen at all — `cP` is `obtain`ed from `exists_code` and carries no n, and n enters only inside the list literal `[n]` via mathlib's `trList`. That is a far better argument than the one given, and it is not made. (2) MISSING DISCLOSURE. L9's exported proposition is satisfiable by a trivial witness: take σ = `id` (ContDiff ⊤), `base n = if Nat.Prime n then p else q`, `Target = {p}`; the iff then holds by `if`-splitting, a ~5-line proof touching none of M23/M27/M28/M32/M57/M58/M59. So the *statement* carries zero information — all content lives in the unexported defs. honest_scope §1 says "no new computability content", which is close but not the same sentence, and a reader of the theorem alone cannot tell the two apart. L10 `prime_base_fst_const` is the right instinct but certifies only coordinate 1 (the state word, input-independent by construction, cf. M31_TM2to1Univ.lean:21-25); the two *tape* coordinates are exactly where n lives and stay uncertified, and the design never says so. The fix is cheap and already exists in this audit's own D5 material: pin the tape pointwise (a `tapeOf_nth`-style spec against `trList [n]`), and add one sentence to §6 — "此命題本身可被平凡見證滿足（σ = id + case-split base），內容全在具名定義裡，讀者必須看 defs 而非只看定理". Note this hole is inherited, not invented: `fluid_reach_characterization` (M37_ReachCharacterization.lean:118) and even `sigmaRL3_reachability_undecidable` (M59:211) are existential in `base` too and admit the same classical cheat — which is why the owner, who wrote README.md:88 to draw exactly this line, is the one person certain to ask about it. || value-per-token: The design is named after, chained around, and structured to deliver a theorem it proves is worthless — and then spends the majority of its tokens building it anyway.

L9 is universal instantiation. `reach_at_k` (M59:134-136) is `∀ (M : BitTM) (v vhalt : Fin M.m → Bool) (T : Tape Bool) (k : ℕ)`, with zero side hypotheses. Feeding it a prime machine adds no logical strength. The only content-producing step in the existing chain is `exact ComputablePred.halting_problem n hcomp` (M59:206-207), and the prime version's defining move is to delete exactly that step. Both sides of the resulting iff are Δ₁. The design says all of this itself, in honest_scope §1 and in its own VALUE risk — and then keeps L9 as the title and as the terminus of a 10-link chain.

The cost accounting makes this decisive. Of the 8 bricks, L8 and L8b are the valuable ones and are independent of primality; L1 is valuable and independent of this repo entirely. L2, L3, L6, L7, L9, L10 exist only to serve L9 — that is six of eight links, including every link with real elaboration friction (the design's own risk list flags L7's `S0 := codeSupp cP Cont'.halt` Finset/Fintype/DecidableEq re-elaboration as "工具首跑必有瑕疵" territory). So the majority of the labor buys a 科普 vignette in a repo whose owner already ruled on this genre twice (docs/GPAC_ROADMAP.md:142 「玩具家族=有限組態可判定死路」, and :243/:256 「邊際價值仍弱於且冗餘於主線 M33 無條件」, with 「未證 undecidability」 listed as the demerit).

The zero-consumer evidence is in-repo and I re-counted it: `cnotTM_suspension_simulates` 1 reference, `ctrlDemoTM_suspension_simulates` 1, `trackWalkTM_suspends` 1, `bennettTM_suspension_simulates` 2 (self + docstring). Five prior "plug a concrete machine into the generic theorem" bricks, five terminal leaves. L9 would be the sixth, and the design does not explain why this one breaks the pattern — because it doesn't.

Two unbudgeted costs compound it. First, the net new content of this design over the death-point probes it was written from is close to zero: L8 and L8b are the probes' own GO-SMALL recommendations re-packaged with tidier citations, so the design's marginal value-per-token is being charged against work already done. Second — and nobody in this stack mentions it — the repo is capped and *published*: README.md:5 advertises "65 modules · 0 sorry · axioms limited to the mathlib standard three", and the project is on Zenodo with a DOI at tag v0.8. Landing M63 means a new module count, a new tag, a new Zenodo version, and a README/honest-scope amendment. That re-release cost is real and is budgeted at zero here. It is tolerable for L8b (strictly stronger headline, worth re-cutting for). It is not tolerable for L9.

Minor receipt defect, in the design's favour and therefore worth flagging as sloppiness rather than error: L1 cites `PrimrecRel.forall_lt` at Mathlib/Computability/Primrec/List.lean:452 and its risk note calls that citation 「二元版」 requiring diagonalisation. At the pinned rev, :452 is `PrimrecPred.forall_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∀ x < n, p x` (unary) and :507 is the `PrimrecRel` binary version. The unary form at :452 is not what L1 needs either (primality's bound and subject are the same `n`), so the diagonalisation worry stands — but the line number and the name do not match each other, in a document whose whole discipline is that a claim without file:line is not evidence.
- **C-executable** avg=5.7
  - 致命: lean-feasibility: will each link actually compile against mathlib rev 360da6fa (v4.32.0-rc1), is each cited lemma real, and which link is secretly a research problem: Not a compile blocker — a misplaced firewall plus an undetermined deliverable. (1) The STOP RULE fences A2 (the tape-level simulation PROOF) but leaves E2 (authoring a *correct* binary trial-division `BitTM`) on the cheap side at 70-140 lines. Yet L3's whole value is a `#eval` drill over n∈[0,1000] that only means anything if Mp is genuinely correct — and by the design's own receipts the alphabet is Bool with blank = one of the two symbols (mathlib Tape.lean:20), so there is no marker and a blocked/separator discipline is forced. Authoring and debugging that as total `next/write/move` over `Fin m → Bool` is realistically 300-800 lines, 2-5× the budget. If you cannot build Mp, E3 and E4 are empty too; the "shippable unit E1-E5+A1" is not shippable at the advertised price. (2) The flagship artifact `orbit_997` is almost certainly unreachable by kernel `decide`. The design's own k₀ estimate is 10⁵-10⁶ steps; kernel reduction of `Nat.iterate` at a literal that size, over a ListBlank term that grows every step, is hopeless regardless of the (correct) observation that ListBlank ops reduce by rfl on `mk`. Feasible n is toy-sized (k₀ ≲ 10³, i.e. single- or low-double-digit n). The design names the `decide`/`native_decide` fork honestly but declines to pick, so the deliverable is undetermined: either a toy-n certificate that nobody will quote, or `Lean.ofReduceBool` breaking README.md:9. It should have pre-committed to small-n-kernel and renamed the headline accordingly. (3) One unnamed API link: `tapeOf_nth_pos … = n.testBit i` needs `(Nat.bits n).getI i = Nat.testBit n i`, which does NOT exist at this pin — Data/Nat/Bits.lean ships only `zero_bits` :240, `bits_append_bit` :243, `bit0_bits` :249, `bit1_bits` :253, and the sole bits↔bit relationship in the tree is at index 0 (Bitwise.lean:169). ~15 lines by `Nat.binaryRec`, escapable via the design's own "explicit blocked encoding" fallback, but uncosted and sitting inside the brick that carries the anti-circularity guarantee. (4) A2 itself remains a genuine wall, correctly labelled — so `prime_iff`, the theorem the design is named after, has no credible path here. || value-per-token: is the theorem obtained worth the Lean labor, who consumes it, and is it a new object or an instance of an existing general theorem?: The headline has zero logical content, and the design's own risk list concedes it. `reach_at_k` is already ∀(M : BitTM) with no hypotheses, so authoring `Mp` and plugging it in is universal instantiation — the only place the existing chain gains content is the step the prime version must delete (`ComputablePred.halting_problem`, M59:199/:268). The repo has already run this exact move five times and I counted the consumers: cnotTM_suspension_simulates 1, ctrlDemoTM_ 1, ctrlFullTM_ 1, trackWalkTM_suspends 1, bennettTM_ 2 (all self/docstring) versus reach_at_k 7 and fluid_reach_characterization 3. Five terminal leaves, zero downstream Lean consumers, and this would be the sixth. The owner's own roadmap already ruled on the genre: docs/GPAC_ROADMAP.md:142 「玩具家族=有限組態可判定死路」 and :243 「邊際價值仍弱於且冗餘於主線 M33 無條件」, with 「未證 undecidability」 listed as the demerit. Meanwhile all the ∀n value sits behind A2, estimated 800–3000 lines with no precedent — the repo has never authored a TM0 machine, and M3d spent 1195 lines to reach a BitTM that still disclaims simulation semantics (M3d:853-855). Invoke the STOP RULE and what ships is per-n certificates with no logical content plus a drill. And the strictly stronger cheaper alternative is verified and unclaimed: `grep -n "characterization\|REPred" M59` = 0 hits, while the needed iff is already written as the local `have key` at M59:181-205 and thrown away by `rw [key] at hcomp` at :206 — M37:6-9 is the owner's own precedent for lifting it (「把封頂內部藏的還原 iff 抬到定理層」), M37:117 and M37:189-206 are the templates, and unlike the toy leaves that line has consumers. The design lists this in its own risk section and writes 「那個比 PrimeReachBridge 划算」. A design that names a cheaper strictly-stronger substitute for the same owner in the same repo has answered the value question against itself.
- **B-bittm** avg=4.7
  - 致命: lean-feasibility: will this chain actually compile against mathlib rev 360da6fa (v4.32.0-rc1), lemma by lemma, and which links are secretly research problems: The central new definition does not typecheck as specified, and the crux theorem is stated falsely. (a) `dibitify : LogicTM → BitTM` needs `m := bits(Lbl) + …` and `embed`, but `LogicTM` as declared (`Lbl : Type`, `inst : DecidableEq Lbl`, `fin : Fintype Lbl`, `δ`) carries NO label→bit-vector encoder. Generically the only way to manufacture `Lbl ↪ (Fin k → Bool)` is `Fintype.equivFin` — which is precisely the Classical, noncomputable trap the design itself indicts at M57_BitTMBridge.lean:59. If that happens, `Mp` is noncomputable, `theorem vP_ne_vC := by decide` (L4) fails, and B12's whole `#eval`/`decide` payoff — the one concrete deliverable this design has over Route B — evaporates. Fix is cheap (add `enc/dec/encdec` fields exactly as mathlib's TM1to1 does, PostTuringMachine.lean:~700, already supplied to the repo at M23:50), but as written the design's load-bearing brick has a hole. (b) L3's crux `dibit_simulates (L) (c) : (bitStepTape (dibitify L))^[6] (embed c) = embed (L.lstep c)` is stated for ALL `c`, while L5 demands the four answer words be raw BitTM self-loops that BYPASS the 6-step gadget. Those are inconsistent unless `dibitify` special-cases absorbing labels and `LogicTM` gains an "absorbing" predicate — neither exists in the design. (c) Unbudgeted and worse than (a)+(b) combined: every → direction (`Mp_prime_iff`, `Mp_comp_iff`, `small_silent`) is a ∀k claim — "the orbit never shows the wrong answer word at ANY k" — but L8-L11 deliver only ∃t and macro-boundary equalities. You need a full reachable-set invariant covering every intermediate head position AND every gadget phase, or a segment decomposition of [0,t). The repo's own precedent proves this cost is real: `trackWalkTM_reaches_marker` (M3e_FixedTM.lean:577) carries `hpath : ∀ i : ℕ, i < p → ¬(…)` as a hypothesis it had to pay for. (d) The LOC estimate is wrong because the design's own calibration is wrong: it asserts "NO precedent in the repo … only `BitTM.ofPerm` permutation demos". False — FluidTuringLean/M3e_FixedTM.lean is 626 lines of hand-authored non-permutation BitTM work (`fixedEnc4` multi-track interleave with injectivity at :231, `trackWalkTM_next_cross` :484 / `_nonmarker` :513 / `_bounce` :569, and the walk induction at :577). One single-scan walk lemma plus its four supports costs ≈160 lines there, over a ONE-field tape with the marker at a known offset. The design needs ~8 such over a two-field shifted layout, so B7 alone is ~1200-1600 LOC, not 400-700; realistic total is 3500-6000 LOC, not 1400-2000. (e) The "every unused bit-vector routes to vD" side condition is called `decide`-checkable; at m≈13 that is 16384 cases each producing a `Fin 13 → Bool`, which kernel `decide` will not survive — though on the invariant route it is moot. || honesty: The non-circularity certificate — the single most load-bearing honesty claim in the document — is misdescribed inside the very paragraph whose job is to prevent overclaim. §6 tells the reviewer: "`tapeOf` is pinned pointwise to `Nat.testBit`-shaped data by `tapeOf_nth_nat`/`tapeOf_nth_neg` (L6)". Two things are wrong. (1) This design is UNARY: L6 defines `symTape n = .bar :: List.replicate n .one ++ [.bar, .one, .one]`. There is no binary expansion anywhere in it, and `grep -rn testBit FluidTuringLean/*.lean` = 0 hits in the repo. `Nat.testBit` is residue from the earlier binary proposal; the qualifier survived the change of carrier while the object under it changed — exactly the owner's own logged mechanism 「換載體必掉限定詞」, occurring in the anti-overclaim section. (2) More seriously, the lemma cited does not do the work claimed. L6's `tapeOf_nth_nat` states `(tapeOf n).nth (i : ℤ) = (dibitList n).getI i`, where `dibitList` is the design's OWN definition, derived from `symTape` — so the "spec lemma" is a near-`rfl` self-pin. A circular encoder `symTape n = if Nat.Prime n then A else B` would satisfy its own `tapeOf_nth_nat` just as happily. Compare the earlier D5 shape, which pinned `tapeOf n` to `Nat.testBit`, a mathlib function that demonstrably cannot mention primality: that pin was an external anchor and defeated the attack; this one is a tautology and defeats nothing. The guard has degraded from a certificate to a naming convention while the prose kept the old strength claim. The actual surviving guard is weaker and purely manual: a human reads `List.replicate n .one` and sees no primality — which §6's own five-item checklist covers under "read the definition", but is not what the sentence says. Not fatal to the construction (one struck sentence plus an honest rewrite: "the guard is that `symTape` is visibly `List.replicate`; the spec lemmas are `rfl` and certify nothing on their own"), but fatal to signing off on the paragraph as written, because a reviewer who trusts it will believe an external anchor exists when it does not. Two smaller items in the same family: §1 calls σ_P "one fixed explicit C^∞ map", which §3 then retracts (its transition tables route through Classical `Fintype.equivFin`/`Function.invFun`, so "explicit" survives only in the repo's loose 顯式 sense); and L13's → direction for `Mp_prime_iff` is assembled from "`vP_ne_vC` plus determinism" with no named brick discharging transient visits to `vP` on composite inputs — the risk list flags the hazard but no lemma in the 12-brick list owns it, which is a hypothesis without a concrete witness by the owner's own rule. || value-per-token (is the theorem worth the Lean labor; who consumes it; new object or instance of an existing general theorem): The deliverable is universal instantiation of a hypothesis-free ∀-theorem at a decidable predicate, priced at ~1400-2000 LOC, while a strictly stronger theorem sits unclaimed at roughly 1% of the cost — and I confirmed both halves of that.

Cost side. `reach_at_k` (M59:134) quantifies over every `BitTM` with zero hypotheses, so `prime_orbit_iff` adds a Lean declaration, not a theorem. The content-creating step in the existing chain is the one this design deletes: `sigmaM_reach_undecidable_of` ends `rw [key] at hcomp; exact ComputablePred.halting_problem n hcomp` (M59:206-207). Swap in a decidable predicate and that tail is gone.

Consumer side, measured not asserted. I counted references over FluidTuringLean/*.lean: `cnotTM_suspension_simulates` 1, `ctrlDemoTM_suspension_simulates` 1, `ctrlFullTM_suspension_simulates` 1, `trackWalkTM_suspends` 1, `bennettTM_suspension_simulates` 2 (self + docstring) — i.e. zero downstream consumers across five prior instances of exactly this "plug a concrete machine into the generic theorem" move, each a one-line proof. Versus `reach_at_k` 7 and `fluid_blowup_undecidable` 7. This design is the sixth leaf of that shape at a thousand times the unit cost. `grep -rniE "prime|primality" FluidTuringLean/ docs/ README.md` = 0 hits: nothing in the repo is waiting for it.

Opportunity side. `grep -n characterization FluidTuringLean/*.lean` returns M37 hits and ZERO M59 hits — the flow line got `fluid_reach_characterization` (M37:118) and the four-in-one `fluid_reach_full_characterization` (M37:189-206, iff ∧ ¬ComputablePred ∧ REPred ∧ ¬ComputablePred∘complement, discharged in 6 lines by `rw [heq]; exact ComputablePred.halting_problem(_re) n`), and the smooth-map line never did. The iff it needs is already fully constructed as the local `have key : … = fun code => (code.eval n).Dom` at M59:181-205 and then thrown away by `rw [key] at hcomp`. Extracting it is ~3 bricks of copy, yields a strictly stronger headline than the current M59 one, and has a compiling template to mirror line-for-line. Spending 1500-2000 LOC on a Δ₁⟺Δ₁ restatement while that sits discarded is the whole case against this design.

Owner precedent, in his own words: docs/GPAC_ROADMAP.md:142 「玩具家族=有限組態可判定死路」, and :243-245 「主線 BitTM、未證 undecidability … 邊際價值仍弱於且冗餘於主線 M33 無條件」. The roadmap already ruled on this genre.

Secondary but real: B3 (`dibit_simulates`, 6-phase gadget across the odd/even boundary and the tape origin) is ~70% of the risk with no in-repo precedent — the repo has never authored a TM0 machine at all, and M3d_BennettTM.lean is 1195 lines whose headline `def bennettTM : BitTM := BitTM.ofPerm …` (M3d:855) still disclaims simulation semantics in its own docstring (M3d:853-854 「模擬語意 = 待決清單」). So the calibration point for "hand-author a machine and prove it simulates something" in this repo is: attempted once, 1195 lines, stopped before the hard half. If B3 fails, links 4-14 are unsalvageable. The design says all of this in its own risk section, which is to its credit as analysis and is also its own strongest argument for rejection.


---

## 附錄 B — 完整性批判（漏了什麼）

## WHAT THIS AUDIT MISSED

### 1. The BitTM-parametric **flow** bridge — nobody opened it, and it falsifies the audit's central structural conclusion

Every claim, probe and design in this stack concluded some version of: *"a prime machine gets `reach_at_k` + `sigmaM_contDiff` from M59 and nothing else"*; *"the characterization chain is welded to `Nat.Partrec.Code` / `Mtr`"*; *"σ is a discrete ℝ³ self-map, so no flow statement is available"*; *"the Target reads only the first coordinate, so two answer regions / a witness divisor are unreachable."*

All four are false, because of a theorem nobody in the audit cited once:

`/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M37_ReachCharacterization.lean:51-58`

```
theorem bitTM_bennett_characterization (M : BitTM)
    (Hcfg : Set M.Cfg) (init : Nat.Partrec.Code → M.Cfg) (n : ℕ)
    (hHclosed : ∀ code, init code ∈ Hcfg → M.step (init code) ∈ Hcfg)
    (hmachine : ∀ code, (∃ k : ℕ, M.step^[k + 1] (init code) ∈ Hcfg) ↔ (code.eval n).Dom) :
    ∃ (Mt : Type) (_ : TopologicalSpace Mt) (_ : CompactSpace Mt) (F : ContinuousFlowOn Mt)
      (enc : (M.Cfg × (ℤ → M.HistRec)) → Mt),
      ∀ code, (∃ t : ℝ, 0 < t ∧ F.φ t (enc (init code, M.blankHist))
          ∈ enc '' {p | p.1 ∈ Hcfg}) ↔ (code.eval n).Dom
```

with its undecidability twin at `/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M20_FlowCapstone.lean:69-80` (`bitTM_bennett_blowup_undecidable (M : BitTM) ...`).

Consequences the audit never priced:

- It is **parametric in an arbitrary `M : BitTM`**, exactly like `reach_at_k`. No `Mtr`, no TM0, no `codeSupp`. Everything the designs said about `Mtr` collapsing halts into `encHalt S` (M27:35-38) is irrelevant here.
- Its target is `enc '' {p | p.1 ∈ Hcfg}` — an **arbitrary set of configurations**, not a state hyperplane. Two disjoint answer regions are the natural shape, and a witnessing divisor left on the tape *is* expressible. The "state-coordinate-only / cannot exhibit a factor" limitation that dominated C2, D2 and all six designs is an artifact of the σ line, not of the repo.
- It delivers `ContinuousFlowOn` with `∃ t : ℝ, 0 < t`, i.e. a **continuous-time** statement. The external analysis's own words are "smooth flow orbit"; every design terminated at `sigmaM`, a discrete self-map, and then wrote an honest-scope paragraph apologising for it. The flow version was sitting there.
- Its two obligations (`hHclosed` = answer set forward-closed; `hmachine` = the machine-level iff) are precisely what every design was going to prove anyway. `hHclosed` is discharged by the absorbing answer words that L5/E5/§3 already budget.

It does still carry `init : Nat.Partrec.Code → M.Cfg` and `(code.eval n).Dom`, so it needs the same index generalization the audit identified for M59 — but the audit told the reader that generalization only unlocks a discrete map. It unlocks the flow too, in a form with strictly more expressive targets. This is a design link that all six candidates waved through by never considering it.

### 2. Eight modules of the continuous-flow / analog line were never read, and two of them change the verdict

Unexamined with no file:line anywhere in the fact sheet, probes or designs: **M38_CouplingObstruction, M39_AnalogTargeting, M40_GatedTargeting, M41_ConcreteWindow, M42_LeapfrogHalfStep, M43_LeapfrogOrbit, M48_SmoothStepAssemble, M51_AutonomousClock, M52_AutonomousLeapfrog, M53_CpuInClock, M60_AnalyticWall, M36_Corollaries**, plus M3_Encoding, M3c_Bennett, M4_Suspension, M9, M18, M19, M21, M22, M24, M35. That is 22 of 65 modules, ~2,400 lines, and it is not a random remainder — **M39→M40→M41→M51→M52→M53 is the entire continuous-flow construction line**, which is the subject of C4 and of the external analysis's `pop_not_contractive` claim.

Two of them matter directly:

**(a) M53 contradicts the framing "the continuous-flow route is blocked."** `/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M53_CpuInClock.lean:175` is `cpuWindow_advances`, and `:72` defines `cpuField (σstep : Cfg3 → Cfg3) (C : ℝ) : Cfg3 × Cfg3 × ℝ → ...` — a **single autonomous C^∞ vector field** (`cpuField_contDiff`, :132) whose flow over one clock window advances a real configuration by one genuine `sigmaRL` machine step, with an explicit `Real.exp (-C)` residual. The continuous-flow route is not blocked from *existing*; it is blocked from being *exact*. M56's `pop_not_contractive` is the wall against exactness, and M53 is the already-shipped honest ε-version. C4 audited M56's scope carefully and never learned that the thing M56 walls off has a working approximate implementation two modules away.

**(b) M38 is the one place where "primality is decidable" would buy something, and the FATAL value verdict missed it.** `/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M38_CouplingObstruction.lean:36` proves `continuous_detector_isClopen`, with the dual at `:61` (`no_continuous_detector_of_not_isClopen`). The module docstring (M38:14-22) states the obstruction's shape exactly: an autonomous coupled ODE needs a *continuous* state-readout `g`; continuous 2-valued detectors only see clopen sets; the halting basin is **Σ₁ but not recursive** (citing M37's `fluid_reach_full_characterization`) hence not clopen; therefore the autonomous coupling is structurally impossible. The whole D4 probe's FATAL verdict rests on "primality is decidable, therefore the bridge has zero content." M38 identifies the one axis on which that is backwards: the repo's own stated blocker for the *autonomous* line is precisely undecidability of the target set. A decidable target is the case where M38's obstruction argument does not run, and the M35 coupled-Riccati + M38-Brick-C line is exactly the direction the owner's docs call paper-blocked *for the halting predicate*. Nobody in six designs, two value critiques and a FATAL verdict noticed that the proposal's supposedly-fatal weakness is the hypothesis M38 needs negated. I am not claiming the prime basin *is* clopen in the relevant Cantor topology — I have not proved that and no one should assert it — but that is the question the audit should have asked and did not.

**(c) M60 supplies a scope statement everyone owed and nobody gave.** `/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M60_AnalyticWall.lean:78` proves `sfloor_not_analytic (k : ℕ) (hk : 2 ≤ k) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) : ¬ AnalyticOnNhd ℝ (sfloor k w) Set.univ`, with the companion `sround_analytic` at `:100`. Since `sigmaM` runs through `sfloor` (M46:75 → M58:90), the repo has a *machine-checked* theorem that this scaffold can never be upgraded past C^∞. Every design's honest-scope section describes σ as "explicit C^∞" and none states the certified impossibility of analytic; that is a free, in-repo, kernel-backed scope line that the anti-overclaim apparatus of all six designs left on the table.

### 3. A mathlib capability nobody checked, and it cheapens the one brick everyone agreed was "the only new mathematics"

Four separate auditors ran the same grep — `Primrec` ∩ `Nat.Prime` — got zero, and concluded the primality-is-computable brick has no mathlib support. That is the wrong query: the question is what *ingredients* exist. In the pinned tree (`/Users/liweiting/Documents/alloy/contact_geometry_lean/.lake/packages/mathlib`, rev 360da6fa…, same pin):

- `Mathlib/Computability/Primrec/List.lean:704` — `theorem sqrt : @Primrec' 1 fun v => v.head.sqrt`
- `Mathlib/Computability/Primrec/List.lean:779-780` — `theorem Primrec.nat_sqrt : Primrec Nat.sqrt := Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt`
- `Mathlib/Computability/Primrec/Basic.lean:710` — `theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ)`

So `Primrec Nat.sqrt` is **already proved**. Three independent rounds of this audit told the reader that `Nat.prime_def_le_sqrt` (Prime/Defs.lean:124) is "a detour that drags in `Nat.le_sqrt`/`Nat.sqrt_lt`" and that `prime_def_lt'` is the only sane route — while the sqrt route is directly available at the Primrec layer and gives an O(√n) bound rather than O(n), which matters for any `runBound`, any `#eval` drill, and any kernel-`decide` certificate. The external analysis's choice of `prime_def_le_sqrt` was scolded four times and was, on this axis, better supported than the correction.

(Settling a disagreement in passing: the two `forall_lt`s are `PrimrecPred.forall_lt` at `Mathlib/Computability/Primrec/List.lean:452` and `PrimrecRel.forall_lt` at `:507`. Design D-minimal cited 452 for the Rel version; 507 is correct.)

### 4. M36 was never read, and it is a cheaper σ-level deliverable than the one every critic recommended

`/Users/liweiting/Documents/alloy/fluid_turing_lean/FluidTuringLean/M36_Corollaries.lean` is 30 lines and contains `fluid_confinement_undecidable (n : ℕ)` at `:21-28`, derived from `fluid_blowup_undecidable` in three tactic lines via `ComputablePred.not`. Four separate graft sections recommended "extract M59's discarded `key` block into a σ-level characterization (N4/L8/B1)" as the best-value alternative — real, but it requires refactoring M59's internals. M36 shows the owner's own cheaper pattern: **`sigmaRL3_confinement_undecidable`, the avoidance complement of M59:211, is a three-line corollary of the existing headline** with no refactor, no `key` extraction, no index generalization. Nobody named it. The σ line is missing both M36's complement and M37's characterization; only the harder of the two was proposed.

### 5. Citation hygiene on the most-quoted lines, where the audit's own standard was strictest

- **The fact sheet was right and a recheck "corrected" it wrongly.** `grep -n` gives `M59_SmoothUndecidable.lean:122: noncomputable def sigmaM` and `:126: theorem sigmaM_contDiff`. The C7 recheck asserted these sit at `:121/:125` and flagged the orchestrator as off-by-one. The orchestrator was right.
- **The single most-cited proof block has three mutually incompatible citations and nobody noticed.** The real layout: `sigmaM_reach_undecidable_of` at `:164`; `have key` opens at `:179`; `rw [key] at hcomp` at `:199`; `exact ComputablePred.halting_problem n hcomp` at `:200`. The audit variously reported the block as `:181-205`, `:179-205`, `:181-207`, with `halting_problem` at `:199`, `:206`, `:207` and `:268` in different sections — including two different numbers inside one claim's own text. Also `offset_exists` is at `:150` (one auditor said `:153`).
- Nobody quoted `sigmaM_contDiff`'s proof, which is the actual evidence for the "zero hypotheses" claim everyone relied on. It is `sigmaRL3_contDiff _ _ _ _ _ _` (M59:127), and `sigmaRL3_contDiff` at `M58_SmoothStep3.lean:166` takes `(δq δw moveN : ℕ → ℕ → ℝ) (Q K : ℕ) (w : ℝ)` with no hypotheses. Confirmed — but it was asserted six times before anyone opened it.

### 6. Where the framing is wrong

The audit evaluated a proposal phrased in terms of a **smooth flow** entirely against the **discrete-map line** (M55–M59), then used properties of that line — state-only targets, one collapsed halt word, noncomputable encoders, "not a flow" — as the grounds for both the honesty verdict and the FATAL value verdict. The repo has a second, older, BitTM-parametric, set-valued-target, genuinely continuous-time route (M20:69 → M37:51 → M33), and a third, autonomous-vector-field route with a working ε-version (M39→M53) and its own certified walls (M38:36, M60:78). None of the three was scored. A bake-off of six designs that all terminate at the same discrete map is not a bake-off; it is one design costed six ways, and the missing modules are exactly the ones that would have produced a different shape.

Secondary framing gap: the external analysis's **two-sided** claim (`n composite ↔ ∃k … ∈ U_composite`) was audited only against the σ line, where it was correctly found unreachable. Against `bitTM_bennett_characterization`'s `Hcfg : Set M.Cfg` target it is the natural shape. The audit reported "the analysis's headline shape is the expensive shape" as a fact about the repo; it is a fact about one of the repo's three bridges.