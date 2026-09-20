# fluid_turing_lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21320838.svg)](https://doi.org/10.5281/zenodo.21320838)

**Machine-checked undecidability of dynamical systems — continuous flows and smooth maps, formalized in Lean 4 + mathlib.**

動力系統圖靈完備性與不可判定性的 Lean 4 形式化（連續流 + 光滑映射兩座封頂）。

> **Status:** 69 modules · **0 `sorry`** · axioms limited to `propext`, `Classical.choice`, `Quot.sound` (the mathlib standard three) · Lean `v4.32.0-rc1` + pinned mathlib.
>
> *(The detailed pre-M33 Euler–Beltrami design log is archived at [`docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md`](docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md).)*

---

## Abstract

That specific dynamical systems can be Turing-complete — and therefore have undecidable long-term behaviour — is a classical line of results **on paper** (Moore 1990–91; Graça / Bournez–Graça–Pouly; Tao's fluid-computer programme; Cardona–Miranda–Peralta-Salas–Presas, *PNAS* 2021). To our knowledge (best-effort search, not an exhaustive survey), no such result had previously been **machine-verified** in any proof assistant.

This repository contributes two machine-checked undecidability theorems, both **unconditional** and **zero-`sorry`**:

1. **Continuous flow.** There is a compact-space continuous-time flow whose reachability predicate is not computable.
2. **Smooth map.** There is an *explicit* `C^∞` map `σ : ℝ³ → ℝ³` whose orbit-reachability predicate is not computable.

These are genuinely different mathematical objects (a continuous **flow** vs. a discrete **map**) that share the same underlying machine layer. On both lines the result is in fact sharpened from "not computable" to an exact **characterization**: the reachability predicate is proved many-one equivalent to the halting problem, hence located precisely in Σ₁ \ Δ₁ (`M37` for the flow, `M59`/`M63` for the map). Alongside them, `M34` contributes an unconditional zero-`sorry` theorem about *literal* finite-time blow-up, at the weaker **reduction level** (see "Honest scope" (C)). We also contribute a **machine-checked negative result**: the naïve continuous-flow robustification of the smooth-map construction is *provably impossible*.

---

## Main results

| Theorem (Lean name) | Statement | Module |
| --- | --- | --- |
| `FluidTuring.fluid_blowup_undecidable` | ∃ a compact-space `ContinuousFlowOn X`, a base-point family and a target set, with `¬ ComputablePred (fun code ↦ ∃ t>0, F.φ t (base code) ∈ Target)`. Unconditional. | `M33` |
| `FluidTuring.sigmaRL3_reachability_undecidable` | ∃ an explicit `σ : ℝ³→ℝ³` with `ContDiff ℝ ⊤ σ`, a base and a target, with `¬ ComputablePred (fun code ↦ ∃ k, σ^[k] (base code) ∈ Target)`. Unconditional. | `M59` |
| `FluidTuring.sigmaRL3_reach_full_characterization` | The *same* explicit `σ : ℝ³→ℝ³` carries a four-in-one placement: orbit reachability is (1) many-one equivalent to the halting problem — `∀ code, (∃ k, σ^[k] (base code) ∈ Target) ↔ (code.eval n).Dom` — hence (2) not computable, (3) `REPred`, and (4) has non-computable complement. So it sits **exactly in Σ₁ \ Δ₁**, at the same level as the halting problem. Strictly stronger than `sigmaRL3_reachability_undecidable`; both are now derived from the single iff `sigmaRL3_reach_characterization` (`M59`), which is where the universal-code assembly lives. σ-line mirror of `M37`'s `fluid_reach_full_characterization`. Unconditional. | `M59`, `M63` |
| `FluidTuring.pop_not_contractive` | On the encoding lattice the read operator is exactly affine with slope `K > 1`; hence no `ρ < K` (a fortiori no contracting `ρ < 1`) bounds it — a certified negative result closing the continuous-robustness route. | `M56` |
| `FluidTuring.literal_blowup_undecidable` | ∃ a real-valued trajectory family whose **literal** finite-time blow-up (`Tendsto … atTop`, from `M13`'s genuine `C^∞` Riccati escape) is not computable, via the two-way `blowupFamily_blowsUp_iff`. Unconditional — but **reduction-level**: the family is assembled by case-splitting on the halting predicate, so unlike `M33`/`M59` the dynamical object is not a single code-independent system. | `M34` |

The two headline theorems reduce, via a from-scratch reversible machine (`BitTM` / `Mtr`, with the halting bridge `Mtr_halts_iff`) and mathlib's `TM2 → TM1 → TM0` chain, to mathlib's `ComputablePred.halting_problem`.

---

## Reproduce / verify

The central claim is **mechanically checkable**: the proofs either compile with zero `sorry` or they do not. Author, institution and reputation are irrelevant to verification.

```bash
# The Lean 4 toolchain is pinned in `lean-toolchain`; `elan` fetches it.
lake exe cache get     # fetch the pinned mathlib build cache
lake build             # builds all 69 modules; success ⇒ every theorem holds
```

Axiom hygiene (no `sorryAx`, no custom axioms) is re-checkable per declaration:

```lean
import FluidTuringLean
open FluidTuring
#print axioms fluid_blowup_undecidable            -- [propext, Classical.choice, Quot.sound]
#print axioms sigmaRL3_reachability_undecidable   -- [propext, Classical.choice, Quot.sound]
#print axioms sigmaRL3_reach_full_characterization -- [propext, Classical.choice, Quot.sound]
```

`scripts/check.sh <decl…>` automates build + `sorry`-scan + axiom check.

---

## Repository map

- `M1`–`M9` — computability base, reversible Turing machine `BitTM`, Bennett reversibilization (`M3b`–`M3e`), flow suspension, Euler/Reeb interface.
- `M10`–`M33` — **main line** (continuous flow): `BitTM`/`Mtr` machine layer, `Mtr_halts_iff`, universal-code assembly, capstone `fluid_blowup_undecidable`.
- `M34`–`M38` — literal-blowup and reachability-characterization extensions: `literal_blowup_undecidable` (`M34`, reduction-level); the coupled Riccati atom (`M35`); the four-in-one reachability characterization placing the flow exactly in Σ₁ \ Δ₁ (`M37`, `fluid_reach_full_characterization`); the clean half of the continuous-detector obstruction (`M38`, `continuous_detector_isClopen` — the other half, "the halting basin is not clopen", is *not* formalized).
- `M39`–`M60` — **GPAC line** (smooth map): smooth primitives (`smoothSelect`, `sfloor`, `sround`), a toy smooth CPU, the infinite-tape bridge (`ListBlank`), the certified G5 wall (`M56`), the smooth-map lift (`M58`), capstone `sigmaRL3_reachability_undecidable` (`M59`), and the analytic-reader wall (`M60`).
- `M62`–`M63` — σ-line drill and corollaries. `M62` rewrites the machine↔orbit bridge at the `Tape` level (`reach_at_k_tape`, whose right-hand side lands in `Fin m → Bool` and is therefore `Decidable`) and runs the repository's **first fire drill**: a concrete machine whose state tracks the tape is actually evaluated by kernel `decide`, with *negative* controls as well as positive ones, and no `native_decide` (which would add `Lean.ofReduceBool` and break the three-axiom claim above). `M63` adds the confinement corollary (`sigmaRL3_confinement_undecidable`, the σ-line counterpart of `M36`) and the four-in-one Σ₁ \ Δ₁ placement. The structural gate both rest on is `sigmaM_reach_iff_of` (`M59`): σ-orbit reachability ⟺ TM0 halting, stated for a *single* configuration, so no index type is baked in.
- `M64` — a **general gate** and its prime instance. `rePred_computer_uniform` / `sigma_reach_of_rePred`: for *any* semi-decidable predicate `p : ℕ → Prop`, one fixed `BitTM` (one start word, one halting word, input `n` written only on the tape) — equivalently one fixed `C^∞` map with one fixed target — reaches the target from `base n` iff `p n`. The rule this makes explicit: feeding a decidable `p` yields zero computability content, feeding an undecidable `p` yields the M59-type results; `sigma_reach_halting_of_gate` re-derives the shape of the M59 capstone from the gate in one line. The "prime computer" (`prime_computer_uniform`, `primeSigma_reach_iff`) is the gate at `p := Nat.Prime`, built at the owner's request after an audit recommended against it (`docs/PRIME_COMPUTER_AUDIT_2026-09-20.md`): a characterization of a decidable predicate, one-sided, not executable — see the module's honest-scope block. By-product: `primrecPred_nat_prime : PrimrecPred Nat.Prime`, which mathlib lacks.
- `M65` — the gate's first non-trivial instance: **Collatz**. `CollatzReaches n := ∃ k, collatzStep^[k] n = 1` is shown r.e. (`rePred_collatzReaches`, via `Primrec.nat_iterate` + `Partrec.rfind`), fed through the gate, and packaged as named constants: `collatzSigma_reach_iff : (∃ k, collatzSigma^[k] (collatzBase n) ∈ collatzTarget) ↔ CollatzReaches n`, hence `collatzConjecture_iff_reach`: the Collatz conjecture holds iff every positive start reaches the fixed target. This is a *reformulation* of the conjecture inside a dynamical system, not progress on it; unlike `Nat.Prime`, whether `CollatzReaches` is decidable is open, so here orbit reachability is the best known shape rather than a detour.
- `M61` — additive abstract-NS specification repair: divergence-free and steady momentum are explicit separate obligations; still a vacuous signature layer, not a real NS PDE result.
- Periodic-NS companion status — `contact_geometry_lean` is verified through C283. C260–C271 provide the one-sided quotient/residual bridge and weighted-`lp 1` transverse coefficient-to-continuous-field LF route. C272–C283 add a real-linear conjugate-reflection reality carrier, its closed real-transverse intersection, reality-preserving coefficient-symbol syntheses, a native-real coordinate-field bridge, real LF transport, and one explicit nonzero zero-mode witness in that transport range. Contact code/receipt commits: `9b08bef28a6849ae53e2381e3ab45001a00f281b` / `ff7030b9169114dfa928c8ef5f84d8c14ce9e479`; 280 modules, 3796 source declarations, 5943 audited declarations, and 280/280 consistency checks pass. The quotient comparison remains one-sided and algebraic; the coordinate symbols and diagonal cancellation are not identified with intrinsic derivative/Laplacian/divergence, and no LF `CompleteSpace`, physical-test density, Leray–Hopf, regularity, or Clay result is proved. C271's witness remains outside any proved tensor-composite range statement; C283 concerns a different transport map and proves only one displayed range member.
- `docs/GPAC_ROADMAP.md`, `docs/UNDECIDABILITY_LINE.md` — dated design logs and scope maps.
- `docs/NAVIER_STOKES_FORMALIZATION_ROADMAP.md` — honest separation of the current abstract
  signature/concrete-example layers from the future periodic PDE, energy, Galerkin, Sobolev, and
  regularity programme.

---

## Honest scope (please read before citing)

The two headline theorems are real, unconditional, and zero-`sorry`. The items below bound **what we claim**, not what is proved. They are three *distinct* kinds:

- **(A) mathlib not yet built.** Realizing the continuous flow as a *genuine* Euler–Beltrami flow on a real Riemannian 3-manifold needs contact geometry / Reeb-field machinery mathlib does not yet formalize. We do not fake it: the geometry-dependent step is an *explicit hypothesis* (`ReebBeltramiRealization`), leaving the theorem zero-`sorry`; the abstract-signature realization is provably vacuous (`reebBeltramiRealization_trivial`). This is Cardona et al. 2021's paper content, not formalized here.
- **(B) genuine mathematical walls.** The continuous-flow robustification of the smooth map is *proved impossible* (`pop_not_contractive`, `M56`); exact-on-lattice reading is impossible for *analytic* functions. No mathlib addition changes these.
- **(C) our own scope choices.** Toy binary encoding; the two headline theorems are the *reachability* version, not literal finite-time blow-up (a compact space admits no literal blow-up at all, and the `M11`–`M13` Riccati bridge is one-directional and is not wired into the main chain); `C^∞` rather than strict-analytic GPAC.

  *Easy to mistake for a further limitation, so stated explicitly:* `M34` **does** prove an unconditional, zero-`sorry` result about **literal** finite-time blow-up — `literal_blowup_undecidable`, built on the two-way `blowupFamily_blowsUp_iff` over `M13`'s genuine `C^∞` Riccati escape. Its scope caveat is a different one: it is **reduction-level**. `blowupFamily` is assembled by case-splitting on the (undecidable) halting predicate, so the trajectory is selected by the answer rather than computing it; in `M33`/`M59` the flow and the map are single objects fixed independently of `code`, which `M34` is not. Welding literal blow-up into *one autonomous coupled vector field* remains blocked — see the continuity/clopen obstruction in `M38`.

These results are **not** claims about real Navier–Stokes or physical fluids.

---

## Related work

The mathematical ideas descend from a well-known lineage: C. Moore (generalized shifts / undecidable dynamics, 1990–91); M. Branicky (error-correcting analog TM simulation, 1995 — the source of the `sround` primitive); D. Graça, O. Bournez, A. Pouly (robust polynomial-ODE simulation of TMs); T. Tao (the fluid-computer route to Navier–Stokes blow-up); R. Cardona, E. Miranda, D. Peralta-Salas, F. Presas (Turing-complete Euler flows, *PNAS* 118(19), 2021). mathlib provides the discrete substrate (`Turing.TM0/1/2`, Carneiro's computability, `ComputablePred.halting_problem`). The contribution here is the **mechanization** of the dynamical-systems side.

---

## Methodology & AI-assistance disclosure

This project was developed with substantial assistance from a large language model (Anthropic's Claude), driving a disciplined loop: **scope** (parallel agents empirically test achievability in Lean and return achievable / multi-round / wall verdicts) → **build** (each sub-lemma checked via the Lean LSP) → **adversarial verify** (independent skeptic agents attack each module along *soundness*, *vacuity*, and *overclaim*; a module is accepted only after passing). Hard invariants held throughout: zero `sorry`; only the standard three axioms; `C^∞ ≠ analytic` kept distinct; toy machines never claimed universal; every module carries an explicit honest-scope section. Every theorem is a genuine Lean proof, kernel-checked independently of how it was produced.

---

## How to cite

Please cite the archived release (see `CITATION.cff`):

```
Li, Wei-Ting. fluid_turing_lean: Machine-checked undecidability of dynamical systems in Lean 4.
Zenodo, 2026. DOI: 10.5281/zenodo.21320838
```

BibTeX:

```bibtex
@software{li_fluid_turing_lean_2026,
  author    = {Li, Wei-Ting},
  title     = {{fluid\_turing\_lean}: Machine-checked undecidability of dynamical systems in Lean 4},
  year      = {2026},
  publisher = {Zenodo},
  version   = {v0.9},
  doi       = {10.5281/zenodo.21320838},
  url       = {https://doi.org/10.5281/zenodo.21320838}
}
```

---

## License

This project is released under the MIT License; see [`LICENSE`](LICENSE).
