# fluid_turing_lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21320838.svg)](https://doi.org/10.5281/zenodo.21320838)

**Machine-checked undecidability of dynamical systems — continuous flows and smooth maps, formalized in Lean 4 + mathlib.**

動力系統圖靈完備性與不可判定性的 Lean 4 形式化（連續流 + 光滑映射兩座封頂）。

> **Status:** 65 modules · **0 `sorry`** · axioms limited to `propext`, `Classical.choice`, `Quot.sound` (the mathlib standard three) · Lean `v4.32.0-rc1` + pinned mathlib.
>
> *(The detailed pre-M33 Euler–Beltrami design log is archived at [`docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md`](docs/README_ARCHIVE_eulerBeltrami_2026-07-08.md).)*

---

## Abstract

That specific dynamical systems can be Turing-complete — and therefore have undecidable long-term behaviour — is a classical line of results **on paper** (Moore 1990–91; Graça / Bournez–Graça–Pouly; Tao's fluid-computer programme; Cardona–Miranda–Peralta-Salas–Presas, *PNAS* 2021). To our knowledge (best-effort search, not an exhaustive survey), no such result had previously been **machine-verified** in any proof assistant.

This repository contributes two machine-checked undecidability theorems, both **unconditional** and **zero-`sorry`**:

1. **Continuous flow.** There is a compact-space continuous-time flow whose reachability predicate is not computable.
2. **Smooth map.** There is an *explicit* `C^∞` map `σ : ℝ³ → ℝ³` whose orbit-reachability predicate is not computable.

These are genuinely different mathematical objects (a continuous **flow** vs. a discrete **map**) that share the same underlying machine layer. We also contribute a **machine-checked negative result**: the naïve continuous-flow robustification of the smooth-map construction is *provably impossible*.

---

## Main results

| Theorem (Lean name) | Statement | Module |
| --- | --- | --- |
| `FluidTuring.fluid_blowup_undecidable` | ∃ a compact-space `ContinuousFlowOn X`, a base-point family and a target set, with `¬ ComputablePred (fun code ↦ ∃ t>0, F.φ t (base code) ∈ Target)`. Unconditional. | `M33` |
| `FluidTuring.sigmaRL3_reachability_undecidable` | ∃ an explicit `σ : ℝ³→ℝ³` with `ContDiff ℝ ⊤ σ`, a base and a target, with `¬ ComputablePred (fun code ↦ ∃ k, σ^[k] (base code) ∈ Target)`. Unconditional. | `M59` |
| `FluidTuring.pop_not_contractive` | On the encoding lattice the read operator is exactly affine with slope `K > 1`; hence no `ρ < K` (a fortiori no contracting `ρ < 1`) bounds it — a certified negative result closing the continuous-robustness route. | `M56` |

Both positive theorems reduce, via a from-scratch reversible machine (`BitTM` / `Mtr`, with the halting bridge `Mtr_halts_iff`) and mathlib's `TM2 → TM1 → TM0` chain, to mathlib's `ComputablePred.halting_problem`.

---

## Reproduce / verify

The central claim is **mechanically checkable**: the proofs either compile with zero `sorry` or they do not. Author, institution and reputation are irrelevant to verification.

```bash
# The Lean 4 toolchain is pinned in `lean-toolchain`; `elan` fetches it.
lake exe cache get     # fetch the pinned mathlib build cache
lake build             # builds all 65 modules; success ⇒ every theorem holds
```

Axiom hygiene (no `sorryAx`, no custom axioms) is re-checkable per declaration:

```lean
import FluidTuringLean
open FluidTuring
#print axioms fluid_blowup_undecidable            -- [propext, Classical.choice, Quot.sound]
#print axioms sigmaRL3_reachability_undecidable   -- [propext, Classical.choice, Quot.sound]
```

`scripts/check.sh <decl…>` automates build + `sorry`-scan + axiom check.

---

## Repository map

- `M1`–`M9` — computability base, reversible Turing machine `BitTM`, Bennett reversibilization (`M3b`–`M3e`), flow suspension, Euler/Reeb interface.
- `M10`–`M33` — **main line** (continuous flow): `BitTM`/`Mtr` machine layer, `Mtr_halts_iff`, universal-code assembly, capstone `fluid_blowup_undecidable`.
- `M34`–`M38` — literal-blowup and reachability-characterization extensions.
- `M39`–`M60` — **GPAC line** (smooth map): smooth primitives (`smoothSelect`, `sfloor`, `sround`), a toy smooth CPU, the infinite-tape bridge (`ListBlank`), the certified G5 wall (`M56`), the smooth-map lift (`M58`), capstone `sigmaRL3_reachability_undecidable` (`M59`), and the analytic-reader wall (`M60`).
- `M61` — additive abstract-NS specification repair: divergence-free and steady momentum are explicit separate obligations; still a vacuous signature layer, not a real NS PDE result.
- Periodic-NS companion status — `contact_geometry_lean` is verified through C271. C260–C262 carry C259's one-sided global-to-all-window image inclusion through faithful algebraic quotients and prove residual naturality. C263–C271 add a complete weighted-`lp 1` coefficient carrier, its closed transverse subspace, absolute continuous-field synthesis and bounded coefficient multipliers, canonical coefficient- and continuous-field-valued LF tests, and an algebraic separated-tensor pointwise formula with an explicit nonzero continuous-field witness. Contact code/receipt commits: `d62ff3085b22448116319f458ab3f929d5c91595` / `8a7dfd55fcd7c3fdec587d562695f63238a21dd5`; 268 modules, 3577 source declarations, 5586 audited declarations, and 268/268 consistency checks pass. The quotient comparison remains one-sided and algebraic; no coefficient-reality condition, LF `CompleteSpace` result, intrinsic divergence-free field identification, density theorem, Leray–Hopf package, or Clay result is proved. C271's explicit nonzero field witness is not proved to lie in the range of its tensor composite.
- `docs/GPAC_ROADMAP.md`, `docs/UNDECIDABILITY_LINE.md` — dated design logs and scope maps.
- `docs/NAVIER_STOKES_FORMALIZATION_ROADMAP.md` — honest separation of the current abstract
  signature/concrete-example layers from the future periodic PDE, energy, Galerkin, Sobolev, and
  regularity programme.

---

## Honest scope (please read before citing)

The two theorems are real, unconditional, and zero-`sorry`. The items below bound **what we claim**, not what is proved. They are three *distinct* kinds:

- **(A) mathlib not yet built.** Realizing the continuous flow as a *genuine* Euler–Beltrami flow on a real Riemannian 3-manifold needs contact geometry / Reeb-field machinery mathlib does not yet formalize. We do not fake it: the geometry-dependent step is an *explicit hypothesis* (`ReebBeltramiRealization`), leaving the theorem zero-`sorry`; the abstract-signature realization is provably vacuous (`reebBeltramiRealization_trivial`). This is Cardona et al. 2021's paper content, not formalized here.
- **(B) genuine mathematical walls.** The continuous-flow robustification of the smooth map is *proved impossible* (`pop_not_contractive`, `M56`); exact-on-lattice reading is impossible for *analytic* functions. No mathlib addition changes these.
- **(C) our own scope choices.** Toy binary encoding; the *reachability* version (not literal finite-time blow-up — the literal Riccati blow-up in `M11`–`M13` is one-directional and not wired into the main chain); `C^∞` rather than strict-analytic GPAC.

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
