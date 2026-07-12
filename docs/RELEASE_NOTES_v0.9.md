# v0.9 — Two machine-checked undecidability theorems (continuous flow + smooth map)

First archival release of **fluid_turing_lean**: a Lean 4 + mathlib formalization of Turing-completeness and undecidability for dynamical systems. This release captures the project at **63 modules, zero `sorry`, standard-three-axioms only**.

## Headline results (both unconditional, zero-`sorry`)

- **`FluidTuring.fluid_blowup_undecidable`** (`M33`) — a compact-space continuous-time flow whose reachability predicate `fun code ↦ ∃ t>0, F.φ t (base code) ∈ Target` is not computable.
- **`FluidTuring.sigmaRL3_reachability_undecidable`** (`M59`) — an *explicit* `C^∞` map `σ : ℝ³ → ℝ³` whose orbit-reachability predicate `fun code ↦ ∃ k, σ^[k] (base code) ∈ Target` is not computable.

These are different mathematical objects — a continuous **flow** vs. a discrete **map** — sharing one machine layer (`BitTM`/`Mtr` + `Mtr_halts_iff`), both reducing to mathlib's `ComputablePred.halting_problem`. To our knowledge (best-effort search), this is the first machine-verified undecidability result for dynamical systems of this kind.

- **`FluidTuring.pop_not_contractive`** (`M56`) — a certified **negative** result: the continuous-flow robustification of the smooth-map construction is impossible (the read operator is exactly affine with slope `K > 1`; no weighted norm contracts it).

## Verify it yourself

The proofs are mechanically checkable — authorship and institution are irrelevant to verification.

```bash
lake exe cache get     # fetch pinned mathlib build cache
lake build             # builds all 63 modules; success ⇒ every theorem holds
```

Per-declaration axiom hygiene:

```lean
import FluidTuringLean
open FluidTuring
#print axioms fluid_blowup_undecidable            -- [propext, Classical.choice, Quot.sound]
#print axioms sigmaRL3_reachability_undecidable   -- [propext, Classical.choice, Quot.sound]
```

Toolchain: Lean `v4.32.0-rc1` (pinned in `lean-toolchain`) + pinned mathlib.

## Honest scope

The two theorems are real and unconditional; the limitations bound *what we claim*, not what is proved. (A) Realizing the flow as a genuine Euler–Beltrami flow needs contact geometry not yet in mathlib — handled as an explicit hypothesis, not a `sorry`. (B) The continuous-flow robustification is *proved impossible* (`pop_not_contractive`); analytic exact-on-lattice reading is impossible. (C) Toy binary encoding; reachability (not literal blow-up); `C^∞` rather than strict-analytic GPAC. **Not** a claim about real Navier–Stokes or physical fluids. See `README.md` for details.

## Provenance

Developed with substantial LLM assistance (Anthropic's Claude) under a scope → build → adversarial-verify discipline; every theorem is nonetheless a genuine kernel-checked Lean proof. See the README's methodology section.

## Cite

See `CITATION.cff`. A Zenodo DOI is minted from this release. License: MIT.
