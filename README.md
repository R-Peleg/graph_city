# GraphCity

A Lean library for finite graph families, by Reuven Peleg, licensed under
Apache-2.0. The project formalizes standard graph facts; it claims no new
mathematical results.

For every natural number `n`, including zero:

| Family | Property | Lean declaration |
| --- | --- | --- |
| Complete graph on `Fin n` | `n` vertices | `GraphCity.Families.Complete.card_vertices` |
| Complete graph on `Fin n` | `n.choose 2` unordered edges | `GraphCity.Families.Complete.card_edges` |
| Complete graph on `Fin n` | chromatic number `n` | `GraphCity.Families.Complete.chromatic_number` |
| Boolean `n`-cube | `2 ^ n` vertices | `card_vertices` |
| Boolean `n`-cube | degree `n` at every vertex | `degree` |
| Boolean `n`-cube | `n * 2 ^ (n - 1)` unordered edges | `card_edges` |

The hypercube has vertices `Fin n → Bool`; two vertices are adjacent exactly
when they differ in one coordinate. Its degree proof constructs a bijection
between coordinates and neighbors by flipping one Boolean coordinate. Its edge
count follows from Mathlib's degree-sum formula. At dimension zero the cube has
one vertex and no edges; the formula uses natural-number subtraction.

The complete-graph results specialize existing Mathlib counting and coloring
theorems. Mathlib's chromatic number takes values in the extended naturals.
Hypercube declarations retain their original names in the root namespace.

## Build

The project pins Lean 4.35.0 and Mathlib's corresponding release commit in
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build GraphCity Challenge Solution
```

## Palomar submission

`Challenge.lean` is an independent statement of all six claims. It imports only
Mathlib, spells out the graph definitions, and deliberately leaves the six
theorem proofs as `sorry`. `Solution.lean` imports the existing proved GraphCity
modules without importing the Challenge. `comparator.json` selects all six
theorems and permits only Lean's three standard axioms. Deliberate Challenge
holes are excluded from the unresolved-proof counts in `formalization.yaml`.

The metadata records the classical source material, reliance on Mathlib,
authorship, automation disclosure, review status, and scope. The original
repository does not identify a particular source text or document its historical
proof-production process; the metadata makes that uncertainty explicit.
Before submitting, fill in any known historical AI/tool use, source texts, and
human review in `formalization.yaml`.

Before submitting, push the intended snapshot and run **Palomar mechanical
preflight** from GitHub Actions on that exact commit. It runs automatically on
pushes to `codex/palomar-registration` and also supports manual dispatch. The workflow calls the
complete Palomar verifier in `mode: full`, using the standard execution profile
and a pinned pipeline revision. A local build is not a replacement for this run.
Proceed only when its mechanical report says `status: pass`.

After the preflight passes, open the
[Palomar submission form](https://submit.palomar-registry.org/) yourself:

1. Enter repository `R-Peleg/graph_city`, the full pushed SHA from
   `git rev-parse HEAD`, and Comparator configuration `comparator.json`.
2. Leave project and metadata paths at their default root locations.
3. Select the responsible-author/maintainer relationship and sign in to GitHub
   to prove repository write access.
4. Save the private status-page link and wait for verification and editorial
   review. Read the exact review before choosing whether to register.

Registration makes the record and review public and is intended to be permanent.
This repository's preparation files do not themselves register anything.

Follow the [submission instructions](https://palomar-registry.org/how-to-submit)
and [agent protocol](https://submit.palomar-registry.org/llms.txt). If you later
delegate intake to an agent, that route requires a temporary verification tag
and secret gist through authenticated GitHub CLI access. The agent must show
you the exact review before you decide whether to register. Keep submission
bearer tokens private.

Palomar also requires a plausible research audience. These elementary results
may not meet that editorial threshold; preparation and successful mechanical
checks do not establish eligibility or registration.
