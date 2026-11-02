/-
Copyright (c) 2026 Reuven Peleg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Complete graphs and Boolean hypercubes

For every natural number `n`, the complete graph on `Fin n` has `n` vertices,
`n.choose 2` edges and chromatic number `n`. The Boolean `n`-cube has functions
`Fin n → Bool` as vertices, with adjacency meaning that exactly one coordinate
differs. It has `2 ^ n` vertices, degree `n` at every vertex, and
`n * 2 ^ (n - 1)` edges. The formula includes `n = 0`, where the cube has one
vertex and no edges; subtraction is natural-number subtraction.

These are standard finite graph facts, with no claim of new mathematics.
The definitions below fix their usual meanings explicitly. Only the six theorem
proofs are deliberate holes; `Solution` supplies the existing GraphCity proofs.
The Challenge imports only Mathlib and does not import the proof development.
-/

@[expose] public section

namespace GraphCity.Families.Complete

/-- The vertices of the complete graph on `n` vertices. -/
abbrev vertexType (n : ℕ) := Fin n

/-- The complete simple graph: two vertices are adjacent exactly when distinct. -/
abbrev graph (n : ℕ) : SimpleGraph (vertexType n) :=
  SimpleGraph.completeGraph (Fin n)

/-- The complete graph on `Fin n` has exactly `n` vertices. -/
@[simp] theorem card_vertices (n : ℕ) :
    Fintype.card (vertexType n) = n := by sorry

/-- The complete graph has one edge for each unordered pair of vertices. -/
theorem card_edges (n : ℕ) :
    (graph n).edgeFinset.card = n.choose 2 := by sorry

/-- Every vertex in a complete graph requires its own color (also for `n = 0`). -/
theorem chromatic_number (n : ℕ) :
    (graph n).chromaticNumber = n := by sorry

end GraphCity.Families.Complete

/-- Vertices of the Boolean `n`-dimensional hypercube. -/
abbrev vertexType (n : ℕ) := (Fin n → Bool)

/-- The Boolean hypercube, with edges between vertices differing in one coordinate. -/
abbrev graph (n : ℕ) : SimpleGraph (vertexType n) where
  Adj u v := ∃! i, u i ≠ v i
  symm := by
    constructor
    intro u v h
    obtain ⟨i, hi, unique⟩ := h
    exact ⟨i, Ne.symm hi, fun j hj ↦ unique j (Ne.symm hj)⟩
  loopless := by
    constructor
    intro u h
    obtain ⟨i, hi, _⟩ := h
    exact hi rfl

noncomputable instance (n : ℕ) : DecidableRel (graph n).Adj :=
  fun _ _ ↦ Classical.propDecidable _

/-- The Boolean `n`-cube has `2 ^ n` vertices. -/
@[simp] theorem card_vertices (n : ℕ) :
    Fintype.card (vertexType n) = 2 ^ n := by sorry

/-- Each vertex has exactly one neighbor for each coordinate. -/
theorem degree (n : ℕ) :
    ∀ v, (graph n).degree v = n := by sorry

/-- The Boolean `n`-cube has `n * 2 ^ (n - 1)` edges, including the zero case. -/
theorem card_edges (n : ℕ) :
    (graph n).edgeFinset.card = n * (2 ^ (n - 1)) := by sorry
