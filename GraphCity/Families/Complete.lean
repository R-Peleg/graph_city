/-
Copyright (c) 2026 Reuven Peleg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg
-/
import GraphCity.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
Complete graph.
The parameter n is the number of vertices.
Every 2 different vertices are connected.
-/

namespace GraphCity.Families.Complete

abbrev vertexType (n : ℕ) := Fin n
abbrev graph (n : ℕ) : SimpleGraph (vertexType n) :=
  SimpleGraph.completeGraph (Fin n)

/- Number of vertices = `n` -/
@[simp]
theorem card_vertices (n : ℕ) :
    Fintype.card (vertexType n) = n := by
  exact Fintype.card_fin n

theorem card_edges (n : ℕ) :
    (graph n).edgeFinset.card = n.choose 2 := by
  unfold graph
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)]
  simp

theorem chromatic_number (n : ℕ) :
    (graph n).chromaticNumber = n := by
  rw [SimpleGraph.chromaticNumber_top]
  simp

end GraphCity.Families.Complete
