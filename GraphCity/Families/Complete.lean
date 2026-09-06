/-
Copyright (c) 2026 Reuven Peleg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg
-/
import GraphCity.Basic
import Mathlib.Data.Fintype.Card

/-!
Complete graph.
The parameter n is the number of vertices.
Every 2 differenct vertices are connected.
-/

namespace GraphCity
namespace Families.Complete

def family : GraphFamily where
  Param := ℕ
  Vertex n := Fin n
  graph n := SimpleGraph.completeGraph (Fin n)
  vertexFintype := inferInstance

@[simp]
theorem card_vertices (n : ℕ) :
    family.vertexCard n = n := by
  exact Fintype.card_fin n

end Families.Complete
end GraphCity
