import Mathlib.Combinatorics.SimpleGraph.Basic

namespace GraphCity

universe u

structure GraphFamily where

  /- The parameter for this graph family -/
  Param : Type u

  /- The vertex set, depending on the param value -/
  Vertex : Param → Type u

  /- The graph itself, depening on the param value -/
  graph : (p : Param) → SimpleGraph (Vertex p)

  /- Property: the vertex set is always finite -/
  vertexFintype : (p : Param) → Fintype (Vertex p)

namespace GraphFamily

/-- The number of vertices of an instance of a finite graph family. -/
def vertexCard (F : GraphFamily) (p : F.Param) : ℕ :=
  @Fintype.card (F.Vertex p) (F.vertexFintype p)

end GraphFamily

end GraphCity
