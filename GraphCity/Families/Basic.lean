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

end GraphCity
