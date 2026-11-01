/-
Copyright (c) 2026 Reuven Peleg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring

/--
The Hypercube: vertices are {0, 1} ^ n, edges connects u and v iff
there is exactly one index in which they are different
-/
/-
Vertex type: boolean flags over 0...n
-/
abbrev vertexType (n : ℕ) := (Fin n → Bool)
abbrev graph (n : ℕ) : SimpleGraph (vertexType n) where
  Adj u v := ∃! i, u i ≠ v i
  symm := by
    constructor
    · intro u v hi
      grind
  loopless := by
    constructor
    · intro u
      simp

-- Provide decidability for the adjacency relation
noncomputable instance (n : ℕ) : DecidableRel (graph n).Adj :=
  fun _ _ ↦ Classical.propDecidable _

/- Number of vertices = `2^n` -/
@[simp]
theorem card_vertices (n : ℕ) :
    Fintype.card (vertexType n) = 2 ^ n := by
  simp

/- helper: flip one index -/
def flip_vertex (n : ℕ) (v : vertexType n) (i : Fin n) :
    vertexType n := Function.update v i (!v i)

lemma flip_vertx_adj (n : ℕ) (v : vertexType n) (i : Fin n) :
    (graph n).Adj v (flip_vertex n v i) := by
  dsimp [graph]
  refine ⟨i, ?_, ?_⟩
  · unfold flip_vertex
    dsimp only
    rw [Function.update_self]
    rw [Bool.eq_not_self]
    rw [not_false_eq_true]
    trivial
  · unfold flip_vertex
    intro y
    contrapose!
    intro hy
    exact (Function.update_of_ne hy (!v i) v).symm

def flip_neighbor (n : ℕ) (v : vertexType n) :
    Fin n → (graph n).neighborSet v :=
  fun i => ⟨flip_vertex n v i, flip_vertx_adj n v i⟩

lemma flip_vertex_injective (n : ℕ) (v : vertexType n) :
    Function.Injective (flip_vertex n v) := by
  intro i j
  contrapose!
  intro h
  dsimp only [flip_vertex]
  rw [Function.ne_iff]
  use i
  rw [Function.update_self]
  rw [Function.update_of_ne h]
  rw [ne_eq, Bool.not_eq_eq_eq_not, Bool.eq_not_self, not_false_eq_true]
  trivial

lemma flip_neighbor_injective (n : ℕ) (v : vertexType n) :
    Function.Injective (flip_neighbor n v) := by
  intro i j h
  have h' := congrArg Subtype.val h
  exact flip_vertex_injective n v h'

lemma flip_neighbor_surjective (n : ℕ) (v : vertexType n) :
    Function.Surjective (flip_neighbor n v) := by
  intro w
  obtain ⟨i, hi, h_unique⟩ := w.property
  dsimp only at h_unique
  use i
  apply Subtype.ext
  dsimp only [flip_neighbor]
  dsimp only [flip_vertex]
  funext j
  by_cases heq: j = i
  · subst j
    rw [Function.update_self]
    rw [Bool.not_eq_eq_eq_not]
    rw [Bool.eq_not]
    exact hi
  · rw [Function.update_of_ne heq]
    have h2 := h_unique j
    have h3 := mt h2 heq
    exact not_ne_iff.mp h3

noncomputable def hypercube_neighbor_equiv (n : ℕ) (v : vertexType n) :
    Fin n ≃ (graph n).neighborSet v :=
  Equiv.ofBijective (flip_neighbor n v)
    ⟨flip_neighbor_injective n v, flip_neighbor_surjective n v⟩

theorem degree (n : ℕ) :
    ∀ v, (graph n).degree v = n := by
  intro v
  have hcard := Fintype.card_congr (hypercube_neighbor_equiv n v)
  simp only [Fintype.card_fin] at hcard
  simp only [SimpleGraph.card_neighborSet_eq_degree (graph n) v] at hcard
  exact hcard.symm

theorem card_edges (n : ℕ) :
    (graph n).edgeFinset.card = n * (2 ^ (n - 1)) := by
  have h1 := (SimpleGraph.sum_degrees_eq_twice_card_edges (graph n)).symm
  simp only [degree] at h1
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  rw [Finset.card_univ] at h1
  simp only [card_vertices] at h1
  cases n with
  | zero =>
    simp_all
  | succ k =>
    simp only [Nat.add_sub_cancel_right]
    rw [pow_succ] at h1
    have h2 := by
      calc
        2 * (graph (k + 1)).edgeFinset.card =
          (2 ^ k * 2) * (k + 1) := h1
        _ = 2 * ((k + 1) * 2 ^ k) := by ring
    omega
