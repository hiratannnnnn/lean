import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# SimpleGraph tutorial

This file is meant to be read top-to-bottom in VS Code with the Lean infoview.
It uses `SimpleGraph` from mathlib, rather than defining graph theory from
scratch.

The main idea is:

* vertices are a type `V`;
* a graph is a symmetric, loopless adjacency relation `G.Adj`;
* familiar graph notions such as neighbor sets, walks, and degrees are already
  available in mathlib.
-/

namespace Tutorial

/-!
## 1. A tiny vertex type

For experiments, finite vertex types are convenient.  Here `V` has exactly
three vertices: `a`, `b`, and `c`.
-/

inductive V
  | a
  | b
  | c
  deriving DecidableEq, Repr

open V

instance : Fintype V where
  elems := {a, b, c}
  complete := by
    intro x
    cases x <;> simp

/-!
## 2. The path graph a -- b -- c

`SimpleGraph V` is built from an adjacency relation.  We provide:

* `Adj`, the intended relation;
* `symm`, proof that adjacency is symmetric;
* `loopless`, proof that no vertex is adjacent to itself.
-/

def path3Adj : V → V → Prop
  | a, b => True
  | b, a => True
  | b, c => True
  | c, b => True
  | _, _ => False

instance : DecidableRel path3Adj := by
  intro x y
  cases x <;> cases y <;> unfold path3Adj <;> infer_instance

def path3 : SimpleGraph V where
  Adj := path3Adj
  symm := by
    intro x y h
    cases x <;> cases y <;> simp [path3Adj] at h ⊢
  loopless := by
    refine ⟨?_⟩
    intro x h
    cases x <;> simp [path3Adj] at h

instance : DecidableRel path3.Adj := by
  intro x y
  change Decidable (path3Adj x y)
  infer_instance

instance (v : V) : Fintype (path3.neighborSet v) :=
  inferInstance

/-!
These are small sanity checks.  `decide` works because this is a finite,
explicit graph.
-/

example : path3.Adj a b := by
  decide

example : path3.Adj b a := by
  decide

example : ¬ path3.Adj a c := by
  decide

example (v : V) : ¬ path3.Adj v v := by
  change ¬ path3Adj v v
  cases v <;> simp [path3Adj]

/-!
## 3. Neighbor sets

`G.neighborSet v` is the set of vertices adjacent to `v`.
-/

example : b ∈ path3.neighborSet a := by
  decide

example : c ∈ path3.neighborSet b := by
  decide

example : c ∉ path3.neighborSet a := by
  decide

/-!
## 4. Complete and empty graphs

mathlib already provides standard graphs.  `completeGraph V` has every
non-loop edge; `emptyGraph V` has no edges.
-/

example : (SimpleGraph.completeGraph V).Adj a b := by
  simp

example : ¬ (SimpleGraph.completeGraph V).Adj a a := by
  simp

example : ¬ (SimpleGraph.emptyGraph V).Adj a b := by
  simp

/-!
## 5. Walks

If we have an edge, mathlib can turn it into a walk of length one.
-/

def abWalk : path3.Walk a b :=
  (show path3.Adj a b by decide).toWalk

example : abWalk.length = 1 := by
  rfl

/-!
Longer walks can be built with `Walk.cons`.
-/

def acWalk : path3.Walk a c :=
  SimpleGraph.Walk.cons
    (show path3.Adj a b by decide)
    ((show path3.Adj b c by decide).toWalk)

example : acWalk.length = 2 := by
  rfl

/-!
## 6. Degrees

For finite graphs, `G.degree v` is the number of neighbors of `v`.
-/

example : path3.degree a = 1 := by
  decide

example : path3.degree b = 2 := by
  decide

example : path3.degree c = 1 := by
  decide

/-!
## 7. A reusable theorem shape

When formalizing your own graph theory, a good first step is often to state
the result over an arbitrary vertex type and an arbitrary `SimpleGraph`.
-/

theorem adjacent_vertices_are_distinct {α : Type} (G : SimpleGraph α) {u v : α}
    (h : G.Adj u v) : u ≠ v := by
  exact h.ne

example : a ≠ b := by
  exact adjacent_vertices_are_distinct path3 (show path3.Adj a b by decide)

end Tutorial
