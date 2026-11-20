/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Hello.Graph

@[expose] public section

namespace Hello.Graph.Examples

def g₁ : Graph String String := [
  ("penguin", "is-a", "bird"),
  ("bird", "is-a", "animal"),
  ("toucan", "is-a", "bird"),
]

example : g₁.hasLabel "is-a" = true := rfl
example : g₁.hasNode "toucan" = true := rfl
example : g₁.hasTarget "pending" = false := rfl
example : g₁.hasTarget "animal" = true := rfl
example : g₁.hasEdge ("bird", "is-a", "animal") = true := rfl
example : g₁.Irrefl := by decide

/-- The path penguin → bird → animal. -/
def p₁ : Graph.Path g₁ "penguin" "animal" :=
  .cons ("penguin", "is-a", "bird") (by decide)
    (.sing ("bird", "is-a", "animal"))

/-- The single-edge path toucan → bird. -/
def p₂ : g₁.Path "toucan" "bird" :=
  .sing ("toucan", "is-a", "bird")

example : p₁.length = 2 := rfl
example : p₁.labels = ["is-a", "is-a"] := rfl
example : (p₂.append (.sing ("bird", "is-a", "animal"))).length = 2 := rfl
example : p₁.toList =
    [("penguin", "is-a", "bird"), ("bird", "is-a", "animal")] := rfl

example : g₁.Reachable "toucan" "animal" :=
  ⟨p₂.append (.sing ("bird", "is-a", "animal"))⟩

example : g₁.Reachable "penguin" "animal" := ⟨p₁⟩

example : g₁.Reachable "penguin" "animal" := by decide
example : g₁.Reachable "toucan" "bird" := by decide
example : ¬ g₁.Reachable "animal" "penguin" := by decide
example : ¬ g₁.Reachable "bird" "bird" := by decide

example : g₁.Acyclic := by decide

def g₂ : Graph String Nat := [
  ("a", 0, "b"), ("b", 1, "c"), ("c", 2, "d"), ("c", 3, "a")
]

/-- g₂ has a cycle! -/
example : ¬ g₂.Acyclic := by decide

end Hello.Graph.Examples
