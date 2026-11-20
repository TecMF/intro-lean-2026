/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Std

/- Graphs -/

@[expose] public section

set_option autoImplicit false
open Std

namespace Hello.Graph

universe u v

/-! ## Edge -/

/-- An edge is a triple: (source node, edge label, target node). -/
abbrev Edge (α : Type u) (β : Type v)
    [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :=
  α × β × α

namespace Edge

variable {α : Type u} {β : Type v} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]

/-- Gets the source node of edge. -/
def source (e : Edge α β) : α :=
  e.1

/-- Gets the label of edge. -/
def label (e : Edge α β) : β :=
  e.2.1

/-- Gets the target node of edge. -/
def target (e : Edge α β) : α :=
  e.2.2

/-- Tests whether `a` is the source node of edge. -/
def hasSource (e : Edge α β) (a : α) : Bool :=
  e.source == a

/-- Tests whether `b` is the label of edge. -/
def hasLabel (e : Edge α β) (b : β) : Bool :=
  e.label == b

/-- Tests whether `a` is the target node of edge. -/
def hasTarget (e : Edge α β) (a : α) : Bool :=
  e.target == a

end Edge

/-! ## Graph -/

/- A graph is a list of edges. -/
abbrev Graph (α : Type u) (β : Type v)
    [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :=
  List (Edge α β)

namespace Graph

variable {α : Type u} {β : Type v} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]

/-- Tests whether `a` is the source node of some edge in graph. -/
def hasSource (g : Graph α β) (a : α) : Bool :=
  g.any (fun e ↦ e.hasSource a)

/-- Tests whether `b` is the label of some edge in graph. -/
def hasLabel (g : Graph α β) (b : β) : Bool :=
  g.any (fun e ↦ e.hasLabel b)

/-- Tests whether `a` is a target node of some edge in graph. -/
def hasTarget (g : Graph α β) (a : α) : Bool :=
  g.any (fun e ↦ e.hasTarget a)

/-- Tests whether `a` is the source or target node of some edge in graph. -/
def hasNode (g : Graph α β) (a : α) : Bool :=
  g.hasSource a || g.hasTarget a

/-- Tests whether edge occurs in graph. -/
def hasEdge (g : Graph α β) (e : Edge α β) : Bool :=
  g.contains e

/- Specs for the above functions. -/

theorem hasSource_iff (g : Graph α β) (a : α) :
    g.hasSource a ↔ ∃ e ∈ g, e.source = a := by
  simp [hasSource, Edge.hasSource]

theorem hasLabel_iff (g : Graph α β) (b : β) :
    g.hasLabel b ↔ ∃ e ∈ g, e.label = b := by
  simp [hasLabel, Edge.hasLabel]

theorem hasTarget_iff (g : Graph α β) (a : α) :
    g.hasTarget a ↔ ∃ e ∈ g, e.target = a := by
  simp [hasTarget, Edge.hasTarget]

theorem hasNode_iff (g : Graph α β) (a : α) :
    g.hasNode a ↔ ∃ e ∈ g, e.source = a ∨ e.target = a := by
  rw [hasNode, Bool.or_eq_true]
  constructor
  · rintro (hs | ht)
    · rcases (hasSource_iff _ _).mp hs with ⟨e, he, hes⟩
      exact ⟨e, ⟨he, .inl hes⟩⟩
    · rcases (hasTarget_iff _ _).mp ht with ⟨e, he, hes⟩
      exact ⟨e, ⟨he, .inr hes⟩⟩
  · rintro ⟨e, he, (hs | ht)⟩
    · left; rw [hasSource_iff]; exact ⟨e, ⟨he, hs⟩⟩
    · right; rw [hasTarget_iff]; exact ⟨e, ⟨he, ht⟩⟩

theorem hasEdge_iff (g : Graph α β) (e : Edge α β) :
    g.hasEdge e ↔ e ∈ g := by
  simp [hasEdge]

/-! ## Irreflexivity -/

/-- A graph is irreflexive if there are no self-loops. -/
def Irrefl (g : Graph α β) : Prop :=
  ∀ e ∈ g, e.source ≠ e.target

/-- Algorithm for checking whether a graph is irreflexive. -/
def irrefl (g : Graph α β) : Bool :=
  g.all (fun e ↦ e.source != e.target)

/-- `irrefl` decides `Irrefl`. -/
theorem irrefl_iff (g : Graph α β) : g.irrefl ↔ g.Irrefl := by
  simp [irrefl, Irrefl, List.all_eq_true]

/-- `Irrefl` is decidable. -/
instance (g : Graph α β) : Decidable (Irrefl g) :=
  decidable_of_iff _ (irrefl_iff _)

/-! ## Path -/

/--
`Path g a a'` is a path in `g` from node `a` to node `a'`, i.e,
a nonempty sequence of chained edges from `a` to `a'`.
-/
inductive Path {α : Type u} {β : Type v}
    [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] (g : Graph α β) :
    α → α → Type (max u v) where
  /-- A path corresponding to a single edge. -/
  | sing (e : Edge α β) (h : e ∈ g := by decide) :
      Path g e.source e.target
  /-- A path corresponding to one edge followed by a path. -/
  | cons (e : Edge α β) (h : e ∈ g := by decide) {b : α} :
      Path g e.target b → Path g e.source b

namespace Path

/-- Counts the number of edges in a path. -/
def length {graph : Graph α β} {a a' : α} : Path graph a a' → Nat
  | sing _ _ => 1
  | cons _ _ p => p.length + 1

theorem length_pos {g : Graph α β} {a a' : α} (p : Path g a a') :
    0 < p.length := by
  cases p <;> simp [length]

/-- Gets the labels of the edges along a path. -/
def labels {graph : Graph α β} {a a' : α} : Path graph a a' → List β
  | sing e _ => [e.label]
  | cons e _ p => e.label :: p.labels

/-- Concatenates two paths. -/
def append {graph : Graph α β} {a₁ a₂ a₃ : α} :
    Path graph a₁ a₂ → Path graph a₂ a₃ → Path graph a₁ a₃
  | sing e h, q => cons e h q
  | cons e h p, q => cons e h (p.append q)

theorem length_append {graph : Graph α β} {a₁ a₂ a₃ : α}
    (p : Path graph a₁ a₂) (q : Path graph a₂ a₃) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | sing e h => simp [append, length, Nat.add_comm]
  | cons e h p ih => simp [append, length, ih]; omega

/-- Converts a path to a list of edges. -/
def toList {g : Graph α β} {a a' : α} : Path g a a' → List (Edge α β)
  | sing e _ => [e]
  | cons e _ p => e :: p.toList

theorem length_eq {g : Graph α β} {a a' : α} (p : Path g a a') :
    p.length = p.toList.length := by
  induction p with
  | sing e h => simp [length, toList]
  | cons e h p ih => simp [length, toList, ih]

theorem mem_of_mem_toList {g : Graph α β} {a a' : α} {p : Path g a a'}
    {e : Edge α β} (he : e ∈ p.toList) : e ∈ g := by
  induction p with
  | sing e' h' => simp [toList] at he; subst he; exact h'
  | cons e' h' p ih =>
    simp [toList] at he
    rcases he with rfl | he
    · exact h'
    · exact ih he

/-- If `e` occurs in `q`, then `q` has a suffix path starting with `e`. -/
theorem exists_suffix {g : Graph α β} {a a' : α} (q : Path g a a')
    (e : Edge α β) (he : e ∈ q.toList) :
    ∃ r : Path g e.source a', r.toList <:+ q.toList := by
  induction q with
  | sing e' h' =>
    simp [toList] at he
    subst he
    exact ⟨.sing _ h', List.suffix_refl _⟩
  | cons e' h' p ih =>
    simp [toList] at he
    rcases he with rfl | he
    · exact ⟨.cons _ h' p, List.suffix_refl _⟩
    · obtain ⟨r, hr⟩ := ih he
      exact ⟨r, hr.trans (List.suffix_cons _ _)⟩

/-- Every path can be replaced by one with no repeated edges that uses only
edges of the original. -/
theorem exists_nodup {g : Graph α β} {a a' : α} (p : Path g a a') :
    ∃ q : Path g a a', q.toList.Nodup ∧ q.toList ⊆ p.toList := by
  induction p with
  | sing e h => exact ⟨.sing e h, by simp [toList], fun x hx ↦ hx⟩
  | cons e h p ih =>
    obtain ⟨q, hn, hs⟩ := ih
    by_cases hm : e ∈ q.toList
    · obtain ⟨r, hr⟩ := exists_suffix q e hm
      refine ⟨r, hr.sublist.nodup hn, fun x hx ↦ ?_⟩
      exact List.mem_cons_of_mem _ (hs (hr.sublist.subset hx))
    · refine ⟨.cons e h q, ?_, fun x hx ↦ ?_⟩
      · exact List.nodup_cons.mpr ⟨hm, hn⟩
      · simp [toList] at hx ⊢
        rcases hx with hx | hx
        · exact .inl hx
        · exact .inr (hs hx)

/-- A reachable node is reached by a path with at most `g.length` edges. -/
theorem exists_short {g : Graph α β} {a a' : α} (p : Path g a a') :
    ∃ q : Path g a a', q.length ≤ g.length := by
  obtain ⟨q, hn, -⟩ := exists_nodup p
  refine ⟨q, ?_⟩
  rw [length_eq]
  exact hn.length_le_of_subset fun _ hx ↦ mem_of_mem_toList hx

end Path

/-! ## Reachability -/

/-- `a'` is reachable from `a` in `g` if there is a path from `a` to `a'`. -/
def Reachable (g : Graph α β) (a a' : α) : Prop :=
  Nonempty (Path g a a')

/-- The reachability relation is transitive. -/
theorem Reachable.trans {g : Graph α β} {a₁ a₂ a₃ : α}
    (h₁ : Reachable g a₁ a₂) (h₂ : Reachable g a₂ a₃) :
    Reachable g a₁ a₃ := by
  obtain ⟨p⟩ := h₁
  obtain ⟨q⟩ := h₂
  exact ⟨p.append q⟩

/-- Checks whether `a'` can be reached from `a` by a path of at most `n`
edges in `g`, searching depth-first. -/
def reachIn (g : Graph α β) : Nat → α → α → Bool
  | 0, _, _ => false
  | n + 1, a, a' => g.any (fun e ↦
      e.hasSource a && (e.hasTarget a' || reachIn g n e.target a'))

theorem reachIn_iff (g : Graph α β) (n : Nat) (a a' : α) :
    g.reachIn n a a' ↔ ∃ p : Path g a a', p.length ≤ n := by
  induction n generalizing a with
  | zero =>
    simp only [reachIn, Bool.false_eq_true, false_iff, not_exists]
    intro p; have := p.length_pos; omega
  | succ n ih =>
    simp only [reachIn, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      Edge.hasSource, Edge.hasTarget, beq_iff_eq]
    constructor
    · rintro ⟨e, he, hs, ht | ht⟩
      · subst hs ht; exact ⟨.sing e he, by simp [Path.length]⟩
      · subst hs
        obtain ⟨p, hp⟩ := (ih _).mp ht
        exact ⟨.cons e he p, by simp [Path.length]; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | sing e h => exact ⟨e, h, rfl, .inl rfl⟩
      | cons e h p =>
        refine ⟨e, h, rfl, .inr ((ih _).mpr ⟨p, ?_⟩)⟩
        simp [Path.length] at hp; omega

/-- Algorithm for checking whether there is a path from `a` to `a'` in `g`.
A shortest path never repeats an edge, so it has at most `g.length` edges. -/
def reachable (g : Graph α β) (a a' : α) : Bool :=
  reachIn g g.length a a'

/-- `reachable` decides `Reachable`. -/
theorem reachable_iff (g : Graph α β) (a a' : α) :
    g.reachable a a' ↔ g.Reachable a a' := by
  unfold reachable Reachable; rw [reachIn_iff]
  constructor
  · rintro ⟨p, -⟩; exact ⟨p⟩
  · rintro ⟨p⟩; exact p.exists_short

/-- `Reachable` is decidable. -/
instance (g : Graph α β) (a a' : α) : Decidable (Reachable g a a') :=
  decidable_of_iff _ (reachable_iff _ _ _)

/-! ## Acyclicity -/

/-- A `graph` is acyclic if no path starts and ends on a same node. -/
def Acyclic (g : Graph α β) : Prop :=
  ∀ a, ¬g.Reachable a a

/-- Acyclicity implies irreflexivity. -/
theorem irref_of_acyclic (g : Graph α β) : g.Acyclic → g.Irrefl := by
  intro h edge he heq; apply h edge.source; constructor
  have p : Path g edge.source edge.target := .sing edge he
  rw [← heq] at p; assumption

/-- Algorithm for checking whether the graph is acyclic.  A cycle must pass
through the source of some edge, so it is enough to check that
no edge's source can reach itself. -/
def acyclic (g : Graph α β) : Bool :=
  g.all (fun e ↦ !g.reachable e.source e.source)

/-- `acyclic` decides `Acyclic`. -/
theorem acyclic_iff (g : Graph α β) : g.acyclic ↔ g.Acyclic := by
  have first : ∀ {x y : α}, Path g x y → ∃ e ∈ g, e.source = x := by
    intro x y p
    cases p with
    | sing e h => exact ⟨e, h, rfl⟩
    | cons e h _ => exact ⟨e, h, rfl⟩
  simp only [acyclic, List.all_eq_true]
  constructor
  · rintro h a ⟨p⟩
    obtain ⟨e, he, rfl⟩ := first p
    have hr : g.reachable e.source e.source = true :=
      (reachable_iff _ _ _).mpr ⟨p⟩
    simpa [hr] using h e he
  · intro h e he
    cases hr : g.reachable e.source e.source
    · rfl
    · exact absurd ((reachable_iff _ _ _).mp hr) (h _)

/-- `Acyclic` is decidable. -/
instance (g : Graph α β) : Decidable (Acyclic g) :=
  decidable_of_iff _ (acyclic_iff _)

end Graph

end Hello.Graph
