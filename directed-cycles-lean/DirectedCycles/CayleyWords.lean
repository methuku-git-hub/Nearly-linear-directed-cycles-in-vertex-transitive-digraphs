module

public import DirectedCycles.Paths
public import DirectedCycles.CyclicLayerWords

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The directed right Cayley relation; generators equal to one give loops. -/
def CayleyDigraph {G : Type*} [Group G] (S : Set G) : Digraph G :=
  fun x y => ∃ a ∈ S, y = x*a

/-- The vertices followed by an ordered generator word, including both endpoints. -/
def wordVertices {G : Type*} [Group G] (x : G) : List G → List G
  | [] => [x]
  | a::xs => x :: wordVertices (x*a) xs

@[simp] theorem wordVertices_length {G : Type*} [Group G] (x : G) (xs : List G) :
    (wordVertices x xs).length = xs.length+1 := by
  induction xs generalizing x with
  | nil => rfl
  | cons a xs ih => simp [wordVertices,ih]

@[simp] theorem wordVertices_head {G : Type*} [Group G] (x : G) (xs : List G) :
    (wordVertices x xs).head? = some x := by cases xs <;> rfl

@[simp] theorem wordVertices_last {G : Type*} [Group G] (x : G) (xs : List G) :
    (wordVertices x xs).getLast? = some (x*xs.prod) := by
  induction xs generalizing x with
  | nil => simp [wordVertices]
  | cons a xs ih =>
    have hne : wordVertices (x*a) xs ≠ [] := by
      have h := wordVertices_length (x*a) xs
      intro he
      rw [he,List.length_nil] at h
      omega
    rw [wordVertices,List.getLast?_cons_of_ne_nil hne,ih]
    simp only [List.prod_cons,mul_assoc]

/-- Every listed generator gives the corresponding directed Cayley edge. -/
theorem wordVertices_chain {G : Type*} [Group G] (S : Set G) (x : G) (xs : List G)
    (hxs : ∀ a ∈ xs, a ∈ S) : (wordVertices x xs).IsChain (CayleyDigraph S) := by
  induction xs generalizing x with
  | nil => exact List.isChain_singleton x
  | cons a xs ih =>
    rw [wordVertices,List.isChain_cons]
    refine ⟨?_,ih (x*a) (fun b hb => hxs b (List.mem_cons_of_mem _ hb))⟩
    intro y hy
    have he : y = x*a := by simpa only [wordVertices_head,Option.mem_some_iff,eq_comm] using hy
    exact ⟨a,hxs a (List.mem_cons_self),he⟩

/-- Word paths are exactly equivariant under left translation. -/
theorem wordVertices_translate {G : Type*} [Group G] (b x : G) (xs : List G) :
    wordVertices (b*x) xs = (wordVertices x xs).map (fun y => b*y) := by
  induction xs generalizing x with
  | nil => rfl
  | cons a xs ih => simpa only [wordVertices,List.map_cons,mul_assoc] using congrArg (b*x :: ·) (ih (x*a))

end DirectedCycles
