module

public import DirectedCycles.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A cyclic layer digraph with right-multiplication labels. Loops remain
possible when the number of layers is one. -/
def CyclicLayerDigraph {G : Type*} [Group G] {T : ℕ} (S : ZMod T → Set G) :
    Digraph (G × ZMod T) := fun x y => y.2 = x.2+1 ∧ ∃ a ∈ S x.2, y.1 = x.1*a

/-- A word has an allowed label at each successive cyclic position. -/
def LayerWord {G : Type*} [Group G] {T : ℕ} (S : ZMod T → Set G) : ZMod T → List G → Prop
  | _, [] => True
  | i, a::xs => a ∈ S i ∧ LayerWord S (i+1) xs

/-- Following an allowed word realizes its ordered product. -/
theorem layerWord_reachable {G : Type*} [Group G] {T : ℕ} (S : ZMod T → Set G)
    (x : G) (i : ZMod T) (xs : List G) (h : LayerWord S i xs) :
    Reachable (CyclicLayerDigraph S) (x,i) (x*xs.prod,i+(xs.length : ZMod T)) := by
  induction xs generalizing x i with
  | nil => simpa [Reachable] using (Relation.ReflTransGen.refl : Reachable (CyclicLayerDigraph S) (x,i) (x,i))
  | cons a xs ih =>
    have ha : CyclicLayerDigraph S (x,i) (x*a,i+1) := ⟨rfl,a,h.1,rfl⟩
    have hp := (Relation.ReflTransGen.single ha).trans (ih (x*a) (i+1) h.2)
    simpa only [Reachable,List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one,mul_assoc,
      add_assoc,add_comm,add_left_comm] using hp

/-- Left multiplication translates paths without changing their labels. -/
theorem cyclicLayer_reachable_translate {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (b : G) {x y : G × ZMod T}
    (h : Reachable (CyclicLayerDigraph S) x y) :
    Reachable (CyclicLayerDigraph S) (b*x.1,x.2) (b*y.1,y.2) := by
  apply reachable_map (fun z => (b*z.1,z.2)) _ h
  intro u v huv
  obtain ⟨ht,a,ha,he⟩ := huv
  refine ⟨ht,a,ha,?_⟩
  change b*v.1 = (b*u.1)*a
  rw [he,mul_assoc]

/-- A fixed choice of baseline labels supplies a word of every length. -/
def baselineLayerWord {G : Type*} [Group G] {T : ℕ} (beta : ZMod T → G) :
    ZMod T → ℕ → List G
  | _, 0 => []
  | i, n+1 => beta i :: baselineLayerWord beta (i+1) n

@[simp] theorem baselineLayerWord_length {G : Type*} [Group G] {T : ℕ}
    (beta : ZMod T → G) (i : ZMod T) (n : ℕ) : (baselineLayerWord beta i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [baselineLayerWord,ih]

theorem baselineLayerWord_allowed {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (beta : ZMod T → G) (hb : ∀ i, beta i ∈ S i)
    (i : ZMod T) (n : ℕ) : LayerWord S i (baselineLayerWord beta i n) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih => exact ⟨hb i,ih (i+1)⟩

/-- Products of all allowed full rounds based at layer zero. -/
def layerRoundProducts {G : Type*} [Group G] {T : ℕ} (S : ZMod T → Set G) : Set G :=
  {g | ∃ xs : List G, xs.length = T ∧ LayerWord S 0 xs ∧ xs.prod = g}

/-- In a finite group, generated full-round products reach every coordinate
in the base layer, using forward walks only. -/
theorem cyclicLayer_base_reachable {G : Type*} [Group G] [Finite G] {T : ℕ}
    (S : ZMod T → Set G) (hgen : Subgroup.closure (layerRoundProducts S) = ⊤) (g : G) :
    Reachable (CyclicLayerDigraph S) (1,0) (g,0) := by
  let R : Submonoid G := {
    carrier := {g | Reachable (CyclicLayerDigraph S) (1,0) (g,0)}
    one_mem' := Relation.ReflTransGen.refl
    mul_mem' := by
      intro x y hx hy
      have h := cyclicLayer_reachable_translate S x hy
      have h' : Reachable (CyclicLayerDigraph S) (x,0) (x*y,0) := by
        simpa only [Prod.fst,Prod.snd,mul_one] using h
      exact hx.trans h' }
  have hR : Submonoid.closure (layerRoundProducts S) ≤ R := by
    apply Submonoid.closure_le.mpr
    rintro x ⟨xs,hlen,hxs,rfl⟩
    have h := layerWord_reachable S 1 0 xs hxs
    change Reachable (CyclicLayerDigraph S) (1,0) (xs.prod,0)
    simpa only [hlen,ZMod.natCast_self,zero_add,one_mul] using h
  have hcl : Submonoid.closure (layerRoundProducts S) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite,hgen,Subgroup.top_toSubmonoid]
  exact hR (by rw [hcl]; trivial)

end DirectedCycles
