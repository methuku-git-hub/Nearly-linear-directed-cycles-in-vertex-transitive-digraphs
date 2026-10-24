import DirectedCycles.BranchingPaths
import DirectedCycles.ActionCoordinates

set_option autoImplicit false
namespace DirectedCycles

/-- Ordered product of edge labels along a vertex list. -/
def pathVoltage {G I : Type*} [Group G] (label : I → I → G) : List I → G
  | [] => 1
  | [_] => 1
  | x :: y :: l => label x y * pathVoltage label (y :: l)

theorem pathVoltage_append_singleton {G I : Type*} [Group G] (label : I → I → G)
    (l : List I) (hne : l ≠ []) (y : I) :
    pathVoltage label (l ++ [y]) = pathVoltage label l * label (l.getLast hne) y := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
    cases l with
    | nil => simp [pathVoltage]
    | cons b l =>
      simpa only [List.cons_append,pathVoltage,List.getLast_cons_cons,mul_assoc]
        using congrArg (fun z => label a b * z) (ih (by simp))

namespace PartialOutBranching
variable {G I : Type*} [Group G] {D : Digraph I} {root : I} {U : Finset I}

noncomputable def potential (B : PartialOutBranching D root U) (label : I → I → G)
    (v : I) (hv : v ∈ U) : G := pathVoltage label (B.path v hv).vertices

theorem potential_root (B : PartialOutBranching D root U) (label : I → I → G) :
    B.potential label root B.root_mem = 1 := by
  simp only [potential,B.root_path,pathVoltage]

theorem potential_arc (B : PartialOutBranching D root U) (label : I → I → G)
    {x y : I} (hx : x ∈ U) (hy : y ∈ U) (hxy : B.arc x y) :
    B.potential label y hy = B.potential label x hx * label x y := by
  unfold potential
  rw [B.path_append_of_arc hx hy hxy,
    pathVoltage_append_singleton label _ (B.path x hx).nonempty y]
  have hh : (B.path x hx).vertices.getLast (B.path x hx).nonempty = x := by
    apply Option.some.inj
    rw [← List.getLast?_eq_some_getLast,(B.path x hx).last]
  rw [hh]

end PartialOutBranching

/-- Changing orbit representatives transforms labels by this exact formula. -/
def gaugeLabels {G I : Type*} [Group G] (S : I → I → Set G) (p : I → G) : I → I → Set G :=
  fun i j => (fun s => p i * s * (p j)⁻¹) '' S i j

def gaugeCoordinates {G I : Type*} [Group G] (p : I → G) : G × I ≃ G × I where
  toFun z := (z.1 * p z.2,z.2)
  invFun z := (z.1 * (p z.2)⁻¹,z.2)
  left_inv z := by simp
  right_inv z := by simp

theorem gaugeLabels_arc {G I : Type*} [Group G] (S : I → I → Set G) (p : I → G)
    (x y : G × I) :
    VoltageDigraph (gaugeLabels S p) x y ↔
      VoltageDigraph S (gaugeCoordinates p x) (gaugeCoordinates p y) := by
  constructor
  · rintro ⟨s,⟨t,ht,rfl⟩,he⟩
    refine ⟨t,ht,?_⟩
    change y.1 * p y.2 = x.1 * p x.2 * t
    rw [he]
    group
  · rintro ⟨s,hs,he⟩
    refine ⟨p x.2 * s * (p y.2)⁻¹,⟨s,hs,rfl⟩,?_⟩
    change y.1 * p y.2 = x.1 * p x.2 * s at he
    have hh := congrArg (fun z => z * (p y.2)⁻¹) he
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using hh

theorem gaugeLabels_stronglyConnected {G I : Type*} [Group G]
    (S : I → I → Set G) (p : I → G) (hsc : StronglyConnected (VoltageDigraph S)) :
    StronglyConnected (VoltageDigraph (gaugeLabels S p)) := by
  intro x y
  have hmap : ∀ u v, VoltageDigraph S u v →
      VoltageDigraph (gaugeLabels S p) ((gaugeCoordinates p).symm u) ((gaugeCoordinates p).symm v) := by
    intro u v huv
    apply (gaugeLabels_arc S p _ _).mpr
    simpa using huv
  simpa using reachable_map (gaugeCoordinates p).symm hmap
    (hsc (gaugeCoordinates p x) (gaugeCoordinates p y))

theorem gauge_outward_tree {G I : Type*} [Group G] [Fintype I]
    {D : Digraph I} {root : I} (B : PartialOutBranching D root Finset.univ)
    (S : I → I → Set G) (label : I → I → G)
    (hl : ∀ x y, B.arc x y → label x y ∈ S x y) :
    let p := fun i => B.potential label i (Finset.mem_univ i)
    p root = 1 ∧ ∀ x y, B.arc x y → 1 ∈ gaugeLabels S p x y := by
  dsimp only
  refine ⟨B.potential_root label,?_⟩
  intro x y hxy
  refine ⟨label x y,hl x y hxy,?_⟩
  dsimp only
  rw [B.potential_arc label (Finset.mem_univ x) (Finset.mem_univ y) hxy]
  exact mul_inv_cancel _

end DirectedCycles
