import DirectedCycles.SelectedReturnLabels
import DirectedCycles.CayleyStrongConnectivity

set_option autoImplicit false
namespace DirectedCycles

def voltageLeftTranslate {G I : Type*} [Group G] (x : G) : G × I ≃ G × I where
  toFun z := (x*z.1,z.2)
  invFun z := (x⁻¹*z.1,z.2)
  left_inv z := by simp
  right_inv z := by simp

theorem voltageLeftTranslate_arc {G I : Type*} [Group G] (S : I → I → Set G) (x : G)
    (u v : G × I) (huv : VoltageDigraph S u v) :
    VoltageDigraph S (voltageLeftTranslate x u) (voltageLeftTranslate x v) := by
  obtain ⟨s,hs,he⟩ := huv
  refine ⟨s,hs,?_⟩
  change x*v.1 = (x*u.1)*s
  rw [he,mul_assoc]

namespace ReturnSpine
variable {G H I : Type*} [Group G] [Group H] [Fintype I] {S : I → I → Set G} {root : I}

/-- The selected Cayley generators carry actual simple directed paths,
with quotient simplicity and the exact two coordinate possibilities. -/
theorem return_path_family [Finite H] (R : ReturnSpine S root) (q : G →* H)
    (hq : Function.Surjective q) (hsc : StronglyConnected (VoltageDigraph S)) :
    ∃ T : Set G, (∀ s ∈ T, q s ≠ 1) ∧ StronglyConnected (CayleyDigraph (q '' T)) ∧
      ∃ P : ∀ s : T, SimplePath (VoltageDigraph S) (1,root) (s.val,root),
        (∀ s : T, ((P s).vertices.map (fun z => (q z.1,z.2))).Nodup) ∧
        (∀ s : T, ∀ z ∈ (P s).vertices, z.1 = 1 ∨ z.1 = s.val*(R.voltage z.2)⁻¹) := by
  classical
  obtain ⟨T,hT,hgen,hpaths⟩ := R.select_return_labels q hq hsc
  have hchoices : ∀ s : T, ∃ P : SimplePath (VoltageDigraph S) (1,root) (s.val,root),
      (P.vertices.map (fun z => (q z.1,z.2))).Nodup ∧
      ∀ z ∈ P.vertices, z.1 = 1 ∨ z.1 = s.val*(R.voltage z.2)⁻¹ := by
    intro s
    obtain ⟨i,j,u,hu,he,hnd⟩ := hpaths s.val s.property
    let P : SimplePath (VoltageDigraph S) (1,root) (s.val,root) := {
      vertices := R.walkVertices 1 i j u
      nodup := List.Nodup.of_map _ hnd
      head := R.walk_head 1 i j u
      last := by simpa only [one_mul,← he] using R.walk_last 1 i j u
      chain := R.walk_chain 1 i j u hu
    }
    refine ⟨P,hnd,?_⟩
    intro z hz
    simpa only [one_mul,← he] using R.walk_occurrence 1 i j u z hz
  choose P hp hc using hchoices
  exact ⟨T,hT,finite_cayley_stronglyConnected (q '' T) hgen,P,hp,hc⟩

end ReturnSpine
end DirectedCycles
