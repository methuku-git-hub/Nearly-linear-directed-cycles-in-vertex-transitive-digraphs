module

public import DirectedCycles.ReturnPathFamily

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

namespace SimplePath
variable {G I : Type*} [Group G] {S : I → I → Set G} {root : I} {s : G}

def translateRoot (P : SimplePath (VoltageDigraph S) (1,root) (s,root)) (x : G) :
    SimplePath (VoltageDigraph S) (x,root) (x*s,root) where
  vertices := P.vertices.map (voltageLeftTranslate x)
  nodup := P.nodup.map (voltageLeftTranslate x).injective
  head := by simp [List.head?_map,P.head,voltageLeftTranslate]
  last := by simp [List.getLast?_map,P.last,voltageLeftTranslate]
  chain := by
    rw [List.isChain_map]
    exact P.chain.imp (voltageLeftTranslate_arc S x)

theorem last_not_mem_dropLast {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) : y ∉ P.vertices.dropLast := by
  have hn := P.nodup
  rw [P.eq_dropLast_append,List.nodup_append] at hn
  intro hy
  exact hn.2.2 y hy y (by simp) rfl

theorem translated_occurrence (P : SimplePath (VoltageDigraph S) (1,root) (s,root))
    (t : I → G) (hc : ∀ z ∈ P.vertices, z.1 = 1 ∨ z.1 = s*(t z.2)⁻¹)
    (x : G) (z : G × I) (hz : z ∈ (P.translateRoot x).vertices) :
    z.1 = x ∨ z.1 = x*s*(t z.2)⁻¹ := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  rcases hc w hw with he | he
  · exact Or.inl (by change x*w.1=x; rw [he,mul_one])
  · exact Or.inr (by change x*w.1=x*s*(t w.2)⁻¹; rw [he,mul_assoc])

theorem translated_root_occurrence (P : SimplePath (VoltageDigraph S) (1,root) (s,root))
    (t : I → G) (ht : t root = 1)
    (hc : ∀ z ∈ P.vertices, z.1 = 1 ∨ z.1 = s*(t z.2)⁻¹)
    (x : G) (z : G × I) (hz : z ∈ (P.translateRoot x).vertices.dropLast) (hr : z.2 = root) :
    z = (x,root) := by
  have hmem := List.mem_of_mem_dropLast hz
  rcases P.translated_occurrence t hc x z hmem with he | he
  · exact Prod.ext he hr
  · have he' : z = (x*s,root) := by
      apply Prod.ext
      · simpa only [hr,ht,inv_one,mul_one] using he
      · exact hr
    exact ((P.translateRoot x).last_not_mem_dropLast (he' ▸ hz)).elim

theorem translates_disjoint {H : Type*} [Group H]
    (P : SimplePath (VoltageDigraph S) (1,root) (s,root)) (q : G →* H)
    (hnd : (P.vertices.map (fun z => (q z.1,z.2))).Nodup)
    (x y : G) (hq : q x = q y) (hne : x ≠ y) :
    (P.translateRoot x).vertices.Disjoint (P.translateRoot y).vertices :=
  quotient_simple_translates_disjoint q P.vertices hnd x y hq hne

theorem translates_disjoint_of_no_mixed {s' : G}
    (P : SimplePath (VoltageDigraph S) (1,root) (s,root))
    (Q : SimplePath (VoltageDigraph S) (1,root) (s',root))
    (t : I → G)
    (hP : ∀ z ∈ P.vertices, z.1 = 1 ∨ z.1 = s*(t z.2)⁻¹)
    (hQ : ∀ z ∈ Q.vertices, z.1 = 1 ∨ z.1 = s'*(t z.2)⁻¹)
    (x y : G) (hstart : x ≠ y) (hend : x*s ≠ y*s')
    (hmixed : ∀ k, y*s' ≠ x*t k ∧ x*s ≠ y*t k) :
    (P.translateRoot x).vertices.Disjoint (Q.translateRoot y).vertices := by
  apply List.disjoint_left.mpr
  intro z hz hz'
  rcases P.translated_occurrence t hP x z hz with he | he <;>
    rcases Q.translated_occurrence t hQ y z hz' with he' | he'
  · exact hstart (he.symm.trans he')
  · exact (hmixed z.2).1 (mul_inv_eq_iff_eq_mul.mp (he'.symm.trans he))
  · exact (hmixed z.2).2 (mul_inv_eq_iff_eq_mul.mp (he.symm.trans he'))
  · exact hend (mul_right_cancel (he.symm.trans he'))

end SimplePath
end DirectedCycles
