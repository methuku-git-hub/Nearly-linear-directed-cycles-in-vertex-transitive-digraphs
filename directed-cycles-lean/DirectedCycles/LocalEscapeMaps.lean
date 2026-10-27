module

public import DirectedCycles.LocalEscapeNorm
public import DirectedCycles.LocalProductInversion
public import DirectedCycles.EscapeNorm

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} (L : LocalGroupAlgebra G) {M : LocalGroupAlgebra H}

theorem powerIn_inv_iff (hL : L.Reversible) {A : Set G}
    (hi : ∀ x ∈ A, L.inv x ∈ A) (g : G) (n : ℕ) :
    L.PowerIn A (L.inv g) n ↔ L.PowerIn A g n := by
  constructor
  · rintro ⟨x,hx,hp⟩
    refine ⟨L.inv x,hi x hx,?_⟩
    have h := hp.reverse_inv L hL
    simpa only [List.reverse_replicate,List.map_replicate,L.inv_inv] using h
  · rintro ⟨x,hx,hp⟩
    refine ⟨L.inv x,hi x hx,?_⟩
    simpa only [List.reverse_replicate,List.map_replicate] using hp.reverse_inv L hL

theorem escapeNorm_inv (hL : L.Reversible) {A : Set G}
    (hi : ∀ x ∈ A, L.inv x ∈ A) (g : G) : L.escapeNorm A (L.inv g) = L.escapeNorm A g := by
  unfold escapeNorm
  congr 1
  ext x
  simp only [escapeValues,Set.mem_ofPred_eq,L.powerIn_inv_iff hL hi]

theorem powerIn_image (f : LocalGroupHom L M) {A : Set G} {g : G} {n : ℕ}
    (h : L.PowerIn A g n) : M.PowerIn (f.toFun '' A) (f.toFun g) n := by
  obtain ⟨x,hx,hp⟩ := h
  refine ⟨f.toFun x,⟨x,hx,rfl⟩,?_⟩
  simpa only [List.map_replicate] using hp.map f

theorem escapeNorm_image_le (f : LocalGroupHom L M) {A : Set G} (hA : L.one ∈ A) (g : G) :
    M.escapeNorm (f.toFun '' A) (f.toFun g) ≤ L.escapeNorm A g := by
  apply le_csInf (L.escapeValues_nonempty hA g)
  rintro x ⟨n,hn,rfl⟩
  exact M.escapeNorm_le_of_powers (fun i hi => L.powerIn_image f (hn i hi))

theorem ofGroup_powerIn_iff [Group G] (A : Set G) (g : G) (n : ℕ) :
    (ofGroup G).PowerIn A g n ↔ g^n ∈ A := by
  simp only [PowerIn,ofGroup_product_iff,List.prod_replicate]
  constructor
  · rintro ⟨x,hx,rfl⟩; exact hx
  · exact fun h => ⟨g^n,h,rfl⟩

/-- The local escape norm agrees exactly with the existing global definition
when every ambient multiplication is defined. -/
theorem ofGroup_escapeNorm_eq [Group G] (A : Set G) (g : G) :
    (ofGroup G).escapeNorm A g = DirectedCycles.escapeNorm A g := by
  unfold escapeNorm DirectedCycles.escapeNorm
  congr 1
  ext x
  simp only [escapeValues,DirectedCycles.escapeValues,Set.mem_ofPred_eq,ofGroup_powerIn_iff]
end LocalGroupAlgebra
end DirectedCycles
