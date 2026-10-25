module

public import DirectedCycles.LocalProductCompression
public import DirectedCycles.LocalTwoProducts
public import DirectedCycles.LocalGlobalSubgroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {H A : Set G}

/-- Conjugating an actual subgroup in a sufficiently large local domain gives
an actual local homomorphism from that group. Six-letter products justify the
cancellation between two conjugates. -/
theorem IsGlobalSubgroup.exists_conjugationHom (hH : L.IsGlobalSubgroup H)
    (hr : L.Reversible) (hHA : H ⊆ A) (hdom : L.AllProductsDefined A 6)
    {b : G} (hb : b ∈ A) (hbi : L.inv b ∈ A) :
    letI := hH.toGroup
    ∃ f : LocalGroupHom (ofGroup H) L,
      ∀ h : H, L.Product [b,h.val,L.inv b] (f.toFun h) := by
  let := hH.toGroup
  have hex : ∀ h : H, ∃ x, L.Product [b,h.val,L.inv b] x := by
    intro h
    apply hdom _ (by simp)
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hb
    · exact hHA h.property
    · exact hbi
  choose φ hφ using hex
  have h1 : φ 1 = L.one := by
    have hs := hφ 1
    change L.Product [b,L.one,L.inv b] (φ 1) at hs
    have hc : List.Forall₂ L.Product [[b,L.one],[L.inv b]] [b,L.inv b] :=
      List.Forall₂.cons ((Product.pair_iff L b L.one b).2 (L.mul_one b))
        (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil)
    have ht := (show L.Product ([[b,L.one],[L.inv b]] : List (List G)).flatten (φ 1) from hs).compress L hc
    exact L.unique ((Product.pair_iff L _ _ _).1 ht) (L.mul_inv b)
  have hinv : ∀ h : H, φ h⁻¹ = L.inv (φ h) := by
    intro h
    have hs := (hφ h).reverse_inv L hr
    have hs' : L.Product [b,(h⁻¹).val,L.inv b] (L.inv (φ h)) := by
      change L.Product [b,L.inv h.val,L.inv b] (L.inv (φ h))
      simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_append,
        List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append,L.inv_inv] using hs
    exact (hφ h⁻¹).unique L hs'
  have hmul : ∀ h k : H, L.mulRel (φ h) (φ k) (φ (h*k)) := by
    intro h k
    obtain ⟨z,hz⟩ := hdom [b,h.val,L.inv b,b,k.val,L.inv b] (by simp) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hb
      · exact hHA h.property
      · exact hbi
      · exact hb
      · exact hHA k.property
      · exact hbi)
    have hblocks : List.Forall₂ L.Product
        [[b,h.val,L.inv b],[b,k.val,L.inv b]] [φ h,φ k] :=
      List.Forall₂.cons (hφ h) (List.Forall₂.cons (hφ k) List.Forall₂.nil)
    have hp : L.Product [φ h,φ k] z :=
      (show L.Product ([[b,h.val,L.inv b],[b,k.val,L.inv b]] : List (List G)).flatten z from hz).compress L hblocks
    have hc : List.Forall₂ L.Product
        [[b],[h.val],[L.inv b,b],[k.val],[L.inv b]] [b,h.val,L.one,k.val,L.inv b] :=
      List.Forall₂.cons (Product.singleton _)
        (List.Forall₂.cons (Product.singleton _)
          (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 (L.inv_mul b))
            (List.Forall₂.cons (Product.singleton _)
              (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil))))
    have hs : L.Product [b,h.val,L.one,k.val,L.inv b] z :=
      (show L.Product ([[b],[h.val],[L.inv b,b],[k.val],[L.inv b]] : List (List G)).flatten z from hz).compress L hc
    have hhk : L.Product [h.val,L.one,k.val] (h*k).val := by
      have hv := (ofGroup_product H [h,1,k]).map hH.inclusionHom
      dsimp only [IsGlobalSubgroup.inclusionHom] at hv
      have heone : (1 : H).val = L.one := rfl
      simpa only [heone,List.prod_cons,List.prod_nil,_root_.mul_one,_root_.one_mul,
        List.map_cons,List.map_nil] using hv
    have hc' : List.Forall₂ L.Product [[b],[h.val,L.one,k.val],[L.inv b]] [b,(h*k).val,L.inv b] :=
      List.Forall₂.cons (Product.singleton _)
        (List.Forall₂.cons hhk (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil))
    have hs' : L.Product [b,(h*k).val,L.inv b] z :=
      (show L.Product ([[b],[h.val,L.one,k.val],[L.inv b]] : List (List G)).flatten z from hs).compress L hc'
    have he : z = φ (h*k) := hs'.unique L (hφ (h*k))
    exact he ▸ ((Product.pair_iff L _ _ _).1 hp)
  refine ⟨⟨φ,h1,hinv,?_⟩,hφ⟩
  intro h k l he
  change h*k = l at he
  exact he ▸ hmul h k
end LocalGroupAlgebra
end DirectedCycles
