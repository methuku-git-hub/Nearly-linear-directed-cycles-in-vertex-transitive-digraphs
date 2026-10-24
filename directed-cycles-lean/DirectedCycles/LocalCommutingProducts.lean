import DirectedCycles.LocalProductSwap

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The four-factor interchange law, with both resulting products actually
constructed from the common four-letter domain. -/
theorem commuting_products {A : Set G} (hdom : L.AllProductsDefined A 4)
    {a b c d ab cd ac bd : G} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hbc : L.Commute b c) (hab : L.mulRel a b ab) (hcd : L.mulRel c d cd)
    (hac : L.mulRel a c ac) (hbd : L.mulRel b d bd) :
    ∃ z, L.mulRel ab cd z ∧ L.mulRel ac bd z := by
  obtain ⟨z,hz⟩ := hdom [a,b,c,d] (by simp) (by aesop)
  obtain ⟨w,hw⟩ := hdom [a,c,b,d] (by simp) (by aesop)
  have he : z = w := Product.swap_pair_value L hbc (a := [a]) (b := [d]) hz hw
  have hblocks : List.Forall₂ L.Product [[a,b],[c,d]] [ab,cd] :=
    List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hab)
      (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hcd) List.Forall₂.nil)
  have hblocks' : List.Forall₂ L.Product [[a,c],[b,d]] [ac,bd] :=
    List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hac)
      (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hbd) List.Forall₂.nil)
  have hz' : L.Product ([[a,b],[c,d]] : List (List G)).flatten z := by simpa using hz
  have hw' : L.Product ([[a,c],[b,d]] : List (List G)).flatten w := by simpa using hw
  exact ⟨z,(Product.pair_iff L _ _ _).1 (hz'.compress L hblocks),
    he.symm ▸ (Product.pair_iff L _ _ _).1 (hw'.compress L hblocks')⟩
end LocalGroupAlgebra
end DirectedCycles
