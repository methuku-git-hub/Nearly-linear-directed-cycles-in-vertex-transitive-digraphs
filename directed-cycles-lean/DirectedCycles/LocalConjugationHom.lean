import DirectedCycles.LocalConjugates
import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalProductRestriction
import DirectedCycles.LocalEscapeMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Conjugation on an inverse-closed local window is an actual local
homomorphism. Six-letter domains justify multiplication of two conjugates. -/
theorem exists_conjugationHom_on (hr : L.Reversible) {A R : Set G}
    (hA1 : L.one ∈ A) (hAi : ∀ x ∈ A, L.inv x ∈ A) (hAR : A ⊆ R)
    (hdom : L.AllProductsDefined R 6) {b : G} (hb : b ∈ R) (hbi : L.inv b ∈ R) :
    ∃ f : LocalGroupHom (L.restrict A hA1 hAi) L,
      ∀ h : A, L.Product [b,h.val,L.inv b] (f.toFun h) := by
  have hex : ∀ h : A, ∃ x, L.Product [b,h.val,L.inv b] x := by
    intro h
    apply hdom _ (by simp)
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hb
    · exact hAR h.property
    · exact hbi
  choose φ hφ using hex
  have h1 : φ ⟨L.one,hA1⟩ = L.one := by
    have hc : List.Forall₂ L.Product [[b,L.one],[L.inv b]] [b,L.inv b] :=
      List.Forall₂.cons ((Product.pair_iff L _ _ _).2 (L.mul_one b))
        (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil)
    have ht := (show L.Product ([[b,L.one],[L.inv b]] : List (List G)).flatten (φ ⟨L.one,hA1⟩)
      from hφ ⟨L.one,hA1⟩).compress L hc
    exact L.unique ((Product.pair_iff L _ _ _).1 ht) (L.mul_inv b)
  have hinv : ∀ h : A, φ ⟨L.inv h.val,hAi _ h.property⟩ = L.inv (φ h) := by
    intro h
    apply (hφ _).unique L
    simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_append,
      List.map_cons,List.map_nil,List.cons_append,L.inv_inv] using (hφ h).reverse_inv L hr
  have hmul : ∀ h k j : A, L.mulRel h.val k.val j.val → L.mulRel (φ h) (φ k) (φ j) := by
    intro h k j hm
    obtain ⟨z,hz⟩ := hdom [b,h.val,L.inv b,b,k.val,L.inv b] (by simp) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hb
      · exact hAR h.property
      · exact hbi
      · exact hb
      · exact hAR k.property
      · exact hbi)
    have hblocks : List.Forall₂ L.Product [[b,h.val,L.inv b],[b,k.val,L.inv b]] [φ h,φ k] :=
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
    have hj : L.Product [h.val,L.one,k.val] j.val :=
      Product.triple_of_rel L (L.mul_one _) (L.one_mul _) hm hm
    have hc' : List.Forall₂ L.Product [[b],[h.val,L.one,k.val],[L.inv b]] [b,j.val,L.inv b] :=
      List.Forall₂.cons (Product.singleton _)
        (List.Forall₂.cons hj (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil))
    have hs' : L.Product [b,j.val,L.inv b] z :=
      (show L.Product ([[b],[h.val,L.one,k.val],[L.inv b]] : List (List G)).flatten z from hs).compress L hc'
    have he : z = φ j := hs'.unique L (hφ j)
    exact he ▸ ((Product.pair_iff L _ _ _).1 hp)
  exact ⟨⟨φ,h1,hinv,fun {h k j} hm => hmul h k j hm⟩,hφ⟩

/-- A local homomorphism on a restricted window preserves every finite power
segment staying in that window. Restriction is justified for every subword,
not just for the final power value. -/
theorem powerIn_restricted_image {H : Type*} {M : LocalGroupAlgebra H} {A : Set G}
    (hA1 : L.one ∈ A) (hAi : ∀ x ∈ A, L.inv x ∈ A)
    (f : LocalGroupHom (L.restrict A hA1 hAi) M) {g : G} (hg : g ∈ A)
    {N : ℕ} (hp : ∀ n ≤ N, L.PowerIn A g n) :
    ∀ n ≤ N, M.PowerIn (Set.range f.toFun) (f.toFun ⟨g,hg⟩) n := by
  have hrepl : ∀ l : List G, (∀ a ∈ l, a ∈ ({g} : Set G)) → l = List.replicate l.length g := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha : a = g := hl a (List.mem_cons_self ..)
      have ht := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
      simp only [List.length_cons,List.replicate_succ]
      exact congrArg₂ List.cons ha ht
  have hdef : L.AllProductsDefined {g} N := by
    intro l hl hm
    obtain ⟨x,_,hx⟩ := hp l.length hl
    exact ⟨x,hrepl l hm ▸ hx⟩
  have hvals : ∀ n ≤ N, L.wordPower {g} n ⊆ A := by
    rintro n hn x ⟨l,hlen,hl,hx⟩
    obtain ⟨y,hy,hpy⟩ := hp n hn
    have he : l = List.replicate n g := (hrepl l hl).trans (by rw [hlen])
    rw [he] at hx
    exact (hx.unique L hpy).symm ▸ hy
  have hrestricted := L.allProductsDefined_restrict A hA1 hAi hdef hvals
  intro n hn
  obtain ⟨x,hx⟩ := hrestricted (List.replicate n (⟨g,hg⟩ : A)) (by simpa only [List.length_replicate] using hn) (by
    intro a ha
    have he : a = (⟨g,hg⟩ : A) := (List.mem_replicate.mp ha).2
    exact he ▸ (show ((⟨g,hg⟩ : A).val ∈ ({g} : Set G)) from rfl))
  exact ⟨f.toFun x,⟨x,rfl⟩,by simpa only [List.map_replicate] using hx.map f⟩

theorem escapeNorm_restricted_image_le {H : Type*} {M : LocalGroupAlgebra H} {A : Set G}
    (hA1 : L.one ∈ A) (hAi : ∀ x ∈ A, L.inv x ∈ A)
    (f : LocalGroupHom (L.restrict A hA1 hAi) M) {g : G} (hg : g ∈ A) :
    M.escapeNorm (Set.range f.toFun) (f.toFun ⟨g,hg⟩) ≤ L.escapeNorm A g := by
  apply le_csInf (L.escapeValues_nonempty hA1 g)
  rintro r ⟨n,hn,rfl⟩
  exact M.escapeNorm_le_of_powers (L.powerIn_restricted_image hA1 hAi f hg hn)
end LocalGroupAlgebra
end DirectedCycles
