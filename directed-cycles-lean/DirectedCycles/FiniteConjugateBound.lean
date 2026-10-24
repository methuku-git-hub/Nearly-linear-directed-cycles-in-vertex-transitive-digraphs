import DirectedCycles.FiniteNormalProducts

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Finite TT Lemma 6.9, with the subgroup's actual index. Normality
inside N is recorded as N lying in the normalizer of H. -/
theorem finite_conjugate_normal_closure_bound {G : Type*} [Group G] [Finite G]
    (S : Set G) (h1 : 1 ∈ S) (hi : S⁻¹ = S) (hgen : Subgroup.closure S = ⊤)
    (N H : Subgroup G) [N.Normal] (hHN : H ≤ N) (hnorm : N ≤ Subgroup.normalizer H)
    (r : ℕ) (hball : (H : Set G) ⊆ S^r) :
    (Subgroup.normalClosure (H : Set G) : Set G) ⊆ S^(N.index*r+2*N.index^2) := by
  classical
  let Q := G ⧸ N
  let : Fintype Q := Fintype.ofFinite Q
  choose t htpow htq using finite_short_coset_representatives S h1 hgen N
  have htp : ∀ q : Q, t q ∈ S^N.index := fun q =>
    Set.pow_subset_pow_right h1 (Nat.sub_le N.index 1) (htpow q)
  let F : Q → Subgroup G := fun q => H.map (MulAut.conj (t q)).toMonoidHom
  have hFN : ∀ q, F q ≤ N := by
    intro q
    have hh := Subgroup.map_mono (f := (MulAut.conj (t q)).toMonoidHom) hHN
    have he : N.map (MulAut.conj (t q)).toMonoidHom = N := Subgroup.Normal.map_conj_eq N (t q)
    rw [he] at hh
    exact hh
  have hFnorm : ∀ q, N ≤ Subgroup.normalizer (F q) := by
    intro q
    have hh := (Subgroup.map_mono (f := (MulAut.conj (t q)).toMonoidHom) hnorm).trans
      (Subgroup.le_normalizer_map (H := H) (MulAut.conj (t q)).toMonoidHom)
    have he : N.map (MulAut.conj (t q)).toMonoidHom = N := Subgroup.Normal.map_conj_eq N (t q)
    rw [he] at hh
    exact hh
  have hFb : ∀ q, (F q : Set G) ⊆ S^(r+2*N.index) := by
    intro q g hg
    obtain ⟨a,ha,rfl⟩ := hg
    have hip : (S^N.index)⁻¹ = S^N.index := by rw [← inv_pow,hi]
    have hti : (t q)⁻¹ ∈ S^N.index := hip ▸ Set.inv_mem_inv.mpr (htp q)
    have hh := Set.mul_mem_mul (Set.mul_mem_mul (htp q) (hball ha)) hti
    rw [← pow_add,← pow_add] at hh
    change t q*a*(t q)⁻¹ ∈ S^(r+2*N.index)
    convert hh using 1
    congr 1
    omega
  have hclosure : Subgroup.normalClosure (H : Set G) ≤ ⨆ q, F q := by
    apply (⨆ q, F q : Subgroup G).closure_le.mpr
    intro g hg
    obtain ⟨a,ha,hh⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨b,rfl⟩ := isConj_iff.mp hh
    let q : Q := Quotient.mk'' b
    have hcoset : (t q)⁻¹*b ∈ N := QuotientGroup.leftRel_apply.mp (Quotient.exact (htq q))
    have hconj : ((t q)⁻¹*b)*a*((t q)⁻¹*b)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hcoset) a).mp ha
    apply Subgroup.mem_iSup_of_mem q
    refine ⟨_,hconj,?_⟩
    change t q*(((t q)⁻¹*b)*a*((t q)⁻¹*b)⁻¹)*(t q)⁻¹ = b*a*b⁻¹
    group
  have hb := finite_normal_sup_power_bound S N F (r+2*N.index) hFN hFnorm hFb
  intro g hg
  have hh := hb (hclosure hg)
  have hcard : Fintype.card Q = N.index := by
    rw [← Nat.card_eq_fintype_card]
    exact N.index_eq_card.symm
  rw [hcard] at hh
  convert hh using 1
  congr 1
  ring

end DirectedCycles
