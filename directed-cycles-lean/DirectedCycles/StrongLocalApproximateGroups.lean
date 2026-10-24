import DirectedCycles.LocalFiniteGleasonProduct
import DirectedCycles.LocalConjugates
import DirectedCycles.LocalApproximateOne
import DirectedCycles.LocalNSSApproximateQuotient

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- BGT Definition 7.1 for a finite approximate group in an actual local
ambient group. The long conjugate-word power is explicitly fully defined;
this is the domain content of the local-group containment in (7.1). This
predicate does not assert existence of strong subgroups. -/
structure IsStrongLocalFiniteApproximateGroup (K : ℕ) (A : Finset G) : Prop where
  approximate : IsLocalFiniteApproximateGroup L K A
  trapping : ∃ S : Set G, (∀ s ∈ S, L.inv s ∈ S) ∧
    L.AllProductsDefined (L.conjugates S (L.wordPower (A : Set G) 4)) (1000*K^3) ∧
    L.wordPower (L.conjugates S (L.wordPower (A : Set G) 4)) (1000*K^3) ⊆ A ∧
    (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → L.PowerIn (L.wordPower (A : Set G) 100) x j) → x ∈ A) ∧
    (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000000*K^3 → L.PowerIn (A : Set G) x j) → x ∈ S)

variable [Fintype G]

/-- The local product estimate is derived from the strong-group predicate,
including every translation domain and both actual bump constructions. -/
theorem strong_local_regularized (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A) (hK : 2 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ g, L.escapeNorm A g ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*L.restrictedEscapeDistance A ε g := by
  obtain ⟨S,hSi,hQdom,hsmall,hfirst,hsecond⟩ := hA.trapping
  let Q := L.conjugates S (L.wordPower (A : Set G) 4)
  have hS1 : L.one ∈ S := hsecond L.one
    (fun j _ _ => ⟨L.one,hA.approximate.one_mem,L.product_replicate_one j⟩)
  have hA4 : L.one ∈ L.wordPower (A : Set G) 4 :=
    ⟨List.replicate 4 L.one,List.length_replicate,by
      intro x hx
      exact (List.mem_replicate.mp hx).2.symm ▸ hA.approximate.one_mem,L.product_replicate_one 4⟩
  have hSQ : S ⊆ Q := L.subset_conjugates hA4
  have hQ1 : L.one ∈ Q := hSQ hS1
  have hK0 : 0 < K := by omega
  have hN : 0 < 1000*K^3 := by positivity
  have hQA : Q ⊆ A := by
    simpa only [L.wordPower_one] using
      L.wordPower_subset_of_maximum hQ1 hQdom hsmall 1 hN
  have hSA : S ⊆ A := hSQ.trans hQA
  have hsub : ∀ {m n : ℕ}, m ≤ n → n ≤ 200 →
      L.wordPower (A : Set G) m ⊆ L.wordPower (A : Set G) n :=
    fun {_ _} hmn hn => L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts hmn hn
  have hfirst4 : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A := by
    intro x hx
    apply hfirst
    intro j hj hj'
    obtain ⟨y,hy,hp⟩ := hx j hj hj'
    exact ⟨y,hsub (by omega : 4 ≤ 100) (by omega) hy,hp⟩
  have hconj : ∀ h ∈ S, ∀ y ∈ L.wordPower (A : Set G) 3,
      ∃ c ∈ Q, L.Product [L.inv y,h,y] c := by
    intro h hh y hy
    have hRdom := hA.approximate.allProducts.wordPower L (by omega : 4*3 ≤ 200)
    have hy4 := hsub (by omega : 3 ≤ 4) (by omega) hy
    have hyi := L.inv_mem_wordPower hr hA.approximate.inv_mem hy4
    have hh4 : h ∈ L.wordPower (A : Set G) 4 := by
      apply hsub (by omega : 1 ≤ 4) (by omega)
      rw [L.wordPower_one]
      exact hSA hh
    obtain ⟨c,hpc⟩ := hRdom [L.inv y,h,y] (by simp) (by aesop)
    exact ⟨c,⟨h,hh,y,hy4,hpc⟩,hpc⟩
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hconst : 2*(1000 : ℝ)*(K : ℝ)^2 ≤ ((1000*K^3 : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (K : ℝ),mul_nonneg (sq_nonneg (K : ℝ)) (sub_nonneg.mpr hKr)]
  exact L.finite_gleason_regularized hd hr A hA.approximate S Q hSA hQ1
    (fun _ hx => L.inv_mem_conjugates hr hSi hx) 1000 (1000000*K^3) (1000*K^3)
    (by omega) (by positivity) (by positivity) hfirst4 hsecond hconj hQdom hsmall hconst hε

/-- All finite local strong approximate groups satisfy the product estimate,
including K = 1, where the actual subgroup structure yields the sharper
constant one. -/
theorem strong_local_approximate_product (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {l : List G} {x : G} (hp : L.Product l x) :
    L.escapeNorm A x ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (L.escapeNorm A)).sum := by
  by_cases hK : 2 ≤ K
  · apply L.escape_word_bound_of_restricted_regularized hA.approximate.one_mem (by positivity) _ hp
    intro ε hε
    exact strong_local_regularized L hd hr hA hK hε
  · have hK1 : K = 1 := by have := hA.approximate.one_le; omega
    subst K
    have hbase := (local_one_approximate_isGlobalSubgroup hA.approximate).escapeNorm_product_le hp
    have hsum : 0 ≤ (l.map (L.escapeNorm A)).sum := List.sum_nonneg (by
      intro r hr
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hr
      exact L.escapeNorm_nonneg hA.approximate.one_mem g)
    norm_num only [one_pow,mul_one,Nat.cast_one,Nat.cast_ofNat]
    linarith

/-- In a finite local ambient group the previously explicit analytic premise
for the NSS quotient is now discharged by the actual strong-group property. -/
theorem strong_local_nss_approximate_quotient
    (hd : L.DivisionClosed) (hr : L.Reversible) {A B : Finset G} {K J : ℕ}
    (hA : IsStrongLocalFiniteApproximateGroup L K A)
    (hB : IsLocalFiniteApproximateGroup L J B)
    (hsmall : L.wordPower (B : Set G) 200 ⊆ (A : Set G)) :
    let H := {x | L.escapeNorm A x = 0}
    ∃ W : L.NormalSubgroupWindow H (L.setMul H A),
      IsLocalFiniteApproximateGroup (W.congruence hd hr).algebra J (W.finiteImage hd hr B) ∧
      (W.congruence hd hr).algebra.IsNSS Set.univ ∧
      (W.congruence hd hr).algebra.DivisionClosed ∧
      (W.congruence hd hr).algebra.Reversible ∧
      B.card ≤ (W.finiteImage hd hr B).card * (localZeroEscapeFinset L A).card := by
  obtain ⟨S,_,_,_,hfirst,_⟩ := hA.trapping
  apply local_nss_approximate_quotient L hd hr hA.approximate.one_mem hA.approximate.inv_mem
    hA.approximate.allProducts (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) _ hfirst hB hsmall
  intro x _ y _ z hm
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
    strong_local_approximate_product L hd hr hA ((LocalGroupAlgebra.Product.pair_iff L _ _ _).2 hm)
end DirectedCycles
