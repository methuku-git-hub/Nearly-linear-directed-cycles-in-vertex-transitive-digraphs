module

public import DirectedCycles.LocalTranslateEnergy
public import DirectedCycles.LocalFiniteDefect
public import DirectedCycles.LocalProductCompression
public import DirectedCycles.LocalWordPowerMonotonicity

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem mul_inter_translate_subset [DecidableEq G] {R : Set G}
    (hdom : L.AllProductsDefined R 3) (A B : Finset G) (g : G)
    (hAR : (A : Set G) ⊆ R) (hBR : (B : Set G) ⊆ R) (hg : g ∈ R) :
    L.finsetMul A (B ∩ L.rightTranslate B g) ⊆
      L.finsetMul A B ∩ L.rightTranslate (L.finsetMul A B) g := by
  classical
  intro x hx
  obtain ⟨a,ha,b,hb,hm⟩ := (L.mem_finsetMul _ _ x).1 hx
  obtain ⟨hbB,hbg⟩ := Finset.mem_inter.mp hb
  refine Finset.mem_inter.mpr ⟨(L.mem_finsetMul A B x).2 ⟨a,ha,b,hbB,hm⟩,?_⟩
  obtain ⟨c,hc,hcg⟩ := (L.mem_rightTranslate B g b).1 hbg
  obtain ⟨ac,hac⟩ := hdom [a,c] (by simp) (by aesop)
  have ham := (Product.pair_iff L _ _ _).1 hac
  obtain ⟨z,hzg,haz⟩ := hdom.triple L (hAR ha) (hBR hc) hg ham hcg
  have he : z = x := L.unique haz hm
  exact (L.mem_rightTranslate _ _ x).2 ⟨ac,(L.mem_finsetMul A B ac).2 ⟨a,ha,c,hc,ham⟩,he ▸ hzg⟩

/-- Overlap is transported by an actual inverse translation. All associativity
and inverse-translation domains are explicit. -/
theorem overlap_right_period [DecidableEq G] (hd : L.DivisionClosed) (hr : L.Reversible)
    {R : Set G} (hdom : L.AllProductsDefined R 3) (B : Finset G) (hBR : (B : Set G) ⊆ R)
    {a a₀ u : G} (ha : a ∈ R) (ha₀ : a₀ ∈ R) (ha₀i : L.inv a₀ ∈ R)
    (hu : L.mulRel a (L.inv a₀) u) :
    (L.rightTranslate B a₀ ∩ L.rightTranslate B a).card =
      (B ∩ L.rightTranslate B u).card := by
  classical
  have hc := hd.cancellative L hr
  have hBa : ∀ b ∈ B, L.Defined b a₀ := by
    intro b hb
    obtain ⟨x,hx⟩ := hdom [b,a₀] (by simp) (by aesop)
    exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
  have hdomi : ∀ b ∈ L.rightTranslate B a₀ ∩ L.rightTranslate B a, L.Defined b (L.inv a₀) := by
    intro b hb
    obtain ⟨c,hcB,hcm⟩ := (L.mem_rightTranslate B a₀ b).1 (Finset.mem_inter.mp hb).1
    exact ⟨c,hd.right hcm⟩
  rw [← L.card_rightTranslate hc _ (L.inv a₀) hdomi,L.rightTranslate_inter hc,
    L.rightTranslate_inv hd B a₀ hBa,L.rightTranslate_mul hdom B hBR ha ha₀i hu]

/-- Dense local almost periods from overlap energy and a minimizing set. -/
theorem dense_almost_periods (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} (A B : Finset G) (ε t δ : ℝ)
    (hA : IsLocalFiniteApproximateGroup L K A) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hBA : B ⊆ A) (hB : t*A.card ≤ B.card)
    (hscale : 2*δ*(K : ℝ) ≤ t^2)
    (hmin : ∀ C : Finset G, C ⊆ A → δ*A.card ≤ C.card →
      (1-ε)*(L.finsetMul A B).card ≤ (L.finsetMul A C).card) :
    ∃ S : Finset G, L.one ∈ S ∧ (∀ g ∈ S, L.inv g ∈ S) ∧
      (S : Set G) ⊆ L.wordPower (A : Set G) 2 ∧ δ*A.card ≤ S.card ∧
      ∀ g ∈ S, (L.defect (L.finsetMul A B) g : ℝ) ≤ ε*(L.finsetMul A B).card := by
  classical
  have hc := hd.cancellative L hr
  let R := L.wordPower (A : Set G) 2
  have hAR : (A : Set G) ⊆ R := by
    simpa only [L.wordPower_one] using
      L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by omega : 1 ≤ 2) (by omega : 2 ≤ 200)
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by norm_num)
  have hA2i : ∀ a ∈ R, L.inv a ∈ R := fun a ha => L.inv_mem_wordPower hr hA.inv_mem ha
  have hABR : (L.finsetMul A B : Set G) ⊆ R := by
    intro x hx
    obtain ⟨a,ha,b,hb,hm⟩ := (L.mem_finsetMul A B x).1 hx
    rw [show R = L.setMul (A : Set G) (A : Set G) by
      dsimp only [R]
      rw [show 2 = 1+1 from rfl,L.wordPower_add hA.allProducts (by norm_num),L.wordPower_one]]
    exact ⟨a,ha,b,hBA hb,hm⟩
  obtain ⟨a₀,ha₀,hCcard⟩ := L.many_overlapping_right_translates hc hA t δ ht hδ hBA hB hscale
  have ha₀i := hA.inv_mem a₀ ha₀
  let C := {a ∈ A | δ*A.card ≤ ((L.rightTranslate B a₀ ∩ L.rightTranslate B a).card : ℝ)}
  let S := {g ∈ R.toFinset | (L.defect (L.finsetMul A B) g : ℝ) ≤ ε*(L.finsetMul A B).card}
  have hmul : ∀ a ∈ A, L.Defined a (L.inv a₀) := by
    intro a ha
    obtain ⟨x,hx⟩ := hA.allProducts [a,L.inv a₀] (by simp) (by aesop)
    exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
  let p : G → G := fun a => if ha : a ∈ A then L.mul a (L.inv a₀) (hmul a ha) else L.one
  have hp : ∀ a ∈ A, L.mulRel a (L.inv a₀) (p a) := by
    intro a ha
    dsimp only [p]
    rw [dite_eq_left ha]
    exact L.mul_spec _ _ _
  have hCS : Set.MapsTo p (C : Set G) (S : Set G) := by
    intro a ha
    obtain ⟨haA,haC⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    constructor
    · apply Set.mem_toFinset.mpr
      exact ⟨[a,L.inv a₀],rfl,by aesop,(Product.pair_iff L _ _ _).2 (hp a haA)⟩
    · let D := B ∩ L.rightTranslate B (p a)
      have hDA : D ⊆ A := Finset.inter_subset_left.trans hBA
      have hDcard : δ*A.card ≤ (D.card : ℝ) := by
        rw [L.overlap_right_period hd hr hRdom B (fun b hb => hAR (hBA hb))
          (hAR haA) (hAR ha₀) (hAR (hA.inv_mem a₀ ha₀)) (hp a haA)] at haC
        exact haC
      have hl := hmin D hDA hDcard
      have hu : ((L.finsetMul A D).card : ℝ) ≤
          (L.finsetMul A B ∩ L.rightTranslate (L.finsetMul A B) (p a)).card := by
        have hpaR : p a ∈ R := ⟨[a,L.inv a₀],rfl,by aesop,(Product.pair_iff L _ _ _).2 (hp a haA)⟩
        exact_mod_cast Finset.card_le_card
          (L.mul_inter_translate_subset hRdom A B (p a) hAR (fun b hb => hAR (hBA hb)) hpaR)
      have he : (L.defect (L.finsetMul A B) (p a) : ℝ)+
          (L.finsetMul A B ∩ L.rightTranslate (L.finsetMul A B) (p a)).card = (L.finsetMul A B).card := by
        exact_mod_cast L.defect_add_overlap (L.finsetMul A B) (p a)
      nlinarith
  refine ⟨S,?_,?_,?_,?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Set.mem_toFinset.mpr (hAR hA.one_mem),?_⟩
    simpa only [L.defect_one,Nat.cast_zero] using mul_nonneg hε (Nat.cast_nonneg (L.finsetMul A B).card)
  · intro g hg
    obtain ⟨hgR,hgε⟩ := Finset.mem_filter.mp hg
    have hgR' : g ∈ R := Set.mem_toFinset.mp hgR
    refine Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr (hA2i g hgR'),?_⟩
    have hdef : ∀ g ∈ R, ∀ b ∈ L.finsetMul A B, L.Defined b g := by
      intro v hv b hb
      obtain ⟨x,hx⟩ := hRdom [b,v] (by simp) (by aesop)
      exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
    rw [L.defect_inv hd hr _ g (hdef g hgR') (hdef (L.inv g) (hA2i g hgR'))]
    exact hgε
  · exact fun g hg => Set.mem_toFinset.mp (Finset.mem_filter.mp hg).1
  · have hh : C.card ≤ S.card := Finset.card_le_card_of_injOn p hCS (by
      intro a ha b hb he
      have hm := hp a (Finset.mem_filter.mp ha).1
      rw [he] at hm
      exact hc.right_cancel hm (hp b (Finset.mem_filter.mp hb).1))
    exact hCcard.trans (by exact_mod_cast hh)
  · exact fun g hg => (Finset.mem_filter.mp hg).2
end LocalGroupAlgebra
end DirectedCycles
