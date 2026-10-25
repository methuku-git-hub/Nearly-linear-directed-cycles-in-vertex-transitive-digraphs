module

public import DirectedCycles.LocalFiniteDefect
public import DirectedCycles.LocalTranslateEnergy
public import DirectedCycles.LocalSmallCostProducts
public import DirectedCycles.LocalProductCompression
public import DirectedCycles.LocalWordPowerMonotonicity

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- Small-defect words have every bracketing defined and remain in A^4.
The length can be arbitrarily large: it is controlled by the total defect,
not by an assumed large ambient multiplication domain. -/
theorem almost_period_product (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsLocalFiniteApproximateGroup L K A)
    (D : Finset G) (hD : (D : Set G) ⊆ L.wordPower (A : Set G) 2)
    (l : List G) (hsmall : (l.map (fun g => (L.defect D g : ℝ))).sum < D.card) :
    ∃ x ∈ L.wordPower (A : Set G) 4, L.Product l x ∧
      (L.defect D x : ℝ) ≤ (l.map (fun g => (L.defect D g : ℝ))).sum := by
  let R := L.wordPower (A : Set G) 4
  have hc := hd.cancellative L hr
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by norm_num)
  have hDR : (D : Set G) ⊆ R := hD.trans
    (L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by norm_num : 2 ≤ 4) (by norm_num))
  have h1R : L.one ∈ R := by
    have hh := L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by norm_num : 1 ≤ 4) (by norm_num)
    exact hh (by rw [L.wordPower_one]; exact hA.one_mem)
  apply L.small_cost_product_exists h1R (fun a ha b hb => ?_)
    (fun g => (L.defect D g : ℝ)) (fun g => Nat.cast_nonneg _) (by simp only [L.defect_one,Nat.cast_zero])
    (fun a ha b hb c hm => ?_) (fun g hg => ?_) l hsmall
  · obtain ⟨x,hx⟩ := hRdom [a,b] (by simp) (by aesop)
    exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
  · exact_mod_cast L.defect_mul_le hc hRdom D hDR ha hb hm
  · have hg' : L.defect D g < D.card := by exact_mod_cast hg
    obtain ⟨a,⟨b,hb,rfl⟩,c,hcD,hm⟩ := L.mem_difference_of_defect_lt hd D g hg'
    rw [show R = L.setMul (L.wordPower (A : Set G) 2) (L.wordPower (A : Set G) 2) by
      dsimp only [R]
      rw [show 4 = 2+2 from rfl,L.wordPower_add hA.allProducts (by norm_num)]]
    exact ⟨L.inv b,L.inv_mem_wordPower hr hA.inv_mem (hD hb),c,hD hcD,hm⟩

/-- A uniform per-letter defect bound gives actual long-product domains and
power containment, simultaneously. -/
theorem almost_period_domains (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsLocalFiniteApproximateGroup L K A)
    (D : Finset G) (hD0 : 0 < D.card) (hD : (D : Set G) ⊆ L.wordPower (A : Set G) 2)
    (S : Set G) (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (hN : (N : ℝ)*ε < 1)
    (hS : ∀ g ∈ S, (L.defect D g : ℝ) ≤ ε*D.card) :
    L.AllProductsDefined S N ∧ ∀ n ≤ N, L.wordPower S n ⊆ L.wordPower (A : Set G) 4 := by
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hD0
  have hword : ∀ l : List G, l.length ≤ N → (∀ g ∈ l, g ∈ S) →
      ∃ x ∈ L.wordPower (A : Set G) 4, L.Product l x := by
    intro l hlen hl
    have hsum : (l.map (fun g => (L.defect D g : ℝ))).sum ≤ (l.length : ℝ)*(ε*D.card) := by
      have hgeneral : ∀ q : List G, (∀ g ∈ q, g ∈ S) →
          (q.map (fun g => (L.defect D g : ℝ))).sum ≤ (q.length : ℝ)*(ε*D.card) := by
        intro q hq
        induction q with
        | nil => simp
        | cons g q ih =>
          have hq' := ih (fun a ha => hq a (List.mem_cons_of_mem g ha))
          have hg' := hS g (hq g (by simp))
          simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
          nlinarith
      exact hgeneral l hl
    have hlen' : (l.length : ℝ) ≤ N := by exact_mod_cast hlen
    have hlenε : (l.length : ℝ)*ε < 1 := (mul_le_mul_of_nonneg_right hlen' hε).trans_lt hN
    have hsmall : (l.map (fun g => (L.defect D g : ℝ))).sum < D.card := by
      have hmul := mul_lt_mul_of_pos_right hlenε hDpos
      nlinarith
    obtain ⟨x,hx,hp,_⟩ := L.almost_period_product hd hr hA D hD l hsmall
    exact ⟨x,hx,hp⟩
  constructor
  · intro l hl hm
    obtain ⟨x,_,hp⟩ := hword l hl hm
    exact ⟨x,hp⟩
  · rintro n hn x ⟨l,hlen,hl,hp⟩
    obtain ⟨y,hy,hq⟩ := hword l (hlen ▸ hn) hl
    exact (hq.unique L hp) ▸ hy
end LocalGroupAlgebra
end DirectedCycles
