module

public import DirectedCycles.SchreierBallGrowth
public import Mathlib.Algebra.Group.Subgroup.Pointwise

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A generating set has a representative for every coset in its first
index-minus-one powers. -/
theorem finite_short_coset_representatives {G : Type*} [Group G] [Finite G]
    (S : Set G) (h1 : 1 ∈ S) (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) :
    ∀ q : G ⧸ H, ∃ g ∈ S^(H.index-1), Quotient.mk'' g = q := by
  let A := (Quotient.mk'' : G → G ⧸ H) '' (S^(H.index-1))
  have hb := finite_coset_growth S h1 hgen H H.index le_rfl
  have hall : A = Set.univ := by
    by_contra hn
    have hh := Set.ncard_lt_card hn
    exact (not_lt_of_ge hb) hh
  intro q
  have hq : q ∈ A := hall ▸ Set.mem_univ q
  exact hq

/-- Products of subgroups normal inside a common containing subgroup
have bounded word length, one bounded factor per subgroup. -/
theorem finite_normal_sup_power_bound {G ι : Type*} [Group G] [Fintype ι]
    (S : Set G) (N : Subgroup G) (H : ι → Subgroup G) (r : ℕ)
    (hHN : ∀ i, H i ≤ N) (hnorm : ∀ i, N ≤ Subgroup.normalizer (H i))
    (hbound : ∀ i, (H i : Set G) ⊆ S^r) :
    ((⨆ i, H i : Subgroup G) : Set G) ⊆ S^(Fintype.card ι*r) := by
  classical
  have h : ∀ T : Finset ι, ((T.sup H : Subgroup G) : Set G) ⊆ S^(T.card*r) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro g hg
      have he : g = 1 := hg
      subst g
      simp
    | @insert i T hi ih =>
      have hTN : T.sup H ≤ N := Finset.sup_le (fun j _ => hHN j)
      rw [Finset.sup_insert,Finset.card_insert_of_notMem hi]
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (H i) (T.sup H) (hTN.trans (hnorm i))]
      rintro g ⟨a,ha,b,hb,rfl⟩
      have hh := Set.mul_mem_mul (hbound i ha) (ih hb)
      rw [← pow_add] at hh
      convert hh using 1
      congr 1
      ring
  have he : Finset.univ.sup H = ⨆ i, H i := by
    apply le_antisymm
    · exact Finset.sup_le (fun i _ => le_iSup H i)
    · exact iSup_le (fun i => Finset.le_sup (Finset.mem_univ i))
  simpa only [he,Finset.card_univ] using h Finset.univ

end DirectedCycles
