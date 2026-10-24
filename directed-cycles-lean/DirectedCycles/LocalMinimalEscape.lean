import DirectedCycles.LocalEscapeNSS
import DirectedCycles.LocalConjugates
import DirectedCycles.LocalUltraproductEscape
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Commutation includes existence of both local products and equality of
their values. -/
def Commute (x y : G) : Prop := ∃ z, L.mulRel x y z ∧ L.mulRel y x z

/-- A trivial actual commutator supplies both commuting product domains. -/
theorem commute_of_commutator_eq_one (hr : L.Reversible) {x u : G}
    (hp : L.Product [L.inv x,L.inv u,x,u] L.one) : L.Commute x u := by
  obtain ⟨a,b,ha,hb,hab⟩ := hp.split L (a := [L.inv x,L.inv u]) (b := [x,u]) rfl (by simp) (by simp)
  have he : b = L.inv a := L.right_inverse_unique hab
  have hrev : L.Product [u,x] (L.inv a) := by
    simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_append,
      List.map_cons,List.map_nil,List.cons_append,L.inv_inv] using ha.reverse_inv L hr
  exact ⟨b,(Product.pair_iff L x u b).1 hb,by
    rw [he]
    exact (Product.pair_iff L u x (L.inv a)).1 hrev⟩

/-- An actual minimum on the finite nonidentity subset is positive under
finite local NSS. -/
theorem exists_minimal_escape [Finite G] (hL : L.Cancellative) (A : Finset G)
    (hA : L.one ∈ A) (hNSS : L.IsNSS (A : Set G))
    (hne : ∃ g ∈ A, g ≠ L.one) :
    ∃ u ∈ A, u ≠ L.one ∧ 0 < L.escapeNorm A u ∧
      ∀ v ∈ A, v ≠ L.one → L.escapeNorm A u ≤ L.escapeNorm A v := by
  classical
  have hs : (A.erase L.one).Nonempty := by
    obtain ⟨g,hg,hg1⟩ := hne
    exact ⟨g,Finset.mem_erase.mpr ⟨hg1,hg⟩⟩
  obtain ⟨u,hu,hmin⟩ := (A.erase L.one).exists_min_image (L.escapeNorm (A : Set G)) hs
  have huA := (Finset.mem_erase.mp hu).2
  have hu1 := (Finset.mem_erase.mp hu).1
  refine ⟨u,huA,hu1,?_,?_⟩
  · have h0 := L.escapeNorm_nonneg hA u
    have hn : L.escapeNorm A u ≠ 0 := fun he =>
      hu1 ((L.finite_nss_iff_escapeNorm hL hA).1 hNSS u he)
    exact lt_of_le_of_ne h0 (Ne.symm hn)
  · intro v hv hv1
    exact hmin v (Finset.mem_erase.mpr ⟨hv1,hv⟩)

/-- First exit in a local group records failed membership-or-domain rather
than inventing an undefined power. -/
theorem exists_first_escape {A : Set G} (hA : L.one ∈ A) {u : G}
    (hu : 0 < L.escapeNorm A u) :
    ∃ N : ℕ, 0 < N ∧ ¬ L.PowerIn A u N ∧
      (∀ n < N, L.PowerIn A u n) ∧ L.escapeNorm A u = 1/(N : ℝ) := by
  classical
  have hex : ∃ N : ℕ, ¬ L.PowerIn A u N := by
    by_contra h
    have hall : ∀ n, L.PowerIn A u n := by simpa using h
    have hz := (L.escapeNorm_eq_zero_iff hA u).2 hall
    linarith
  let N := Nat.find hex
  have hbad : ¬ L.PowerIn A u N := Nat.find_spec hex
  have hprev : ∀ n < N, L.PowerIn A u n := by
    intro n hn
    exact not_not.mp (Nat.find_min hex hn)
  have hN : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    exact hbad (hz ▸ (L.powerIn_zero A u).2 hA)
  exact ⟨N,hN,hbad,hprev,L.escapeNorm_eq_inv_of_first_exit hA hbad hprev⟩

/-- A commutator below the least positive escape norm is the identity,
which gives actual local commutation. -/
theorem minimal_escape_commutes (hr : L.Reversible) {A : Set G} (hA : L.one ∈ A)
    {u x k : G} (hu : 0 < L.escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ L.one → L.escapeNorm A u ≤ L.escapeNorm A v)
    (hk : L.Product [L.inv x,L.inv u,x,u] k)
    {D : ℝ} (hbound : L.escapeNorm A k ≤ D*L.escapeNorm A x*L.escapeNorm A u)
    (hsmall : D*L.escapeNorm A x < 1) : L.Commute x u := by
  have hlt : L.escapeNorm A k < L.escapeNorm A u := by nlinarith
  have hkA : k ∈ A := L.mem_of_escapeNorm_lt_one hA (hlt.trans_le (L.escapeNorm_le_one hA u))
  have he : k = L.one := by
    by_contra hn
    exact (not_lt_of_ge (hmin k hkA hn)) hlt
  apply L.commute_of_commutator_eq_one hr
  simpa only [he] using hk
end LocalGroupAlgebra
end DirectedCycles
