import DirectedCycles.NormGrowthNSS
import DirectedCycles.LocalGlobalSubgroup

set_option autoImplicit false
namespace DirectedCycles.LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Expanding actual local squares exclude every complete power sequence in
an appropriately bounded window. No ambient global group is assumed. -/
theorem powerSequence_trivial_of_doubling_growth (V : Set G) (size : G → ℝ) (c R : ℝ)
    (hc : 1 < c) (hsize : ∀ x ∈ V, 0 ≤ size x)
    (hzero : ∀ x ∈ V, size x = 0 → x = L.one)
    (hbound : ∀ x ∈ V, size x ≤ R)
    (hgrowth : ∀ x ∈ V, ∀ y ∈ V, L.mulRel x x y → c*size x ≤ size y) :
    ∀ x : G, ∀ p : L.PowerSequence x, (∀ n, p.power n ∈ V) → x = L.one := by
  intro x p hp
  have hxV : x ∈ V := p.one ▸ hp 1
  apply hzero x hxV
  apply le_antisymm _ (hsize x hxV)
  by_contra hn
  have hs : 0 < size x := lt_of_not_ge hn
  have hlower : ∀ n : ℕ, c^n*size x ≤ size (p.power (2^n)) := by
    intro n
    induction n with
    | zero => simp only [pow_zero,p.one,_root_.one_mul,le_refl]
    | succ n ih =>
      have he : 2^(n+1) = 2^n+2^n := by omega
      rw [he,pow_succ]
      calc
        c^n*c*size x = c*(c^n*size x) := by ring
        _ ≤ c*size (p.power (2^n)) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ size (p.power (2^n+2^n)) := hgrowth _ (hp _) _ (hp _) (p.add _ _)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (R/size x) hc
  have hgt : R < c^n*size x := (div_lt_iff₀ hs).mp hn
  exact (not_lt_of_ge ((hlower n).trans (hbound _ (hp _)))) hgt

/-- The same local expansion excludes actual total subgroups in the window. -/
theorem nss_of_doubling_growth (V : Set G) (size : G → ℝ) (c R : ℝ)
    (hc : 1 < c) (hsize : ∀ x ∈ V, 0 ≤ size x)
    (hzero : ∀ x ∈ V, size x = 0 → x = L.one)
    (hbound : ∀ x ∈ V, size x ≤ R)
    (hgrowth : ∀ x ∈ V, ∀ y ∈ V, L.mulRel x x y → c*size x ≤ size y) : L.IsNSS V := by
  intro S hS hSV x hx
  let := hS.toGroup
  let xS : S := ⟨x,hx⟩
  let p : L.PowerSequence x := {
    power := fun n => ((xS^n : S) : G)
    product := by
      intro n
      have hp := (ofGroup_product S (List.replicate n xS)).map hS.inclusionHom
      simpa [IsGlobalSubgroup.inclusionHom,xS] using hp }
  exact L.powerSequence_trivial_of_doubling_growth V size c R hc hsize hzero hbound hgrowth
    x p (fun n => hSV (xS^n).property)
end DirectedCycles.LocalGroupAlgebra
