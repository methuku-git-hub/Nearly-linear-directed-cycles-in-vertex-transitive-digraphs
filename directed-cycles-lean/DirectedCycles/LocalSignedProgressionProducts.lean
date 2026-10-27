module

public import DirectedCycles.LocalSignedProgression
public import DirectedCycles.LocalDivision

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem PowerSegment.power_mem_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N)
    {n : ℕ} (hn : n ≤ N) : p.power n ∈ p.signedProgression L :=
  (p.mem_signedProgression L _).2 ⟨Sum.inl ⟨n,by omega⟩,rfl⟩

theorem PowerSegment.inv_power_mem_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N)
    {n : ℕ} (hn : n ≤ N) : L.inv (p.power n) ∈ p.signedProgression L :=
  p.inv_mem_signedProgression L (p.power_mem_signedProgression L hn)

/-- Multiplying two signed interval elements gives a signed value in the
doubled segment. All cancellation and inverse-product domains are explicit. -/
theorem PowerSegment.signed_product_in_double (hd : L.DivisionClosed) (hr : L.Reversible)
    {u : G} {N : ℕ} (p : L.PowerSegment u N) (d : L.PowerSegment u (2*N))
    (hmatch : ∀ n ≤ N, d.power n = p.power n) {x y z : G}
    (hx : x ∈ p.signedProgression L) (hy : y ∈ p.signedProgression L) (hmul : L.mulRel x y z) :
    ∃ t : ℕ, t ≤ 2*N ∧ (z = d.power t ∨ z = L.inv (d.power t)) := by
  obtain ⟨i,rfl⟩ := (p.mem_signedProgression L x).1 hx
  obtain ⟨j,rfl⟩ := (p.mem_signedProgression L y).1 hy
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change L.mulRel (p.power i.val) (p.power j.val) z at hmul
      have hm := d.add (n := i.val) (m := j.val) (by omega)
      rw [hmatch i.val (by omega),hmatch j.val (by omega)] at hm
      exact ⟨i.val+j.val,by omega,Or.inl (L.unique hmul hm)⟩
    | inr j =>
      change L.mulRel (p.power i.val) (L.inv (p.power (j.val+1))) z at hmul
      by_cases hij : j.val+1 ≤ i.val
      · have hm := d.add (n := i.val-(j.val+1)) (m := j.val+1) (by omega)
        rw [show i.val-(j.val+1)+(j.val+1)=i.val by omega] at hm
        have hh := hd.right hm
        rw [hmatch i.val (by omega),hmatch (j.val+1) (by omega)] at hh
        exact ⟨i.val-(j.val+1),by omega,Or.inl (L.unique hmul hh)⟩
      · have hm := d.add (n := j.val+1-i.val) (m := i.val) (by omega)
        rw [show j.val+1-i.val+i.val=j.val+1 by omega] at hm
        have hh := hr (hd.right hm)
        simp only [L.inv_inv] at hh
        rw [hmatch i.val (by omega),hmatch (j.val+1) (by omega)] at hh
        exact ⟨j.val+1-i.val,by omega,Or.inr (L.unique hmul hh)⟩
  | inr i =>
    cases j with
    | inl j =>
      change L.mulRel (L.inv (p.power (i.val+1))) (p.power j.val) z at hmul
      by_cases hij : i.val+1 ≤ j.val
      · have hm := d.add (n := i.val+1) (m := j.val-(i.val+1)) (by omega)
        rw [show i.val+1+(j.val-(i.val+1))=j.val by omega] at hm
        have hh := hd.left hm
        rw [hmatch (i.val+1) (by omega),hmatch j.val (by omega)] at hh
        exact ⟨j.val-(i.val+1),by omega,Or.inl (L.unique hmul hh)⟩
      · have hm := d.add (n := j.val) (m := i.val+1-j.val) (by omega)
        rw [show j.val+(i.val+1-j.val)=i.val+1 by omega] at hm
        have hh := hr (hd.left hm)
        simp only [L.inv_inv] at hh
        rw [hmatch j.val (by omega),hmatch (i.val+1) (by omega)] at hh
        exact ⟨i.val+1-j.val,by omega,Or.inr (L.unique hmul hh)⟩
    | inr j =>
      change L.mulRel (L.inv (p.power (i.val+1))) (L.inv (p.power (j.val+1))) z at hmul
      have hm := hr (d.add (n := j.val+1) (m := i.val+1) (by omega))
      rw [hmatch (j.val+1) (by omega),hmatch (i.val+1) (by omega)] at hm
      exact ⟨(j.val+1)+(i.val+1),by omega,Or.inr (L.unique hmul hm)⟩
end LocalGroupAlgebra
end DirectedCycles
