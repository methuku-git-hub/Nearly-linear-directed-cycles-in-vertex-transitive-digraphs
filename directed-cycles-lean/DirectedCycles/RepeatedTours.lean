module

public import DirectedCycles.EulerSequence

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Projection to the position inside one tour commutes with cyclic successor. -/
theorem modNat_finRotate {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (i : Fin (k * n)) :
    (finRotate (k * n) i).modNat = finRotate n i.modNat := by
  by_cases hone : n = 1
  · subst n
    exact Subsingleton.elim _ _
  have htwo : 2 ≤ n := by omega
  have hp : 0 < n := hn
  have hkn : 1 < k * n := by nlinarith
  let : NeZero n := ⟨by omega⟩
  let : NeZero (k * n) := ⟨by omega⟩
  apply Fin.ext
  rw [finRotate_apply, finRotate_apply]
  change ((i + 1 : Fin (k * n)).val % n) = (i.modNat + 1 : Fin n).val
  rw [Fin.val_add, Fin.val_add, Fin.val_one', Fin.val_one']
  change ((i.val + 1 % (k * n)) % (k * n)) % n = (i.val % n + 1 % n) % n
  rw [Nat.mod_eq_of_lt hkn, Nat.mod_mod_of_dvd _ (dvd_mul_left n k)]
  exact Nat.add_mod _ _ _

/-- Every position in a tour occurs exactly `k` times in its cyclic repetition,
expressed as the identity for all real-valued weights. -/
theorem sum_modNat {k n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin (k * n), f i.modNat) = (k : ℝ) * ∑ j : Fin n, f j := by
  calc (∑ i : Fin (k * n), f i.modNat) =
      ∑ p : Fin k × Fin n, f (finProdFinEquiv p).modNat :=
        (Equiv.sum_comp finProdFinEquiv (fun i => f i.modNat)).symm
    _ = ∑ p : Fin k × Fin n, f p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      change f ((finProdFinEquiv.symm (finProdFinEquiv p)).2) = f p.2
      rw [Equiv.symm_apply_apply]
    _ = (k : ℝ) * ∑ j : Fin n, f j := by simp [Fintype.sum_prod_type]

/-- Repeated Euler tours in precisely the cyclic form needed for sampling.
The final sum identity proves exact arc multiplicity without choosing labels
for the individual copies of an arc. -/
theorem repeated_regular_euler_sequence {V : Type*} [Fintype V] (D : Digraph V)
    (hD : StronglyConnected D) (d : ℕ) (hdpos : 0 < d) (hq : 0 < Fintype.card V)
    (hout : ∀ v, (Finset.univ.filter (D v)).card = d)
    (hin : ∀ v, (Finset.univ.filter (fun u => D u v)).card = d)
    (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∃ A : Fin N → V, N = k * Fintype.card V * d ∧
      ∃ hA : ∀ i, D (A i) (A (finRotate N i)),
        ∀ f : {e : V × V // D e.1 e.2} → ℝ,
          (∑ i, f ⟨(A i, A (finRotate N i)), hA i⟩) = k * ∑ e, f e := by
  obtain ⟨n, A, hn, hA, hbij⟩ := regular_directed_euler_sequence D hD d hdpos hq hout hin
  have htwo : 0 < n := by rw [hn]; positivity
  let B : Fin (k * n) → V := fun i => A i.modNat
  have hB : ∀ i, D (B i) (B (finRotate (k * n) i)) := by
    intro i
    dsimp only [B]
    rw [modNat_finRotate hk htwo]
    exact hA i.modNat
  let e : Fin n ≃ {e : V × V // D e.1 e.2} := Equiv.ofBijective
    (fun i => ⟨(A i, A (finRotate n i)), hA i⟩) hbij
  refine ⟨k * n, B, by rw [hn, Nat.mul_assoc], hB, ?_⟩
  intro f
  calc (∑ i, f ⟨(B i, B (finRotate (k * n) i)), hB i⟩) =
      ∑ i : Fin (k * n), f (e i.modNat) := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg f
        apply Subtype.ext
        simp only [B, modNat_finRotate hk htwo]
        rfl
    _ = (k : ℝ) * ∑ j : Fin n, f (e j) := sum_modNat (fun j => f (e j))
    _ = (k : ℝ) * ∑ a, f a := by rw [Equiv.sum_comp e f]

end DirectedCycles
