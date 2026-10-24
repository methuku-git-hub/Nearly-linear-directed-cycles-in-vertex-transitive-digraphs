import DirectedCycles.ShortPowerProgression

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- First exit and trapping rule out every positive period below twice the
first-exit time. This prevents hidden torsion identifications in the quotient. -/
theorem no_short_period {A : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (u : G) {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A)
    {m : ℕ} (hm : 0 < m) (hmN : m < 2*N) : u^m ≠ 1 := by
  intro he
  have hA : (1 : G) ∈ A := by simpa using hprev 0 hN
  by_cases hsmall : m < N
  · apply hexit
    have hred : u^N = u^(N%m) := by
      calc
        u^N = u^(N%m+m*(N/m)) := by rw [Nat.mod_add_div]
        _ = u^(N%m)*(u^m)^(N/m) := by rw [pow_add,pow_mul]
        _ = u^(N%m) := by simp [he]
    rw [hred]
    exact hprev _ ((Nat.mod_lt N hm).trans hsmall)
  · exact no_short_power_return hi C htrap u hN (by omega) hmN hexit hprev
      (fun j _ => by simpa [he] using hA)

/-- Integer periods give ordinary positive periods through absolute value. -/
theorem natAbs_pow_eq_one_of_zpow_eq_one (u : G) {m : ℤ} (hm : u^m = 1) :
    u^m.natAbs = 1 := by
  obtain ⟨k,rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using hm
  · have h := congrArg Inv.inv hm
    simpa using h

theorem shortPowerProgression_injective {A : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (u : G) {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A) :
    Set.InjOn (fun n : ℤ => u^n) {n | n.natAbs < N} := by
  intro m hm n hn he
  by_contra hne
  have hpos : 0 < (m-n).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt : (m-n).natAbs < 2*N := by
    have h := Int.natAbs_add_le m (-n)
    simp only [Int.natAbs_neg,← sub_eq_add_neg] at h
    change m.natAbs < N at hm
    change n.natAbs < N at hn
    omega
  change u^m = u^n at he
  have hp : u^(m-n) = 1 := by rw [zpow_sub,he]; simp
  exact no_short_period hi C htrap u hN hexit hprev hpos hlt
    (natAbs_pow_eq_one_of_zpow_eq_one u hp)

theorem int_natAbs_lt_iff (n : ℤ) (N : ℕ) : n.natAbs < N ↔ -(N : ℤ) < n ∧ n < (N : ℤ) := by
  constructor
  · intro hn
    apply abs_lt.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  · intro hn
    have h := abs_lt.mpr hn
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h

/-- A finite presentation of the same short progression. -/
noncomputable def shortPowerProgressionFinset (u : G) (N : ℕ) : Finset G := by
  classical
  exact (Finset.Ioo (-(N : ℤ)) (N : ℤ)).image (fun n => u^n)

theorem coe_shortPowerProgressionFinset (u : G) (N : ℕ) :
    (shortPowerProgressionFinset u N : Set G) = shortPowerProgression u N := by
  classical
  ext x
  simp [shortPowerProgressionFinset,shortPowerProgression,int_natAbs_lt_iff]

theorem card_shortPowerProgressionFinset {A : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (u : G) {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A) :
    (shortPowerProgressionFinset u N).card = 2*N-1 := by
  classical
  unfold shortPowerProgressionFinset
  rw [Finset.card_image_iff.mpr ?_,Int.card_Ioo]
  · omega
  · intro m hm n hn he
    apply shortPowerProgression_injective hi C htrap u hN hexit hprev
      ((int_natAbs_lt_iff m N).2 (Finset.mem_Ioo.mp hm))
      ((int_natAbs_lt_iff n N).2 (Finset.mem_Ioo.mp hn)) he
end DirectedCycles
