module

public import DirectedCycles.FiniteStructure
public import DirectedCycles.BoundedStabilizerCycles
public import DirectedCycles.LargeOrbits
public import DirectedCycles.SmallOrbitArithmetic
public import DirectedCycles.EpsilonReduction
public import DirectedCycles.Thresholds

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The complete main-theorem deduction from the finite structural input.
The input remains an explicit premise until that external dependency is
proved; this theorem is deliberately not named `theorem_1_5`. -/
theorem main_of_finite_structure (hstructure : FiniteStructuralInput) : MainTheorem := by
  classical
  apply main_of_small_errors
  intro eps heps heps1
  let lam := eps/10
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hlam1 : lam < 1 := by dsimp only [lam]; linarith
  have halpha : 0 < 1-4*lam := by dsimp only [lam]; linarith
  obtain ⟨B,r,c,I,Ns,hB,hstruct⟩ := hstructure lam hlam hlam1
  obtain ⟨Nb,hbig⟩ := large_normal_orbits hlam B hB
  obtain ⟨b,hb,Ny,hsmall⟩ := bounded_stabilizer_cycle_bound.{0} B r c I hB (eps/3)
    (by positivity) (by linarith)
  obtain ⟨Nt,ht⟩ := main_thresholds heps hb
  obtain ⟨Nq,hqthreshold⟩ := eventually_constant_mul_power_le halpha
    (show (0 : ℝ) < (max Ny 1 : ℕ) by exact_mod_cast (by omega : 0 < max Ny 1))
  refine ⟨max Ns (max Nb (max Nt (max Nq 2))),?_⟩
  intro n hn X hloop hconn htrans
  have hnNs : Ns ≤ n := (le_max_left _ _).trans hn
  have hnNb : Nb ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnNt : Nt ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnNq : Nq ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hn2 : 2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let G := automorphismGroup X
  let : Fintype G := Fintype.ofFinite G
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hX := automorphismGroup_invariant X
  have hXtrans := automorphismGroup_transitive X htrans
  obtain ⟨H,hH,hdiam,hquot⟩ := hstruct n hnNs X hloop hconn htrans
  let : H.Normal := hH
  let Ω := Quotient (MulAction.orbitRel H (Fin n))
  let : Fintype Ω := Fintype.ofFinite Ω
  let : MulAction G Ω := normalOrbitAction H
  let pi : Fin n → Ω := Quotient.mk''
  have hpi : ∀ (g : G) x, pi (g • x) = g • pi x := fun _ _ => rfl
  have htΩ := equivariant_quotient_transitive pi Quotient.mk''_surjective hpi hXtrans
  let q₀ : Ω := pi ⟨0,by omega⟩
  let m := Fintype.card {x : Fin n // pi x = q₀}
  have hm : ∀ q : Ω, Fintype.card {x : Fin n // pi x = q} = m :=
    fun q => equivariant_equal_fibre_cards pi hpi htΩ q q₀
  have hcard : n = Fintype.card Ω*m := by
    simpa only [Fintype.card_fin] using card_eq_quotient_mul_fibre pi m hm
  obtain ⟨hstab,N,hN,hNil,hr,hc,hI⟩ := hquot
  by_cases hmb : (n : ℝ)^(4*lam) ≤ m
  · obtain ⟨C,hC⟩ := hbig G (Fin n) H X hconn hX hXtrans
      (by simpa only [Fintype.card_fin] using hnNb) m hm
      (by simpa only [Fintype.card_fin] using hmb)
      (by simpa only [Fintype.card_fin] using hdiam)
      (by simpa only [Nat.card_eq_fintype_card] using hstab)
    refine ⟨C,((ht n hnNt).1).trans ?_⟩
    simpa only [Fintype.card_fin,lam] using hC
  · have hqpos : (0 : ℝ) < Fintype.card Ω := by
      have hcpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨q₀⟩
      exact_mod_cast hcpos
    have hq : (n : ℝ)^(1-4*lam) < Fintype.card Ω :=
      small_fibre_quotient_bound n (Fintype.card Ω) m (4*lam) hnpos hqpos
        (by exact_mod_cast hcard) (lt_of_not_ge hmb)
    have hNy : Ny ≤ Nat.card Ω := by
      have hh := hqthreshold n hnNq
      simp only [Real.rpow_zero,mul_one] at hh
      have hNy' : (Ny : ℝ) ≤ Fintype.card Ω :=
        (show (Ny : ℝ) ≤ (max Ny 1 : ℕ) by exact_mod_cast (le_max_left Ny 1)).trans (hh.trans hq.le)
      simpa only [Nat.card_eq_fintype_card] using (show Ny ≤ Fintype.card Ω by exact_mod_cast hNy')
    let K := PermutationImage G Ω
    let : Fintype K := Fintype.ofFinite K
    let : N.Normal := hN
    let : Group.IsNilpotent N := hNil
    let Z := QuotientDigraph X pi
    have hZinv : ∀ g : G, ∀ x y, Z (g • x) (g • y) ↔ Z x y :=
      equivariant_quotient_invariant X pi hX hpi
    have hZsc : StronglyConnected Z := quotient_stronglyConnected X pi Quotient.mk''_surjective
      ((vertexTransitive_connected_iff_stronglyConnected htrans).mp hconn)
    obtain ⟨C,hC⟩ := hsmall K Ω Z (induced_action_invariant Z hZinv)
      (induced_action_transitive htΩ) hZsc N hN hNil hr hc hI hstab hNy
    obtain ⟨L,hL⟩ := normal_orbit_cycle_lift X hX hXtrans H C
    refine ⟨L,((ht n hnNt).2).trans ?_⟩
    have hpower := small_quotient_cycle_power b n (Nat.card Ω) (eps/3) lam C.length hb.le hnpos.le
      (by linarith) (by simpa only [Nat.card_eq_fintype_card] using hq.le) hC
    exact hpower.trans (by exact_mod_cast hL)

end DirectedCycles
