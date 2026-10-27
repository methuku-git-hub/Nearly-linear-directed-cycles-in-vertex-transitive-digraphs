module

public import DirectedCycles.CyclicExperiment
public import DirectedCycles.InvariantLoads
public import DirectedCycles.PathSamplingCore
public import DirectedCycles.RepeatedTours
public import DirectedCycles.SamplingArithmetic
public import DirectedCycles.WeakComponents

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

theorem positive_regular_degree {W : Type*} [Fintype W] (Q : Digraph W)
    (hQ : StronglyConnected Q) (hq : 2 ≤ Fintype.card W) (d : ℕ)
    (hd : ∀ a, (Finset.univ.filter (Q a)).card = d) : 0 < d := by
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card W)
  have hp : ({a} : Finset W) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  obtain ⟨x, _, y, _, hxy⟩ := stronglyConnected_arc_leaving Q hQ {a} (by simp) hp
  rw [← hd x]
  exact Finset.card_pos.mpr ⟨y, by simp [hxy]⟩

set_option maxHeartbeats 1200000 in
/-- Lemma 4.5 for an equivariant uniform partition. Every random path, its
marginal law, independence, collision estimate, and load estimate is constructed
inside the proof; no probabilistic conclusion is an additional premise. -/
theorem joining_short_connections_on_partition {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [Fintype W] [DecidableEq W] [MulAction G V] [MulAction G W]
    (D : Digraph V) (Q : Digraph W) (π : V → W) (hs : Function.Surjective π)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hstrong : StronglyConnected Q) (hq : 0 < Fintype.card W) (m d t : ℕ) (hd : 0 < d)
    (hm : ∀ a, Fintype.card {x // π x = a} = m)
    (hout : ∀ a, (Finset.univ.filter (Q a)).card = d)
    (hin : ∀ b, (Finset.univ.filter (fun a => Q a b)).card = d)
    (hshort : ∀ a b, Q a b → ∀ x : {x // π x = a}, ∀ y : {y // π y = b},
      ∃ P : SimplePath D x.val y.val, P.length ≤ t)
    (hlarge : 192 * d * (t + 1) ^ 2 ≤ m) :
    ∃ C : Cycle D, (Fintype.card V : ℝ) / (96 * (t + 1 : ℝ) ^ 2) ≤ C.length := by
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity : 0 < 192 * d * (t + 1) ^ 2) hlarge
  let k := m / (48 * d * (t + 1) ^ 2)
  obtain ⟨hk, hN4, hNlen, hcoef⟩ := sampling_arithmetic (Fintype.card W) m d t hq hd hlarge
  change 4 ≤ k at hk
  have hkpos : 0 < k := by omega
  obtain ⟨N, A, hN, hA, hmult⟩ := repeated_regular_euler_sequence Q hstrong d hd hq hout hin k hkpos
  have hn : 4 ≤ N := by rw [hN]; exact hN4
  have hbase : ∀ x y, Q (π x) (π y) → ∃ P : SimplePath D x y, P.length ≤ t := by
    intro x y hxy
    exact hshort (π x) (π y) hxy ⟨x, rfl⟩ ⟨y, rfl⟩
  choose base hb using hbase
  let β := EndpointSeed (G := G) π A
  let : ∀ j, Nonempty (β j) := fun j =>
    let ⟨x, hx⟩ := hs (A j)
    ⟨(⟨x, hx⟩, 1)⟩
  let P := cyclicSampledPath Q π hQ hπ base A hA
  let L : ℝ := (k : ℝ) * d * (t + 1 : ℝ) / m
  let T : ℝ := (t : ℝ) + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlen : ∀ i ω, ((P i ω).length : ℝ) ≤ T := by
    intro i ω
    dsimp only [P, T]
    exact_mod_cast cyclicSampledPath_length Q π hQ hπ base t hb A hA i ω
  have hload : ∀ v, (∑ i, uniformProbability (fun ω => v ∈ P i ω)) ≤ L := by
    intro v
    have he : (∑ i, uniformProbability (fun ω => v ∈ P i ω)) =
        (k : ℝ) * ∑ e : {p : W × W // Q p.1 p.2},
          orbitRouteLoad Q π hQ hπ base e.val.1 e.val.2 e.property v := by
      calc (∑ i, uniformProbability (fun ω => v ∈ P i ω)) =
          ∑ i, orbitRouteLoad Q π hQ hπ base (A i) (A (finRotate N i)) (hA i) v := by
            apply Finset.sum_congr rfl
            intro i _
            exact cyclicSampledPath_marginal Q π hs hQ hπ base hn A hA i v
        _ = _ := hmult (fun e => orbitRouteLoad Q π hQ hπ base e.val.1 e.val.2 e.property v)
    rw [he]
    have hl := mul_le_mul_of_nonneg_left
      (orbitRouteLoad_global Q π hs hQ hπ ht base t d m hb hout hm hmpos v) (Nat.cast_nonneg k)
    simpa only [L, mul_div_assoc, mul_assoc] using hl
  have hLT : L * T ≤ 1 / 48 := by
    have he : L * T = (k : ℝ) * d * (t + 1 : ℝ) ^ 2 / m := by dsimp [L, T]; ring
    rw [he]
    exact hcoef
  obtain ⟨C, hC⟩ := cyclic_path_sampling D N hn β P
    (cyclicSampledPath_depends Q π hQ hπ base A hA)
    (cyclicSampledPath_loop hD Q π hQ hπ base A hA)
    L T hL hlen hload hLT
  refine ⟨C, ?_⟩
  have hNreal : (Fintype.card V : ℝ) / (96 * (t + 1 : ℝ) ^ 2) ≤ N := by
    rw [card_eq_quotient_mul_fibre π m hm, hN]
    exact hNlen
  exact hNreal.trans (by exact_mod_cast hC)


/-- Manuscript Lemma 4.5 for the orbits of an actual normal subgroup. -/
theorem joining_short_connections {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hq : 2 ≤ Fintype.card (Quotient (MulAction.orbitRel H V))) (m d t : ℕ)
    (hm : ∀ a : Quotient (MulAction.orbitRel H V), Fintype.card {x : V // Quotient.mk'' x = a} = m)
    (hlarge : 192 * d * (t + 1) ^ 2 ≤ m) :
    letI := normalOrbitAction (V := V) H
    ∀ Q : Digraph (Quotient (MulAction.orbitRel H V)), Loopless Q → StronglyConnected Q →
      (∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b) →
      (∀ a, (Finset.univ.filter (Q a)).card = d) →
      (∀ b, (Finset.univ.filter (fun a => Q a b)).card = d) →
      (∀ a b, Q a b → ∀ (x : {v : V // Quotient.mk'' v = a})
        (y : {v : V // Quotient.mk'' v = b}), ∃ P : SimplePath D x.val y.val, P.length ≤ t) →
      ∃ C : Cycle D, (Fintype.card V : ℝ) / (96 * (t + 1 : ℝ) ^ 2) ≤ C.length := by
  let Ω := Quotient (MulAction.orbitRel H V)
  let π : V → Ω := Quotient.mk''
  let : MulAction G Ω := normalOrbitAction H
  intro Q _hloop hstrong hQ hout hin hshort
  exact joining_short_connections_on_partition D Q π Quotient.mk''_surjective
    hD hQ (normal_orbit_projection_smul H) ht hstrong (by omega) m d t
    (positive_regular_degree Q hstrong hq d hout) hm hout hin hshort hlarge

end DirectedCycles
