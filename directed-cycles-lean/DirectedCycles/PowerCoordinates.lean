module

public import DirectedCycles.Basic
public import DirectedCycles.SeriesCounts
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- An ordered product, whose factors need not commute. -/
def powerWord {G : Type*} [Group G] {n : ℕ} (u : Fin n → G) (t : Fin n → ℤ) : G :=
  (List.ofFn (fun i => u i ^ t i)).prod

/-- Every element is represented by this one fixed ordered family of powers. -/
def HasPowerCoordinates (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∃ u : Fin n → G, Function.Surjective (powerWord u)

theorem map_powerWord {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) {n : ℕ} (u : Fin n → G) (t : Fin n → ℤ) :
    f (powerWord u t) = powerWord (fun i => f (u i)) t := by
  simp only [powerWord, map_list_prod, List.map_ofFn]
  apply congrArg (fun w : Fin n → Q => (List.ofFn w).prod)
  funext i
  exact map_zpow f (u i) (t i)

theorem powerWord_append {G : Type*} [Group G] {m n : ℕ}
    (u : Fin m → G) (v : Fin n → G) (a : Fin m → ℤ) (b : Fin n → ℤ) :
    powerWord (Fin.append u v) (Fin.append a b) = powerWord u a * powerWord v b := by
  simp only [powerWord, List.ofFn_add, Fin.append_left', Fin.append_right, List.prod_append]

theorem hasPowerCoordinates_zero (G : Type*) [Group G] [Subsingleton G] : HasPowerCoordinates G 0 :=
  ⟨Fin.elim0, fun x => ⟨Fin.elim0, Subsingleton.elim _ x⟩⟩

theorem hasPowerCoordinates_of_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) {n : ℕ} (h : HasPowerCoordinates G n) :
    HasPowerCoordinates Q n := by
  obtain ⟨u, hu⟩ := h
  refine ⟨fun i => f (u i), ?_⟩
  intro x
  obtain ⟨g,rfl⟩ := hf x
  obtain ⟨t,rfl⟩ := hu g
  exact ⟨t, (map_powerWord f u t).symm⟩

/-- For an abelian group, a minimum generating set provides ordered coordinates. -/
theorem abelian_power_coordinates (G : Type*) [CommGroup G] [Group.FG G] :
    HasPowerCoordinates G (Group.rank G) := by
  obtain ⟨S, hScard, hS⟩ := Group.rank_spec G
  let E := S.equivFinOfCardEq hScard
  let u : Fin (Group.rank G) → G := fun i => (E.symm i).val
  have hU : Subgroup.closure (Set.range u) = ⊤ := by
    have he : Set.range u = (S : Set G) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact (E.symm i).property
      · intro hx
        exact ⟨E ⟨x,hx⟩, congrArg Subtype.val (E.symm_apply_apply ⟨x,hx⟩)⟩
    rw [he, hS]
  refine ⟨u, ?_⟩
  intro x
  obtain ⟨a,ha⟩ := Subgroup.exists_of_mem_closure_range u x (by rw [hU]; trivial)
  refine ⟨a, ?_⟩
  simpa only [powerWord, Fin.prod_ofFn] using ha.symm

/-- Lift quotient coordinates first, then append coordinates in the normal
subgroup. The product order is retained throughout. -/
theorem power_coordinates_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {m n : ℕ} (hN : HasPowerCoordinates N n) (hQ : HasPowerCoordinates (G ⧸ N) m) :
    HasPowerCoordinates G (m + n) := by
  obtain ⟨u,hu⟩ := hQ
  obtain ⟨v,hv⟩ := hN
  let q := QuotientGroup.mk' N
  let lift : G ⧸ N → G := fun x => Classical.choose (QuotientGroup.mk'_surjective N x)
  have hlift : ∀ x, q (lift x) = x := fun x => Classical.choose_spec (QuotientGroup.mk'_surjective N x)
  let U : Fin m → G := fun i => lift (u i)
  let V : Fin n → G := fun i => (v i).val
  refine ⟨Fin.append U V, ?_⟩
  intro x
  obtain ⟨a,ha⟩ := hu (q x)
  have hq : q (powerWord U a) = q x := by
    rw [map_powerWord]
    simpa only [U, hlift] using ha
  have hmem : (powerWord U a)⁻¹ * x ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((powerWord U a)⁻¹ * x) = 1
    rw [map_mul, map_inv, hq, inv_mul_cancel]
  obtain ⟨b,hb⟩ := hv ⟨(powerWord U a)⁻¹ * x, hmem⟩
  refine ⟨Fin.append a b, ?_⟩
  rw [powerWord_append]
  have he : powerWord V b = (powerWord U a)⁻¹ * x := by
    change powerWord (fun i => N.subtype (v i)) b = _
    rw [← map_powerWord N.subtype v b]
    exact congrArg Subtype.val hb
  rw [he, mul_inv_cancel_left]

/-- Lift the coordinates through a normal series with abelian factors. -/
theorem normal_series_power_coordinates {G : Type*} [Group G] [Finite G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal]
    (hd : ∀ i, H (i + 1) ≤ H i) (c : ℕ) (hc : H c = ⊥)
    [∀ i, IsMulCommutative (SeriesFactor H i)] :
    HasPowerCoordinates (H 0) (∑ i ∈ Finset.range c, Group.rank (SeriesFactor H i)) := by
  induction c generalizing H with
  | zero =>
    have : Subsingleton (H 0) := by rw [hc]; infer_instance
    simpa only [Finset.sum_range_zero] using hasPowerCoordinates_zero (H 0)
  | succ c ih =>
    let J : ℕ → Subgroup G := fun i => H (i + 1)
    have htail := ih J (fun i => hd (i + 1)) hc
    let e := Subgroup.subgroupOfEquivOfLe (hd 0)
    have hN := hasPowerCoordinates_of_surjective e.symm.toMonoidHom e.symm.surjective htail
    let : CommGroup (SeriesFactor H 0) := { (inferInstance : Group (SeriesFactor H 0)) with mul_comm := mul_comm' }
    have hQ := abelian_power_coordinates (SeriesFactor H 0)
    have h := power_coordinates_extension ((H 1).subgroupOf (H 0)) hN hQ
    simpa only [J, Finset.sum_range_succ', Nat.add_comm] using h

end DirectedCycles
