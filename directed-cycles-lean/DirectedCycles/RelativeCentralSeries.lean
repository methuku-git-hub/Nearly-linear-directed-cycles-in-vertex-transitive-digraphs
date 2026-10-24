import DirectedCycles.LowerCentralFactors
import DirectedCycles.NilpotentRanks

set_option autoImplicit false
open scoped Classical commutatorElement IsMulCommutative
namespace DirectedCycles

/-- Iterated commutators with the ambient group, starting at K. -/
def relativeSeries {G : Type*} [Group G] (K : Subgroup G) : ℕ → Subgroup G
  | 0 => K
  | i+1 => ⁅relativeSeries K i, (⊤ : Subgroup G)⁆

instance relativeSeries_normal {G : Type*} [Group G] (K : Subgroup G) [K.Normal] (i : ℕ) :
    (relativeSeries K i).Normal := by
  induction i with
  | zero => exact inferInstanceAs K.Normal
  | succ i ih => exact inferInstanceAs (⁅relativeSeries K i, (⊤ : Subgroup G)⁆).Normal

theorem relativeSeries_step_le {G : Type*} [Group G] (K : Subgroup G) [K.Normal] (i : ℕ) :
    relativeSeries K (i+1) ≤ relativeSeries K i := Subgroup.commutator_le_left _ _

theorem relativeSeries_le_lower {G : Type*} [Group G] (K : Subgroup G) (i : ℕ) :
    relativeSeries K i ≤ lowerSeries G i := by
  induction i with
  | zero => exact le_top
  | succ i ih => exact Subgroup.commutator_mono ih le_rfl

/-- Exponent propagation in the first entry of a central commutator. -/
theorem central_commutator_pow_of_pow_central {G : Type*} [Group G] (H : Subgroup G)
    (hc : ⁅H,(⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (e : ℕ)
    (he : ∀ x : H, x.val ^ e ∈ Subgroup.center G) (x : H) (y : G) :
    ⁅x.val,y⁆ ^ e = 1 := by
  let f := centralCommutatorLeftHom H hc y
  have hf := map_pow f x e
  have h : ⁅x.val,y⁆ ^ e = ⁅x.val ^ e,y⁆ := (congrArg Subtype.val hf).symm
  rw [h]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (he x) y).symm

/-- The exponent bound holds on the entire generated commutator subgroup. -/
theorem central_commutator_subgroup_pow_of_pow_central {G : Type*} [Group G] (H : Subgroup G)
    (hc : ⁅H,(⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (e : ℕ)
    (he : ∀ x : H, x.val ^ e ∈ Subgroup.center G) :
    ∀ x : (⁅H,(⊤ : Subgroup G)⁆ : Subgroup G), x ^ e = 1 := by
  let S : Set G := {g | ∃ x ∈ H, ∃ y : G, ⁅x,y⁆ = g}
  let K := ⁅H,(⊤ : Subgroup G)⁆
  have hK : K = Subgroup.closure S := by
    simp only [K, Subgroup.commutator_def, Subgroup.mem_top, true_and, S]
  let f : K →* Subgroup.center G := {
    toFun := fun x => ⟨x.val,hc x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hgen : Subgroup.closure (K.subtype ⁻¹' S) = ⊤ := by
    subst K
    rw [hK]
    exact Subgroup.closure_preimage_eq_top S
  have hp : ∀ x ∈ K.subtype ⁻¹' S, f x ^ e = 1 := by
    intro x hx
    obtain ⟨a,ha,b,hab⟩ := hx
    change ⁅a,b⁆ = x.val at hab
    apply Subtype.ext
    change x.val ^ e = 1
    rw [← hab]
    exact central_commutator_pow_of_pow_central H hc e he ⟨a,ha⟩ b
  intro x
  have h := commutative_image_exponent_of_generators f (K.subtype ⁻¹' S) hgen e hp x
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.center G => z.val) h

/-- An exponent for K/[K,G] propagates to every relative central factor. -/
theorem relativeSeries_pow_mem {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (e : ℕ) (he : ∀ x : K, x.val ^ e ∈ relativeSeries K 1) (i : ℕ) :
    ∀ x : relativeSeries K i, x.val ^ e ∈ relativeSeries K (i+1) := by
  induction i with
  | zero => exact he
  | succ i ih =>
    let N := relativeSeries K (i+1+1)
    let q := QuotientGroup.mk' N
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
    let A := (relativeSeries K i).map q
    let B := (relativeSeries K (i+1)).map q
    have hB : ⁅A,(⊤ : Subgroup (G ⧸ N))⁆ = B := by
      change ⁅(relativeSeries K i).map q,⊤⁆ = (⁅relativeSeries K i,(⊤ : Subgroup G)⁆).map q
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective q hq]
    have hc : B ≤ Subgroup.center (G ⧸ N) := by
      apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
      change ⁅(relativeSeries K (i+1)).map q,⊤⁆ = ⊥
      rw [← Subgroup.map_top_of_surjective q hq, ← Subgroup.map_commutator]
      exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact le_rfl)
    have hp : ∀ x : A, x.val ^ e ∈ Subgroup.center (G ⧸ N) := by
      intro x
      obtain ⟨a,ha,heq⟩ := x.property
      rw [← heq, ← map_pow]
      exact hc ⟨a^e,ih ⟨a,ha⟩,rfl⟩
    have hall := central_commutator_subgroup_pow_of_pow_central A (hB ▸ hc) e hp
    intro x
    have hx : q x.val ∈ ⁅A,(⊤ : Subgroup (G ⧸ N))⁆ := by
      rw [hB]
      exact ⟨x.val,x.property,rfl⟩
    have h := congrArg (fun z : (⁅A,(⊤ : Subgroup (G ⧸ N))⁆ : Subgroup (G ⧸ N)) => z.val)
      (hall ⟨q x.val,hx⟩)
    apply (QuotientGroup.eq_one_iff _).mp
    exact (map_pow q x.val e).trans h

instance relativeFactor_isMulCommutative {G : Type*} [Group G] (K : Subgroup G)
    [K.Normal] (i : ℕ) : IsMulCommutative (SeriesFactor (relativeSeries K) i) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  have hm : (commutator (relativeSeries K i)).map (relativeSeries K i).subtype =
      ⁅relativeSeries K i,relativeSeries K i⁆ := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.subtype_range]
  intro x hx
  have him : x.val ∈ (commutator (relativeSeries K i)).map (relativeSeries K i).subtype := ⟨x,hx,rfl⟩
  rw [hm] at him
  exact Subgroup.commutator_mono le_rfl le_top him

theorem relativeFactor_exponent {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (e : ℕ) (he : ∀ x : K, x.val ^ e ∈ relativeSeries K 1) (i : ℕ) :
    ∀ x : SeriesFactor (relativeSeries K) i, x ^ e = 1 := by
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective ((relativeSeries K (i+1)).subgroupOf (relativeSeries K i)) x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (relativeSeries_pow_mem K e he i a)

/-- Orders multiply along a series that starts at an arbitrary subgroup. -/
theorem card_start_eq_prod_series_factors {G : Type*} [Group G] [Finite G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal] (hd : ∀ i, H (i+1) ≤ H i)
    (c : ℕ) (hc : H c = ⊥) :
    Nat.card (H 0) = ∏ i ∈ Finset.range c, Nat.card (SeriesFactor H i) := by
  have hstep : ∀ i, Nat.card (H i) = Nat.card (H (i+1)) * Nat.card (SeriesFactor H i) := by
    intro i
    have h := ((H (i+1)).subgroupOf (H i)).card_mul_index
    rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hd i)).toEquiv] at h
    exact h.symm
  have hprod : ∀ n, Nat.card (H 0) = Nat.card (H n) * ∏ i ∈ Finset.range n, Nat.card (SeriesFactor H i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, hstep n]
      ring
  simpa only [hc, Subgroup.card_bot, one_mul] using hprod c

/-- A relative abelianization exponent bounds the order of any normal
subgroup of a finite nilpotent group. -/
theorem normal_subgroup_order_of_relative_exponent {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (K : Subgroup G) [K.Normal] (r c e : ℕ)
    (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) (he : 0 < e)
    (hexp : ∀ x : K, x.val ^ e ∈ relativeSeries K 1) :
    Nat.card K ≤ e ^ (c * ∑ i ∈ Finset.range c, r ^ (i+1)) := by
  let R := ∑ i ∈ Finset.range c, r ^ (i+1)
  have hbot : relativeSeries K c = ⊥ := by
    apply le_antisymm _ bot_le
    exact (relativeSeries_le_lower K c).trans
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc).le
  have hprod := card_start_eq_prod_series_factors (relativeSeries K) (relativeSeries_step_le K) c hbot
  change Nat.card K = _ at hprod
  rw [hprod]
  calc (∏ i ∈ Finset.range c, Nat.card (SeriesFactor (relativeSeries K) i)) ≤
        ∏ _i ∈ Finset.range c, e ^ R := by
          apply Finset.prod_le_prod
          intro i _
          let F := SeriesFactor (relativeSeries K) i
          let : Fintype F := Fintype.ofFinite F
          have hcard := finite_abelian_card_le_exponent_rank (G := F) e he (relativeFactor_exponent K e hexp i)
          have hcard' : Nat.card F ≤ e ^ Group.rank F := by
            simpa only [Nat.card_eq_fintype_card] using hcard
          have hrF : Group.rank F ≤ R :=
            (Group.rank_le_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)).trans
              (nilpotent_subgroup_rank_bound r c hr hc (relativeSeries K i))
          exact hcard'.trans (Nat.pow_le_pow_right (by omega) hrF)
       _ = e ^ (c * ∑ i ∈ Finset.range c, r ^ (i+1)) := by
          simp only [Finset.prod_const, Finset.card_range, ← pow_mul, R, Nat.mul_comm]

end DirectedCycles
