module

public import DirectedCycles.LocalPowerPeriod
public import DirectedCycles.LocalPowerSegmentDouble

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The signed interval has one copy of zero and two copies of each positive
exponent. Its values are actual finite-segment powers and their inverses. -/
def PowerSegment.signedMap {u : G} {N : ℕ} (p : L.PowerSegment u N) :
    Fin (N+1) ⊕ Fin N → G :=
  Sum.elim (fun i => p.power i.val) (fun i => L.inv (p.power (i.val+1)))

/-- A local NSS set remains NSS on a larger region whenever global
subgroups trapped in that region are forced into the original set. -/
theorem nss_of_subgroup_trapping {A B : Set G} (hNSS : L.IsNSS A)
    (htrap : ∀ H : Set G, L.IsGlobalSubgroup H → H ⊆ B → H ⊆ A) : L.IsNSS B :=
  fun H hH hHB => hNSS H hH (htrap H hH hHB)

/-- Signed powers are distinct under local NSS and the actual subgroup
trapping property. Doubling constructs the domain of every candidate period. -/
theorem PowerSegment.signedMap_injective (hc : L.Cancellative) {A : Set G}
    (hA : L.one ∈ A) (hNSS : L.IsNSS A)
    (htrap : ∀ H : Set G, L.IsGlobalSubgroup H → H ⊆ L.wordPower A 2 → H ⊆ A)
    {u : G} (hu : u ≠ L.one) {N : ℕ} (p : L.PowerSegment u N) (hN : 1 ≤ N)
    (hmem : ∀ n ≤ N, p.power n ∈ A) (hdom : L.AllProductsDefined A 8) :
    Function.Injective (p.signedMap L) := by
  obtain ⟨q,hq,hqmem⟩ := p.exists_double L hN hA hmem
    (hdom.mono L (Set.Subset.refl _) (by omega : 4 ≤ 8))
  have hNSS2 := L.nss_of_subgroup_trapping hNSS htrap
  have hbin : ∀ x ∈ L.wordPower A 2, ∀ y ∈ L.wordPower A 2, L.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := (hdom.wordPower L (by omega : 2*2 ≤ 8)) [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  have hinj : ∀ i ≤ N, ∀ j ≤ N, p.power i = p.power j → i = j := by
    intro i hi j hj he
    apply q.injective_prefix L hc hNSS2 hu (fun n hn => hqmem n hn.le) hbin (show i < 2*N by omega) (show j < 2*N by omega)
    simpa only [hq i hi,hq j hj] using he
  have hcross : ∀ i ≤ N, ∀ j, 0 < j → j ≤ N → p.power i ≠ L.inv (p.power j) := by
    intro i hi j hj0 hj he
    have hsum : i+j ≤ 2*N := by omega
    have hprod := q.add hsum
    rw [hq i hi,hq j hj,he] at hprod
    have hperiod : q.power (i+j) = L.one := L.unique hprod (L.inv_mul _)
    let s : L.PowerSegment u (i+j) := ⟨q.power,fun n hn => q.product n (by omega)⟩
    exact hu (s.eq_one_of_period L hNSS2 (by omega) hperiod (fun n hn => hqmem n (by omega)) hbin)
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have he : p.power i.val = p.power j.val := hab
      have hij := hinj i.val (by omega) j.val (by omega) he
      exact congrArg Sum.inl (Fin.ext hij)
    | inr j => exact (hcross i.val (by omega) (j.val+1) (by omega) (by omega) hab).elim
  | inr i =>
    cases b with
    | inl j => exact (hcross j.val (by omega) (i.val+1) (by omega) (by omega) hab.symm).elim
    | inr j =>
      have he : L.inv (p.power (i.val+1)) = L.inv (p.power (j.val+1)) := hab
      have hij := hinj (i.val+1) (by omega) (j.val+1) (by omega) (L.inv_injective he)
      exact congrArg Sum.inr (Fin.ext (by omega))

noncomputable def PowerSegment.signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N) : Finset G := by
  classical
  exact Finset.univ.image (p.signedMap L)

theorem PowerSegment.mem_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N) (x : G) :
    x ∈ p.signedProgression L ↔ ∃ i, p.signedMap L i = x := by
  classical
  simp only [signedProgression,Finset.mem_image,Finset.mem_univ,true_and]

theorem PowerSegment.card_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hinj : Function.Injective (p.signedMap L)) : (p.signedProgression L).card = 2*N+1 := by
  classical
  rw [signedProgression,Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
  omega

theorem PowerSegment.signedProgression_subset {u : G} {N : ℕ} (p : L.PowerSegment u N)
    {A : Set G} (hi : ∀ x ∈ A, L.inv x ∈ A) (hmem : ∀ n ≤ N, p.power n ∈ A) :
    (p.signedProgression L : Set G) ⊆ A := by
  intro x hx
  obtain ⟨i,rfl⟩ := (p.mem_signedProgression L x).1 hx
  cases i with
  | inl i => exact hmem i.val (by omega)
  | inr i => exact hi _ (hmem (i.val+1) (by omega))

theorem PowerSegment.one_mem_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N) :
    L.one ∈ p.signedProgression L :=
  (p.mem_signedProgression L L.one).2 ⟨Sum.inl ⟨0,by omega⟩,p.zero⟩

theorem PowerSegment.inv_mem_signedProgression {u : G} {N : ℕ} (p : L.PowerSegment u N)
    {x : G} (hx : x ∈ p.signedProgression L) : L.inv x ∈ p.signedProgression L := by
  obtain ⟨i,rfl⟩ := (p.mem_signedProgression L x).1 hx
  apply (p.mem_signedProgression L _).2
  cases i with
  | inl i =>
    by_cases hi : i.val = 0
    · refine ⟨Sum.inl ⟨0,by omega⟩,?_⟩
      change p.power 0 = L.inv (p.power i.val)
      rw [hi,p.zero,L.inv_one]
    · refine ⟨Sum.inr ⟨i.val-1,by omega⟩,?_⟩
      change L.inv (p.power (i.val-1+1)) = L.inv (p.power i.val)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
  | inr i =>
    refine ⟨Sum.inl ⟨i.val+1,by omega⟩,?_⟩
    change p.power (i.val+1) = L.inv (L.inv (p.power (i.val+1)))
    rw [L.inv_inv]
end LocalGroupAlgebra
end DirectedCycles
