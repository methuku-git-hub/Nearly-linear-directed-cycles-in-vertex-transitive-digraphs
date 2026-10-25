module

public import DirectedCycles.LieStrongTrappingWindows
public import DirectedCycles.LocalConjugateWordDomains
public import DirectedCycles.LocalConjugateMaps
public import DirectedCycles.LocalEscapeMaps

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [LieGroup 𝓘(ℝ,E) ∞ H]

/-- The actual Lie trapping windows pull back through a local model. Inner
preimages are required only inside the proved source word window, not in
the entire ambient source group. All conjugate-word domains are derived. -/
theorem local_lie_model_trapping (L : LocalGroupAlgebra G) (hr : L.Reversible)
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H)) {K N : ℕ} (hK : 1 ≤ K)
    (hN : 100 ≤ N) (hNK : 9*(1000*K^3) ≤ N) {r : ℝ}
    (hw : LieStrongTrappingWindows H E (1000*K^3) r) (A S : Set G)
    (hA1 : L.one ∈ A) (hAi : ∀ a ∈ A, L.inv a ∈ A) (hSA : S ⊆ A)
    (hdom : L.AllProductsDefined A N)
    (hAout : π.toFun '' A ⊆ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r))
    (hSout : π.toFun '' S ⊆ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E)
      ((1001/1000 : ℝ)*(r/(10*((1000*K^3 : ℕ) : ℝ)))))
    (hAin : ∀ x ∈ L.wordPower A N, π.toFun x ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r → x ∈ A)
    (hSin : ∀ x ∈ A, π.toFun x ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E)
      (r/(10*((1000*K^3 : ℕ) : ℝ))) → x ∈ S) :
    L.AllProductsDefined (L.conjugates S (L.wordPower A 4)) (1000*K^3) ∧
    L.wordPower (L.conjugates S (L.wordPower A 4)) (1000*K^3) ⊆ A ∧
    (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → L.PowerIn (L.wordPower A 100) x j) → x ∈ A) ∧
    (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000000*K^3 → L.PowerIn A x j) → x ∈ S) := by
  let M := LocalGroupAlgebra.ofGroup H
  let B := (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)
  let T := (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E)
    ((1001/1000 : ℝ)*(r/(10*((1000*K^3 : ℕ) : ℝ))))
  have hpow : ∀ n, π.toFun '' (L.wordPower A n) ⊆ M.wordPower B n := by
    intro n
    exact (LocalGroupAlgebra.wordPower_image_subset π A n).trans (M.wordPower_mono_set hAout n)
  have hconj : π.toFun '' (L.conjugates S (L.wordPower A 4)) ⊆ M.conjugates T (M.wordPower B 4) :=
    (LocalGroupAlgebra.conjugates_image_subset π S (L.wordPower A 4)).trans
      (LocalGroupAlgebra.conjugates_mono hSout (hpow 4))
  obtain ⟨hQdom,hQword⟩ := L.conjugate_word_domains hr hAi hdom (by omega) hNK hSA
  refine ⟨hQdom,?_,?_,?_⟩
  · intro x hx
    apply hAin x ((L.wordPower_subset_wordPower hA1 hdom hNK le_rfl) (hQword hx))
    apply hw.conjugateWords
    exact M.wordPower_mono_set hconj (1000*K^3)
      (LocalGroupAlgebra.wordPower_image_subset π _ _ ⟨x,hx,rfl⟩)
  · intro x hx
    obtain ⟨y,hy,hpy⟩ := hx 1 (by omega) (by omega)
    have he : y = x := (LocalGroupAlgebra.Product.singleton_iff L).1
      (by simpa only [List.replicate_one] using hpy)
    apply hAin x ((L.wordPower_subset_wordPower hA1 hdom hN le_rfl) (he ▸ hy))
    apply hw.firstPowerTest
    intro j hj hj'
    obtain ⟨y,hy,hpy⟩ := hx j hj hj'
    have hp : M.PowerIn (M.wordPower B 100) (π.toFun x) j :=
      ⟨π.toFun y,hpow 100 ⟨y,hy,rfl⟩,by simpa only [List.map_replicate] using hpy.map π⟩
    exact (LocalGroupAlgebra.ofGroup_powerIn_iff _ _ _).1 hp
  · intro x hx
    have hKpos : 0 < K := by omega
    have hbound : 1 ≤ 1000000*K^3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    obtain ⟨y,hy,hpy⟩ := hx 1 (by omega) hbound
    have he : y = x := (LocalGroupAlgebra.Product.singleton_iff L).1
      (by simpa only [List.replicate_one] using hpy)
    apply hSin x (he ▸ hy)
    apply hw.secondPowerTest
    intro j hj hj'
    have hj'' : j ≤ 1000000*K^3 := by nlinarith
    obtain ⟨y,hy,hpy⟩ := hx j hj hj''
    have hp : M.PowerIn B (π.toFun x) j :=
      ⟨π.toFun y,hAout ⟨y,hy,rfl⟩,by simpa only [List.map_replicate] using hpy.map π⟩
    exact (LocalGroupAlgebra.ofGroup_powerIn_iff _ _ _).1 hp
end DirectedCycles
