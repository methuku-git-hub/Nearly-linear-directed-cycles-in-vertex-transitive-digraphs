module

public import DirectedCycles.LocalOrderedGrid
public import DirectedCycles.LocalSignedPrefix
public import DirectedCycles.LocalCentralProductGrid
public import DirectedCycles.LocalShortSignedProperness
public import DirectedCycles.LocalIteratedGeneratorCommutators

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- The ordered grid of lifted generators and a short central segment is
proper. The entire grid is built from the actual source word domains; the
last coordinate is separated by the finite-period NSS argument. -/
theorem central_orderedGrid_injective (hd : L.DivisionClosed) (hr : L.Reversible)
    {A : Set G} (hNSS : L.IsNSS A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    {r : ℕ} (g : Fin (r+1) → D.small) (N : Fin (r+1) → ℕ)
    (hall : L.SignedWordsIn (fun i => (g i).val) N D.small)
    (hq : D.algebra.SignedWordsIn (fun i : Fin r => D.project (g i.castSucc))
      (fun i => N i.castSucc) Set.univ)
    (hproper : Function.Injective (D.algebra.orderedGrid hq))
    (hu : (g (Fin.last r)).val ≠ L.one)
    {M W : ℕ} (p : L.PowerSegment (g (Fin.last r)).val W) (hMW : M ≤ W)
    (hprev : ∀ n < M, p.power n ∈ A)
    (hshort : 2*N (Fin.last r) < M)
    (hkernel : ∀ k : ℤ, k.natAbs ≤ N (Fin.last r) → p.signedPower k ∈ P) :
    Function.Injective (L.orderedGrid hall) := by
  classical
  let Np : Fin r → ℕ := fun i => N i.castSucc
  have hpref : L.SignedWordsIn (fun i : Fin r => (g i.castSucc).val) Np D.small :=
    L.signedWords_prefix_defined (fun i => (g i).val) N D.small hall
  let a := L.orderedGrid hpref
  let z := L.orderedGrid hall
  have hpowersmall : ∀ j : ↥(signedCoordinateInterval (N (Fin.last r))), p.signedPower j.val ∈ D.small := by
    intro j
    let zero : SignedCoordinates Np := SignedCoordinates.zero Np
    have hz := L.orderedGrid_product hall (SignedCoordinates.snoc (N := N) zero j)
    rw [L.orderedLetters_succ] at hz
    simp only [SignedCoordinates.snoc_castSucc,SignedCoordinates.snoc_last,
      zero,SignedCoordinates.zero_val,L.orderedLetters_zero,List.nil_append] at hz
    have hj := (mem_signedCoordinateInterval _ _).1 j.property
    have he := hz.unique L (p.signed_block_product L hr j.val (by omega))
    exact he ▸ (z (SignedCoordinates.snoc (N := N) zero j)).property
  let b : ↥(signedCoordinateInterval (N (Fin.last r))) → D.small :=
    fun j => ⟨p.signedPower j.val,hpowersmall j⟩
  let f : SignedCoordinates Np × ↥(signedCoordinateInterval (N (Fin.last r))) → D.small :=
    fun kj => z (SignedCoordinates.snoc (N := N) kj.1 kj.2)
  have ha : Function.Injective (fun k => D.project (a k)) :=
    D.projected_orderedGrid_injective (fun i => g i.castSucc) Np hpref hq hproper
  have hb : Function.Injective (fun j => (b j).val) := by
    intro j k he
    apply Subtype.ext
    exact p.short_signed_injective L hd hr hNSS hdom hu hMW hprev hshort
      ((mem_signedCoordinateInterval _ _).1 j.property) ((mem_signedCoordinateInterval _ _).1 k.property) he
  have hb1 : ∀ j, D.project (b j) = D.algebra.one := by
    intro j
    exact (D.project_eq_one_iff_mem (b j)).2 (hkernel j.val ((mem_signedCoordinateInterval _ _).1 j.property))
  have hm : ∀ k j, L.mulRel (a k).val (b j).val (f (k,j)).val := by
    intro k j
    have hz := L.orderedGrid_product hall (SignedCoordinates.snoc (N := N) k j)
    rw [L.orderedLetters_succ] at hz
    simp only [SignedCoordinates.snoc_castSucc,SignedCoordinates.snoc_last] at hz
    obtain ⟨x,y,hx,hy,hm⟩ := hz.split_allow_empty L rfl
    have hx' := hx.unique L (L.orderedGrid_product hpref k)
    have hj := (mem_signedCoordinateInterval _ _).1 j.property
    have hy' := hy.unique L (p.signed_block_product L hr j.val (by omega))
    simpa only [hx',hy'] using hm
  have hf := D.productGrid_injective (hd.cancellative L hr) a b f ha hb hb1 hm
  intro k l he
  let kp : SignedCoordinates Np := fun i => k i.castSucc
  let lp : SignedCoordinates Np := fun i => l i.castSucc
  have hk : SignedCoordinates.snoc (N := N) kp (k (Fin.last r)) = k := by
    funext i
    induction i using Fin.lastCases <;> simp [kp,SignedCoordinates.snoc]
  have hl : SignedCoordinates.snoc (N := N) lp (l (Fin.last r)) = l := by
    funext i
    induction i using Fin.lastCases <;> simp [lp,SignedCoordinates.snoc]
  have hp : (kp,k (Fin.last r)) = (lp,l (Fin.last r)) := hf (by
    change (z (SignedCoordinates.snoc (N := N) kp (k (Fin.last r)))).val =
      (z (SignedCoordinates.snoc (N := N) lp (l (Fin.last r)))).val
    rw [hk,hl]
    exact congrArg Subtype.val he)
  rw [← hk,← hl]
  exact congrArg (fun kj => SignedCoordinates.snoc (N := N) kj.1 kj.2) hp
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
