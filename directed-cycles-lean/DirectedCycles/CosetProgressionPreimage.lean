import DirectedCycles.CosetProgressionHomWords
import DirectedCycles.SurjectiveTupleGeneration

set_option autoImplicit false
namespace DirectedCycles

/-- Pull back a coset nilprogression through an actual surjective group
homomorphism. Its finite subgroup is the full subgroup preimage. -/
noncomputable def preimageCosetNilprogression {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) {r c : ℕ} (Q : CosetNilprogression H r c) :
    CosetNilprogression G r c := by
  let U := Q.U.comap f
  let K := Q.H.comap f
  let F := f.subgroupComap Q.U
  have hF := subgroupComap_surjective_of_surjective f hf Q.U
  let g : Fin r → U := fun i => Classical.choose (hF (Q.generators i))
  have hg : ∀ i, F (g i) = Q.generators i := fun i => Classical.choose_spec (hF (Q.generators i))
  have hK : K.subgroupOf U = (Q.H.subgroupOf Q.U).comap F := rfl
  have hnormal : (K.subgroupOf U).Normal := by rw [hK]; infer_instance
  have hgen : Subgroup.closure ((K.subgroupOf U : Set U) ∪ Set.range g) = ⊤ := by
    rw [hK]
    exact generates_of_surjective_tuple_lifts F hF (Q.H.subgroupOf Q.U) Q.generators g hg Q.generates
  refine ⟨U,K,Subgroup.comap_mono Q.hHU,hnormal,g,Q.lengths,Q.lengths_pos,hgen,?_⟩
  let := hnormal
  intro w hw
  have hq := Q.commutators w hw
  rw [← w.map_eval (QuotientGroup.mk' (Q.H.subgroupOf Q.U)) Q.generators] at hq
  have hmemQ : w.eval Q.generators ∈ Q.H.subgroupOf Q.U :=
    (QuotientGroup.eq_one_iff (w.eval Q.generators)).1 hq
  have hmem : (w.eval Q.generators).val ∈ Q.H := hmemQ
  rw [← w.map_eval (QuotientGroup.mk' (K.subgroupOf U)) g]
  apply (QuotientGroup.eq_one_iff _).2
  change f (w.eval g).val ∈ Q.H
  have he := w.map_eval F g
  rw [show (fun i => F (g i)) = Q.generators from funext hg] at he
  have hev := congrArg (fun z : Q.U => z.val) he
  change f (w.eval g).val = (w.eval Q.generators).val at hev
  exact hev.symm ▸ hmem

/-- The carrier equality is exact, for any actual generator lifts and the
full subgroup preimage. It does not assume an extra containment property. -/
theorem coset_progression_carrier_preimage {G H : Type*} [Group G] [Group H]
    (f : G →* H) {r c d : ℕ} (P : CosetNilprogression G r c) (Q : CosetNilprogression H r d)
    (hH : P.H = Q.H.comap f) (hg : ∀ i, f (P.generators i).val = (Q.generators i).val)
    (hN : P.lengths = Q.lengths) : P.carrier = f ⁻¹' Q.carrier := by
  have hword : ∀ w, f (signedWordValue (fun i => (P.generators i).val) w) =
      signedWordValue (fun i => (Q.generators i).val) w := by
    intro w
    rw [map_signedWordValue,show (fun i => f (P.generators i).val) = (fun i => (Q.generators i).val) from funext hg]
  ext z
  constructor
  · rintro ⟨h,w,hw,hz⟩
    have hfh : f h.val ∈ Q.H := by
      exact (congrArg (fun S : Subgroup G => h.val ∈ S) hH).mp h.property
    refine ⟨⟨f h.val,hfh⟩,w,?_,?_⟩
    · simpa only [hN] using hw
    · have hh := congrArg f hz
      rwa [map_mul,hword] at hh
  · rintro ⟨h,w,hw,hz⟩
    let x := signedWordValue (fun i => (P.generators i).val) w
    have hh : z*x⁻¹ ∈ P.H := by
      rw [hH]
      change f (z*x⁻¹) ∈ Q.H
      rw [map_mul,map_inv,hword,hz.symm]
      simpa only [mul_inv_cancel_right] using h.property
    refine ⟨⟨z*x⁻¹,hh⟩,w,?_,?_⟩
    · simpa only [hN] using hw
    · change (z*x⁻¹)*x = z
      exact inv_mul_cancel_right z x

/-- The constructed preimage has exactly the full preimage carrier. -/
theorem preimageCosetNilprogression_carrier {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) {r c : ℕ} (Q : CosetNilprogression H r c) :
    (preimageCosetNilprogression f hf Q).carrier = f ⁻¹' Q.carrier := by
  apply coset_progression_carrier_preimage f _ Q rfl ?_ rfl
  intro i
  exact congrArg Subtype.val (Classical.choose_spec (subgroupComap_surjective_of_surjective f hf Q.U (Q.generators i)))
end DirectedCycles
