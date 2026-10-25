module

public import DirectedCycles.RestrictedLayerGroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Baseline product and relative alternatives, as in equation (5.5). -/
def normalizedRelativeLabels {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (xs : List G) : Set G :=
  {xs.prod} ∪ {x | ∃ j : Fin xs.length, ∃ a ∈ S (j.val : ZMod T), a * (xs[j.val])⁻¹ = x}

/-- The exact generator description for the normalized auxiliary group. -/
theorem normalizedLayer_generation {G : Type*} [Group G] {T : ℕ} [NeZero T]
    (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T) (hxs : LayerWord S 0 xs)
    (hp : ∀ j < xs.length, (xs.take j).prod = 1) :
    Subgroup.closure (layerRoundProducts S) = Subgroup.closure (normalizedRelativeLabels S xs) := by
  let C := Subgroup.closure (layerRoundProducts S)
  let H := Subgroup.closure (normalizedRelativeLabels S xs)
  have hprodC : xs.prod ∈ C := Subgroup.subset_closure ⟨xs,hlen,hxs,rfl⟩
  have hprodH : xs.prod ∈ H := Subgroup.subset_closure (Or.inl rfl)
  apply le_antisymm
  · have hlabels : ∀ i : ZMod T, ∀ a ∈ S i, a ∈ H := by
      intro i a ha
      have hi : i.val < xs.length := by rw [hlen]; exact ZMod.val_lt i
      have hb : xs[i.val] ∈ H := by
        rcases normalizedBaseline_label xs hp i.val hi with he | he
        · rw [he]; exact H.one_mem
        · rw [he]; exact hprodH
      have hd : a*(xs[i.val])⁻¹ ∈ H := Subgroup.subset_closure
        (Or.inr ⟨⟨i.val,hi⟩,a,by simpa using ha,rfl⟩)
      simpa only [inv_mul_cancel_right] using H.mul_mem hd hb
    apply H.closure_le.mpr
    rintro g ⟨ys,_,hys,rfl⟩
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp ha
    have h := (layerWord_iff_get S 0 ys).mp hys j
    rw [List.get_eq_getElem] at hj
    rw [hj] at h
    exact hlabels _ a h
  · apply C.closure_le.mpr
    intro x hx
    rcases hx with hx | ⟨j,a,ha,rfl⟩
    · exact (Set.mem_singleton_iff.mp hx) ▸ hprodC
    · have hallowed := layerWord_set S 0 xs hxs j.val a (by simpa using ha)
      have hnew : (xs.set j.val a).prod ∈ C := Subgroup.subset_closure
        ⟨xs.set j.val a,by simpa using hlen,hallowed,rfl⟩
      have he := list_product_replacement xs j.val j.isLt a
      rw [hp j.val j.isLt,one_mul,inv_one,mul_one] at he
      rw [he] at hnew
      change a*(xs[j.val])⁻¹ ∈ C
      simpa only [mul_inv_cancel_right] using C.mul_mem hnew (C.inv_mem hprodC)

end DirectedCycles
