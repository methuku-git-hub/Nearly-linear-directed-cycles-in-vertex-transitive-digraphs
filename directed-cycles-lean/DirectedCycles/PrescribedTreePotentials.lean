import DirectedCycles.OrbitCycleLabels
import DirectedCycles.TreePotentials

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

theorem out_tree_potential [Fintype I] (W : OrbitCycleWalk (VoltageDigraph S) a)
    (hstart : (W.point 0).1 = 1)
    (B : PartialOutBranching (fun i j => (S i j).Nonempty) (W.point 0).2 Finset.univ)
    (hB : W.outOrbitPath.vertices.IsChain B.arc) (label : I → I → G)
    (hlabel : ∀ k, label (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) = W.edgeLabel k) :
    ∀ k : Fin W.length, B.potential label (W.orbitIndex k) (Finset.mem_univ _) =
      (W.point k.castSucc).1 := by
  change (List.ofFn W.orbitIndex).IsChain B.arc at hB
  have hall : ∀ n : ℕ, ∀ hn : n < W.length,
      B.potential label (W.orbitIndex ⟨n,hn⟩) (Finset.mem_univ _) =
        (W.point (⟨n,hn⟩ : Fin W.length).castSucc).1 := by
    intro n
    induction n with
    | zero =>
      intro hn
      change B.potential label (W.point 0).2 _ = (W.point 0).1
      rw [B.potential_root,hstart]
    | succ n ih =>
      intro hn
      have hn' : n < W.length := by omega
      have harc := List.isChain_ofFn.mp hB n hn
      have hp := B.potential_arc label (Finset.mem_univ _) (Finset.mem_univ _) harc
      have hl := hlabel ⟨n,hn'⟩
      rw [← W.orbitIndex_succ] at hl
      change label (W.orbitIndex ⟨n,hn'⟩) (W.orbitIndex ⟨n+1,hn⟩) = W.edgeLabel ⟨n,hn'⟩ at hl
      rw [hp,ih hn',hl]
      simp only [edgeLabel]
      exact mul_inv_cancel_left _ _
  exact fun k => hall k.val k.isLt

/-- Once representatives have been normalized along the prescribed
out-path, all internal cycle labels become 1 and the closing label is a. -/
theorem normalized_cycle_labels (W : OrbitCycleWalk (VoltageDigraph S) a)
    (p : I → G)
    (hp : ∀ k, p (W.orbitIndex k) = (W.point k.castSucc).1)
    (label : I → I → G)
    (hlabel : ∀ k, label (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) = W.edgeLabel k) :
    ∀ k : Fin W.length,
      p (W.orbitIndex k) * label (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) *
        (p (W.orbitIndex (finRotate W.length k)))⁻¹ =
        if k.val+1 < W.length then 1 else a := by
  intro k
  rw [hp,hlabel]
  simp only [edgeLabel,mul_inv_cancel_left]
  by_cases hk : k.val+1 < W.length
  · rw [ite_eq_left hk]
    have hnext : finRotate W.length k = ⟨k.val+1,hk⟩ := by
      let : NeZero W.length := ⟨by have := W.two_le; omega⟩
      apply Fin.ext
      simp [finRotate_apply,Fin.val_add,
        Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),Nat.mod_eq_of_lt hk]
    rw [hnext,hp]
    exact mul_inv_cancel _
  · rw [ite_eq_right hk]
    have hlast : k.succ = Fin.last W.length := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_last]; omega
    have hzero : finRotate W.length k = ⟨0,by have := W.two_le; omega⟩ := by
      let : NeZero W.length := ⟨by have := W.two_le; omega⟩
      apply Fin.ext
      have hv : k.val+1 = W.length := by omega
      simp [finRotate_apply,Fin.val_add,
        Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),hv]
    rw [hzero,hp,hlast,W.closes]
    change a*(W.point 0).1*((W.point 0).1)⁻¹ = a
    exact mul_inv_cancel_right _ _

end OrbitCycleWalk
end DirectedCycles
