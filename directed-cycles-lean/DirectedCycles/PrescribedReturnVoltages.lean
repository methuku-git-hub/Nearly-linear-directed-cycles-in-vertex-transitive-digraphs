import DirectedCycles.PrescribedTreePotentials
import DirectedCycles.ReturnVoltages

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

theorem inward_cycle_arcs (W : OrbitCycleWalk (VoltageDigraph S) a)
    (A : Digraph I) (hA : W.inOrbitPath.vertices.IsChain (fun x y => A y x))
    (k : Fin W.length) (hk : 0 < k.val) : A (W.point k.succ).2 (W.orbitIndex k) := by
  change (List.ofFn (fun i : Fin W.length => (W.point i.succ).2)).IsChain (fun x y => A y x) at hA
  have hn : k.val-1+1 < W.length := by omega
  have hh := List.isChain_ofFn.mp hA (k.val-1) hn
  have hleft : (⟨k.val-1,by omega⟩ : Fin W.length).succ = k.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ,Fin.val_castSucc]
    omega
  have hright : (⟨k.val-1+1,hn⟩ : Fin W.length).succ = k.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  change A (W.point k.succ).2 (W.point k.castSucc).2
  simpa only [hleft,hright] using hh

/-- The inward tree gives voltage a at every nonroot orbit of the
prescribed cycle. This follows from its actual selected labels. -/
theorem inward_cycle_voltages (W : OrbitCycleWalk (VoltageDigraph S) a)
    (A : Digraph I) (hA : W.inOrbitPath.vertices.IsChain (fun x y => A y x))
    (label : I → I → G) (t : I → G) (ht : t (W.point 0).2 = 1)
    (hte : ∀ x y, A y x → t x = label x y*t y)
    (hlabel : ∀ k : Fin W.length,
      label (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) =
        if k.val+1 < W.length then 1 else a) :
    ∀ k : Fin W.length, 0 < k.val → t (W.orbitIndex k) = a := by
  have hall : ∀ m : ℕ, ∀ k : Fin W.length, 0 < k.val → W.length-k.val = m →
      t (W.orbitIndex k) = a := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk hkm
      have harc := W.inward_cycle_arcs A hA k hk
      rw [W.orbitIndex_succ] at harc
      rw [hte _ _ harc,hlabel]
      by_cases hnext : k.val+1 < W.length
      · rw [ite_eq_left hnext,one_mul]
        have hrot : finRotate W.length k = ⟨k.val+1,hnext⟩ := by
          let : NeZero W.length := ⟨by have := W.two_le; omega⟩
          apply Fin.ext
          simp [finRotate_apply,Fin.val_add,
            Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),Nat.mod_eq_of_lt hnext]
        rw [hrot]
        apply ih (W.length-(k.val+1)) (by omega) ⟨k.val+1,hnext⟩ (by simp) rfl
      · rw [ite_eq_right hnext]
        have hlast : k.succ = Fin.last W.length := by
          apply Fin.ext
          simp only [Fin.val_succ,Fin.val_last]
          omega
        rw [← W.orbitIndex_succ,hlast,W.closes]
        change a*t (W.point 0).2 = a
        rw [ht,mul_one]
  exact fun k hk => hall (W.length-k.val) k hk rfl

end OrbitCycleWalk
end DirectedCycles
