import DirectedCycles.LocalCommutingProducts
import DirectedCycles.LocalCommutingPowers
import DirectedCycles.LocalAdditivePowerSegment

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Pointwise products of commuting finite local power segments form an
actual power segment. Every product and all bracketings are supplied by the
four-letter ambient domain, rather than a global-group power identity. -/
theorem PowerSegment.product_segment {A : Set G}
    (hdom : L.AllProductsDefined A 4) {u v : G} {N : ℕ} (hN : 1 ≤ N)
    (p : L.PowerSegment u N) (q : L.PowerSegment v N)
    (hpA : ∀ n ≤ N, p.power n ∈ A) (hqA : ∀ n ≤ N, q.power n ∈ A)
    (huv : L.Commute u v) :
    ∃ h : G, L.mulRel u v h ∧ ∃ s : L.PowerSegment h N,
      (∀ n ≤ N, L.mulRel (p.power n) (q.power n) (s.power n)) ∧
      (∀ n ≤ N, s.power n ∈ L.wordPower A 2) := by
  classical
  have hu : u ∈ A := (p.one hN) ▸ hpA 1 hN
  have hv : v ∈ A := (q.one hN) ▸ hqA 1 hN
  have hdom3 : L.AllProductsDefined A 3 := hdom.mono L (Set.Subset.refl _) (by omega)
  have hcomm : ∀ i ≤ N, ∀ j ≤ N, L.Commute (q.power i) (p.power j) := by
    intro i hi j hj
    have hqv : L.Commute u (q.power i) := q.commute L hdom3 hv hu huv hqA i hi
    exact p.commute L hdom3 hu (hqA i hi) (hqv.symm L) hpA j hj
  have hbin : ∀ n ≤ N, L.Defined (p.power n) (q.power n) := by
    intro n hn
    obtain ⟨z,hz⟩ := hdom [p.power n,q.power n] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  let f : ℕ → G := fun n => if hn : n ≤ N then L.mul (p.power n) (q.power n) (hbin n hn) else L.one
  have hf : ∀ n ≤ N, L.mulRel (p.power n) (q.power n) (f n) := by
    intro n hn
    dsimp only [f]
    rw [dite_eq_left hn]
    exact L.mul_spec _ _ _
  have h0 : f 0 = L.one := by
    have hh := hf 0 (by omega)
    rw [p.zero,q.zero] at hh
    exact L.unique hh (L.one_mul L.one)
  have h1 : L.mulRel u v (f 1) := by simpa only [p.one hN,q.one hN] using hf 1 hN
  have hadd : ∀ n m, n+m ≤ N → L.mulRel (f n) (f m) (f (n+m)) := by
    intro n m hnm
    obtain ⟨z,hz,hz'⟩ := L.commuting_products hdom (hpA n (by omega)) (hqA n (by omega))
      (hpA m (by omega)) (hqA m (by omega)) (hcomm n (by omega) m (by omega))
      (hf n (by omega)) (hf m (by omega)) (p.add hnm) (q.add hnm)
    exact L.unique hz' (hf (n+m) hnm) ▸ hz
  let s := PowerSegment.of_add L f h0 (fun _ => rfl) hadd
  refine ⟨f 1,h1,s,hf,?_⟩
  intro n hn
  exact ⟨[p.power n,q.power n],rfl,by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact hpA n hn
    · exact hqA n hn,
    (Product.pair_iff L _ _ _).2 (hf n hn)⟩
end LocalGroupAlgebra
end DirectedCycles
