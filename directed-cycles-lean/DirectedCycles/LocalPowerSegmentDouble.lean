import DirectedCycles.LocalAdditivePowerSegment
import DirectedCycles.LocalTripleProducts
import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalWordPowerMonotonicity

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A power segment in A doubles in length inside A^2. The four-letter
A-domain supplies every new addition and hence every bracketing. -/
theorem PowerSegment.exists_double {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hN : 1 ≤ N) {A : Set G} (hA : L.one ∈ A)
    (hmem : ∀ n ≤ N, p.power n ∈ A) (hdom : L.AllProductsDefined A 4) :
    ∃ q : L.PowerSegment u (2*N), (∀ n ≤ N, q.power n = p.power n) ∧
      (∀ n ≤ 2*N, q.power n ∈ L.wordPower A 2) := by
  classical
  have hbin : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  let q : ℕ → G := fun n => if hn : n ≤ N then p.power n
    else if hn' : n ≤ 2*N then L.mul (p.power N) (p.power (n-N))
      (hbin _ (hmem N le_rfl) _ (hmem (n-N) (by omega))) else L.one
  have qsmall : ∀ n ≤ N, q n = p.power n := by
    intro n hn; simp only [q,dite_eq_left hn]
  have qlarge : ∀ n, N < n → n ≤ 2*N →
      L.mulRel (p.power N) (p.power (n-N)) (q n) := by
    intro n hn hn'
    simp only [q,dite_eq_right (not_le.mpr hn),dite_eq_left hn']
    exact L.mul_spec _ _ _
  have qmem : ∀ n ≤ 2*N, q n ∈ L.wordPower A 2 := by
    intro n hn
    by_cases hs : n ≤ N
    · rw [qsmall n hs]
      exact ⟨[p.power n,L.one],rfl,by aesop,(Product.pair_iff L _ _ _).2 (L.mul_one _)⟩
    · exact ⟨[p.power N,p.power (n-N)],rfl,by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl
        · exact hmem N le_rfl
        · exact hmem (n-N) (by omega),
        (Product.pair_iff L _ _ _).2 (qlarge n (by omega) hn)⟩
  have qadd : ∀ i j, i+j ≤ 2*N → L.mulRel (q i) (q j) (q (i+j)) := by
    intro i j hij
    have hqdom := hdom.wordPower L (by omega : 2*2 ≤ 4)
    obtain ⟨z,hz⟩ := hqdom [q i,q j] (by simp) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl
      · exact qmem i (by omega)
      · exact qmem j (by omega))
    have hmul : L.mulRel (q i) (q j) z := (Product.pair_iff L _ _ _).1 hz
    have he : z = q (i+j) := by
      by_cases his : i ≤ N
      · by_cases hjs : j ≤ N
        · rw [qsmall i his,qsmall j hjs] at hmul
          by_cases hsum : i+j ≤ N
          · rw [qsmall (i+j) hsum]
            exact L.unique hmul (p.add hsum)
          · have hsum1 : i+(N-i) = N := by omega
            have hsum2 : (N-i)+(i+j-N) = j := by omega
            have hab := p.add (n := i) (m := N-i) (by omega)
            rw [hsum1] at hab
            have hbc := p.add (n := N-i) (m := i+j-N) (by omega)
            rw [hsum2] at hbc
            exact (L.assoc hab hbc (qlarge (i+j) (by omega) hij) hmul).symm
        · have hjs' : N < j := by omega
          have hsi : i+(j-N) = i+j-N := by omega
          have hip : L.mulRel (p.power i) (p.power (j-N)) (p.power (i+j-N)) := by
            simpa only [hsi] using p.add (n := i) (m := j-N) (by omega)
          have hni : L.mulRel (p.power N) (p.power i) (q (N+i)) := by
            by_cases hi0 : i = 0
            · subst i; simpa only [Nat.add_zero,qsmall N le_rfl,p.zero] using L.mul_one (p.power N)
            · simpa only [Nat.add_sub_cancel_left] using qlarge (N+i) (by omega) (by omega)
          have hin : L.mulRel (p.power i) (p.power N) (q (N+i)) := by
            have hNsub : N-i ≤ N := Nat.sub_le _ _
            have hia := p.add (n := i) (m := N-i) (by omega)
            have hai := p.add (n := N-i) (m := i) (by omega)
            have hpair : L.mulRel (p.power i) (p.power N) (q (N+i)) := by
              obtain ⟨v,hv⟩ := hbin _ (hmem i his) _ (hmem N le_rfl)
              have hia' : L.mulRel (p.power i) (p.power (N-i)) (p.power N) := by simpa only [Nat.add_sub_of_le his] using hia
              have hai' : L.mulRel (p.power (N-i)) (p.power i) (p.power N) := by simpa only [Nat.sub_add_cancel his] using hai
              have hvq := L.assoc hia' hai' hni hv
              exact hvq ▸ hv
            exact hpair
          have htriple := hdom.mono L (Set.Subset.refl A) (by omega : 3 ≤ 4)
          obtain ⟨v,hleft,hright⟩ := htriple.triple L (hmem N le_rfl) (hmem i his)
            (hmem (j-N) (by omega)) hni hip
          have heq : v = q (i+j) := L.unique hright (qlarge (i+j) (by omega) hij)
          have hji := qlarge j hjs' (by omega)
          rw [qsmall i his] at hmul
          have he' := L.assoc hin hji hleft hmul
          exact he'.symm.trans heq
      · have hil : N < i := by omega
        have hjs : j ≤ N := by omega
        have hsum : (i-N)+j = i+j-N := by omega
        have hab := qlarge i hil (by omega)
        have hbc : L.mulRel (p.power (i-N)) (p.power j) (p.power (i+j-N)) := by
          simpa only [hsum] using p.add (n := i-N) (m := j) (by omega)
        rw [qsmall j hjs] at hmul
        exact L.assoc hab hbc hmul (qlarge (i+j) (by omega) hij)
    exact he ▸ hmul
  let qp := PowerSegment.of_add L q (by rw [qsmall 0 (by omega),p.zero])
    (fun _ => (qsmall 1 hN).trans (p.one hN)) qadd
  exact ⟨qp,qsmall,qmem⟩
end LocalGroupAlgebra
end DirectedCycles
