module

public import DirectedCycles.TemplateCycle

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- The a-successor of a connector's s-edge tail is absent from the entire
expanded cycle. Thus the only non-a edge cannot skip an occupied a-successor. -/
theorem connector_successor_absent {Q : Type*} [Group Q]
    (E : ExpansionTemplate G I a l D) (q : G →* Q) (h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (e : Fin E.length) (he : E.level e = l (E.position e)) :
    ∀ f k, E.point f k ≠ (E.vertex e*a^(E.choice e).val)*a := by
  intro f k hv
  have hchoice : (E.choice e).val ≤ D := by have := (E.choice e).isLt; omega
  have hu : l (E.position e)+(E.choice e).val+1 < h := by
    have := hgap (E.position e); omega
  have hp := E.point_projection q h hgap hpow r hx f k
  have hqtail : q ((E.vertex e*a^(E.choice e).val)*a) =
      r (E.position e)*(q a)^(l (E.position e)+(E.choice e).val+1) := by
    simp only [map_mul,map_pow,hx e,he,pow_add,pow_one,mul_assoc]
  have hcoordinates :
      ((E.tag f k).1, (⟨(E.tag f k).2.coordinate h,
        (E.tag f k).2.coordinate_lt (hgap (E.tag f k).1)⟩ : Fin h)) =
      (E.position e,⟨l (E.position e)+(E.choice e).val+1,hu⟩) :=
    hcoord (hp.symm.trans ((congrArg q hv).trans hqtail))
  by_cases hf : E.level f < l (E.position f)
  · rw [E.tag_fixed f k hf] at hcoordinates
    have hi : E.position f = E.position e := congrArg Prod.fst hcoordinates
    have hc := congrArg (fun z : I × Fin h => z.2.val) hcoordinates
    change E.level f = l (E.position e)+(E.choice e).val+1 at hc
    rw [hi] at hf
    omega
  · by_cases hk : k.val ≤ (E.choice f).val
    · rw [E.tag_outgoing f k hf hk] at hcoordinates
      have hi : E.position f = E.position e := congrArg Prod.fst hcoordinates
      have hc := congrArg (fun z : I × Fin h => z.2.val) hcoordinates
      change l (E.position f)+k.val = l (E.position e)+(E.choice e).val+1 at hc
      rw [hi] at hc
      have hkval : k.val = (E.choice e).val+1 := by omega
      simp only [point,hf,hk,ite_false,ite_true] at hv
      have hv' : E.vertex f*a^k.val = E.vertex e*a^k.val := by
        simpa only [hkval,pow_succ,mul_assoc] using hv
      have hfe : f = e := E.vertex.injective (mul_right_cancel hv')
      subst f
      omega
    · rw [E.tag_incoming f k hf hk] at hcoordinates
      have hi : E.position (finRotate E.length f) = E.position e := congrArg Prod.fst hcoordinates
      have hc := congrArg (fun z : I × Fin h => z.2.val) hcoordinates
      change h-(D-k.val+1) = l (E.position e)+(E.choice e).val+1 at hc
      have hki : k.val < D+1 := by simpa only [pointCount,hf,ite_false] using k.isLt
      have hh := hgap (E.position e)
      omega

end ExpansionTemplate
end DirectedCycles
