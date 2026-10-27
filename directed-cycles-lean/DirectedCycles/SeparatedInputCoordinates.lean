module

public import DirectedCycles.SeparatedLiftInput
public import DirectedCycles.ActualCertifiedEdges

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace SeparatedLiftInput
variable {G J : Type*} [Group G] [Finite G] {a : G}
  {S : Set (G ⧸ elementClosure a)} {C : Cycle (CayleyDigraph S)}
  {s : Fin C.length → G}
  {hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i)}
  {t : J → G} {D : ℕ}

def data (X : SeparatedLiftInput a S C s hstep t D) : List (ℕ × G) := cycleRunData X.runs s

theorem data_length (X : SeparatedLiftInput a S C s hstep t D) : X.data.length = C.length :=
  cycleRunData_length X.runs s

theorem data_get (X : SeparatedLiftInput a S C s hstep t D) (p : Fin X.data.length) :
    X.data[p.val] =
      (X.runs ⟨p.val,by rw [← X.data_length]; exact p.isLt⟩,
        s ⟨p.val,by rw [← X.data_length]; exact p.isLt⟩) :=
  cycleRunData_get X.runs s p

theorem data_nonempty (X : SeparatedLiftInput a S C s hstep t D) : X.data ≠ [] := by
  intro he
  have hh := X.data_length
  rw [he,List.length_nil] at hh
  have := C.two_le
  omega

theorem data_prefixes (X : SeparatedLiftInput a S C s hstep t D) :
    Function.Injective (fun i : Fin X.data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes X.data i.castSucc)) :=
  cycleRunData_prefix_injective (QuotientGroup.mk' (elementClosure a)) S C X.runs s hstep

theorem data_endpoint (X : SeparatedLiftInput a S C s hstep t D) :
    QuotientGroup.mk' (elementCommutators a) (X.data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^X.closing := by
  simpa only [data,cycleRunData_snd] using X.endpoint

theorem data_congruence (X : SeparatedLiftInput a S C s hstep t D) :
    (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((X.data.map (fun z => z.1+D)).sum : ℤ)+X.closing := by
  rw [elementClosure_factor_card_eq_orderOf,data,cycleRunData_sum]
  exact X.congruence

theorem group_le (X : SeparatedLiftInput a S C s hstep t D) :
    cyclicAuxiliaryGroup a D X.data X.data_nonempty ≤ elementCommutators a :=
  cyclicAuxiliaryGroup_le_of_congruence a D X.data X.data_nonempty X.closing
    X.data_endpoint X.data_congruence

theorem source_residue (X : SeparatedLiftInput a S C s hstep t D) (i : Fin C.length) (u : ℕ) :
    QuotientGroup.mk' (elementCommutators a)
      (runReference a D X.data ⟨i.val,by rw [X.data_length]; exact i.isLt⟩) *
        (QuotientGroup.mk' (elementCommutators a) a)^(X.runs i+u) =
      residuePower (QuotientGroup.mk' (elementCommutators a) a) (X.residues i+u) *
        QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod :=
  actual_run_source_residue a D X.runs s X.residues X.prefix_residues i u

theorem finish_offsets (X : SeparatedLiftInput a S C s hstep t D) :
    ∀ i : Fin C.length,
      QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take (((finRotate C.length).symm i).val+1)).prod =
        residuePower (QuotientGroup.mk' (elementCommutators a) a)
          (if i.val = 0 then (X.closing : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))) else 0) *
        QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod := by
  let b := QuotientGroup.mk' (elementCommutators a) a
  let : NeZero (orderOf b) := ⟨(orderOf_pos b).ne'⟩
  apply cyclic_prefix_finish_offsets b C.length C.two_le
    (fun i => QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod)
    (X.closing : ZMod (orderOf b))
  · simp
  · simp only [Fin.val_last,List.take_of_length_le (by simp : (List.ofFn s).length ≤ C.length),
      residuePower_intCast]
    exact X.endpoint

end SeparatedLiftInput
end DirectedCycles
