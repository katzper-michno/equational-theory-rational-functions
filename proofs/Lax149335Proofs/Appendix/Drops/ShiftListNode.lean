import Lax149335Proofs.Appendix.Drops.ShiftNonEmpty

/-!
# The list node of the shift exchange lemma

The last case of the induction of `Lax149335Proofs.Appendix.Drops.ShiftExchange`: the conclusion of
the shift exchange lemma is preserved by the homomorphism combinator.  Read on contents, this
is `Lax149335Proofs.SC.homT`: if a content is of the shape of the conclusion, then so is the content
of the list of its values.

The proof uses the two rebracketings of `Lax149335Proofs.Appendix.Drops.Contents`:

* `Lax149335Proofs.shift_content` handles a list whose element content is a **single** non-empty
  component: the first letter of `S` is peeled off, the trailing part of each element and the
  leading letter of the next one are merged into pairs, and what remains at the end is the
  tail of the last element;
* `Lax149335Proofs.block_content` handles a list whose element content is a **co-pairing**: the list
  is split into the blocks of the first summand and the blocks that follow an element of the
  second summand.

The induction that combines them is `Lax149335Proofs.NEC.homT_fdot`: for a non-empty content `c` and
an arbitrary content `w` of the class `Lax149335Proofs.QC`, the content of the list of values of
`c ⊙ w` is of the shape of the conclusion.  The empty components are removed beforehand, by
the normalisation `Lax149335Proofs.IsShiftExchangeShape.rc`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty} {r : ℕ}

/-- The constant empty word is an empty content. -/
theorem EC.nil (S T : Ty) : EC S T (nilT (S ⊕' T)) :=
  (PEq.symm (PEq.id_comp _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-! ### A list of one non-empty component -/

/-- **The base case**: the content of a list whose elements are a letter of `S` followed by a
tail content.  The prime lift `shift` peels the first letter of `S` off, and the pairs of the
middle are the tail of an element followed by the letter of `S` of the next one. -/
theorem SC1.homT_head {W X E : Ty} {x : Term X S} {v : Term E ((S ⊕' T)⋆)} (hx : IsDrop x)
    (hrx : rank x ≤ r) (hv : TC S T r v) :
    SC1 S T r (Term.homT (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙ v)) := by
  set u : Term (W ⊗ X) ((S ⊕' T)⋆) := (Term.snd W X ⨟ x) ⨟ sLetter S T with hu
  have hmid : TC S T r (Term.homT (v ⊙ u) ⊙ v) :=
    TC.pc_fdot (PC.homT (TC.fdot_sLetter hv hx hrx)) hv
  exact ⟨Ty.unit, (W ⊗ X) ⊗ ((E ⊗ (W ⊗ X))⋆ ⊗ E), Term.shift (W ⊗ X) E,
    nilT (S ⊕' T), u ⊙ (Term.homT (v ⊙ u) ⊙ v), IsLift.shift _ _, EC.nil S T,
    NEC.head hx hrx hmid, PEq.symm (shift_content u v)⟩

/-! ### A list of several non-empty components -/

/-- **The inductive step**: the content of a list whose elements are a non-empty content
followed by an arbitrary content of the class maintained by the induction.  The induction is
on the non-empty content; the co-pairing case is the one that uses `block`. -/
theorem NEC.homT_fdot {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : NEC S T r c) :
    ∀ {K : Ty} {w : Term K ((S ⊕' T)⋆)}, QC S T r w → SC1 S T r (Term.homT (c ⊙ w)) := by
  induction h with
  | @head W X E x v hx hrx hv =>
      intro K w hw
      refine SC1.of_liftEq (LiftEq.homT (LiftEq.assoc _ _ _)) ?_
      exact SC1.homT_head hx hrx (TC.fdot_sc hv (QC.sc hw))
  | @either A₁ A₂ c₁ c₂ _ hc₂ ih₁ ih₂ =>
      intro K w hw
      refine SC1.of_liftEq (LiftEq.homT
        ⟨distL A₁ A₂ K, IsLift.distL _ _ _, fdot_either_distL _ _ _⟩) ?_
      refine SC1.congr (PEq.symm (block_content (c₁ ⊙ w) (c₂ ⊙ w)))
        (SC1.lift_comp (IsLift.block _ _) ?_)
      have hleft : SC1 S T r (Term.homT (c₁ ⊙ w)) := ih₁ hw
      have hright : SC1 S T r (Term.homT ((c₂ ⊙ w) ⊙ Term.homT (c₁ ⊙ w))) := by
        refine SC1.of_liftEq (LiftEq.homT (LiftEq.assoc _ _ _)) ?_
        exact ih₂ (QC.fdot hw (Or.inr hleft))
      exact SC1.fdot hleft hright
  | congr h _ ih =>
      intro K w hw
      exact SC1.congr (homT_congr (fdot_congr h (PEq.refl _))) (ih hw)
  | @lift A A' rho c hrho _ ih =>
      intro K w hw
      refine SC1.congr (homT_congr (PEq.symm ((fdot_precomp _ _ _ _).trans
        (fdot_congr (PEq.refl _) (PEq.id_comp _))))) ?_
      exact SC1.congr (homT_precomp _ _)
        (SC1.lift_comp (IsLift.listF (IsLift.prodF hrho (IsLift.id K))) (ih hw))

/-- The content of a list whose element content is non-empty. -/
theorem NEC.homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : NEC S T r c) :
    SC1 S T r (Term.homT c) := by
  induction h with
  | head hx hrx hv => exact SC1.homT_head hx hrx hv
  | @either A₁ A₂ c₁ c₂ _ hc₂ ih₁ ih₂ =>
      refine SC1.congr (PEq.symm (block_content c₁ c₂))
        (SC1.lift_comp (IsLift.block _ _) ?_)
      exact SC1.fdot ih₁ (hc₂.homT_fdot (Or.inr ih₁))
  | congr h _ ih => exact SC1.congr (homT_congr h) ih
  | lift hrho _ ih =>
      exact SC1.congr (homT_precomp _ _) (SC1.lift_comp (IsLift.listF hrho) ih)

/-! ### The list node -/

/-- The content of a list whose element content is in the normal form of
`Lax149335Proofs.RC`. -/
theorem RC.homT_sc {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : RC S T r c) :
    SC S T r (Term.homT c) := by
  rcases h with he | (hn | hs)
  · exact EC.sc (EC.homT he)
  · exact SC1.sc hn.homT
  · obtain ⟨A₁, E, rho, e, n, hrho, he, hn, hc⟩ := hs
    refine SC.congr (homT_congr hc) (SC.congr (homT_precomp _ _)
      (SC.lift_comp (IsLift.listF hrho) ?_))
    refine SC.congr (PEq.symm (block_content e n))
      (SC.lift_comp (IsLift.block _ _) (SC1.sc ?_))
    exact EC.fdot_sc1 (EC.homT he) (NEC.homT (hn.fdot_ec (EC.homT he)))

/-- **The list node**, read on contents: the content of the list of the values of a content of
the shape of the conclusion is again of that shape. -/
theorem SC.homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SC S T r c) :
    SC S T r (Term.homT c) := by
  obtain ⟨D, alpha, g, ha, hg, hc⟩ := h
  refine SC.congr (homT_congr hc) (SC.congr (homT_precomp _ _)
    (SC.lift_comp (IsLift.listF ha) ?_))
  exact RC.homT_sc hg.rc

end Lax149335Proofs

bridge_export Lax149335Proofs
