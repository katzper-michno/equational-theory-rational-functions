import Lax149335Proofs.Appendix.Drops.ExchangeShiftBlock
import Lax149335Proofs.Appendix.Drops.Contents
import Lax149335Proofs.Appendix.Drops.SumShuffleLifts

/-!
# The shape of a drop with a co-product codomain (appendix, *Proof of Exchange Lemma*)

The sum normalisation lemma (`Lax149335Proofs.drops_with_sum_codomain_tree`) puts a drop with a
co-product codomain in the shape of a case tree whose leaves are `g ; Left`, `g ; Right` and
`g₁ + g₂`.  The case *Block* of the exchange lemma needs the normal form of the paper in its
sharpest form: **after a lift, a drop `A ⇒ P + Q` is a co-product of two drops**, unless all
of its leaves land in one of the two summands.  This is `Lax149335Proofs.SumSplitShape`, and
`Lax149335Proofs.sumSplitShape_of_drop` proves that every drop has such a shape.

The proof combines the leaves of the case tree pairwise; the nine combinations are handled by
the co-product shuffles `Lax149335Proofs.Term.sumInter`, `Lax149335Proofs.Term.sumSwapMid` and
`Lax149335Proofs.Term.sumSwapMid'` defined here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- The shape of a case tree into a co-product `P + Q`: either all of its leaves land in the
left summand, or all of them land in the right summand, or the source can be lifted to a
co-product whose two summands are mapped by drops into `P` and into `Q`. -/
inductive SumSplitShape : {A P Q : Ty} → Term A (P ⊕' Q) → Prop
  | left {A P Q : Ty} {t : Term A (P ⊕' Q)} {h : Term A P} :
      IsDrop h → t ≡ₜ (h ⨟ inl P Q) → SumSplitShape t
  | right {A P Q : Ty} {t : Term A (P ⊕' Q)} {h : Term A Q} :
      IsDrop h → t ≡ₜ (h ⨟ inr P Q) → SumSplitShape t
  | both {A P Q : Ty} {t : Term A (P ⊕' Q)} {A₁ A₂ : Ty} {b : Term A (A₁ ⊕' A₂)}
      {h₁ : Term A₁ P} {h₂ : Term A₂ Q} :
      IsLift b → IsDrop h₁ → IsDrop h₂ → t ≡ₜ (b ⨟ sumF h₁ h₂) → SumSplitShape t

/-- **Every case tree into a co-product has a split shape**: its leaves either all land in
the left summand, or all in the right summand, or the source can be lifted to a co-product of
two types, one mapped into `P` and the other into `Q` by a drop. -/
theorem sumSplitShape_of_tree {r : ℕ} : {A P Q : Ty} → {t : Term A (P ⊕' Q)} →
    IsNormalSumTree r t → SumSplitShape t := by
  intro A P Q t h
  induction h with
  | inl hg _ => exact .left hg (PEq.refl _)
  | inr hg _ => exact .right hg (PEq.refl _)
  | sumF hg₁ hg₂ _ _ => exact .both (IsLift.id _) hg₁ hg₂ (PEq.symm (PEq.id_comp _))
  | @either A₁ A₂ P Q t₁ t₂ _ _ ih₁ ih₂ =>
      cases ih₁ with
      | @left h hd he =>
          cases ih₂ with
          | @left h' hd' he' =>
              refine .left (IsDrop.comp (IsDrop.sumF hd hd') (IsDrop.codiag _)) ?_
              exact (either_congr he he').trans (PEq.symm (either_comp h h' (inl P Q)))
          | @right h' hd' he' =>
              refine .both (IsLift.id _) hd hd' ?_
              exact ((either_congr he he').trans
                (PEq.symm (Term.sumF_as_either h h'))).trans (PEq.symm (PEq.id_comp _))
          | @both B₁ B₂ b h₁ h₂ hb hd₁ hd₂ he' =>
              refine .both
                (IsLift.comp (IsLift.sumF (IsLift.id _) hb) (IsLift.sumAssocL _ _ _))
                (IsDrop.comp (IsDrop.sumF hd hd₁) (IsDrop.codiag _)) hd₂ ?_
              have key : ((sumF (Term.id A₁) b ⨟ sumAssocL A₁ B₁ B₂) ⨟
                  sumF (either h h₁) h₂) ≡ₜ either (h ⨟ inl P Q) (b ⨟ sumF h₁ h₂) := by
                calc ((sumF (Term.id A₁) b ⨟ sumAssocL A₁ B₁ B₂) ⨟ sumF (either h h₁) h₂)
                    ≡ₜ (sumF (Term.id A₁) b ⨟ (sumAssocL A₁ B₁ B₂ ⨟
                        sumF (either h h₁) h₂)) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ (sumAssocL A₁ B₁ B₂ ⨟
                        either (either h h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (Term.sumF_as_either _ _))
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ (sumAssocL A₁ B₁ B₂ ⨟
                        either (either (h ⨟ inl P Q) (h₁ ⨟ inl P Q)) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (either_congr (either_comp _ _ _)
                        (PEq.refl _)))
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟
                        either (h ⨟ inl P Q) (either (h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.symm (either_assocL _ _ _))
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ either (h ⨟ inl P Q) (sumF h₁ h₂)) :=
                      PEq.compR _ (either_congr (PEq.refl _)
                        (PEq.symm (Term.sumF_as_either _ _)))
                  _ ≡ₜ either (Term.id A₁ ⨟ (h ⨟ inl P Q)) (b ⨟ sumF h₁ h₂) :=
                      sumF_either _ _ _ _
                  _ ≡ₜ either (h ⨟ inl P Q) (b ⨟ sumF h₁ h₂) :=
                      either_congr (PEq.id_comp _) (PEq.refl _)
              exact (either_congr he he').trans (PEq.symm key)
      | @right h hd he =>
          cases ih₂ with
          | @left h' hd' he' =>
              refine .both (IsLift.comm _ _) hd' hd ?_
              have key : (comm A₁ A₂ ⨟ sumF h' h) ≡ₜ either (h ⨟ inr P Q) (h' ⨟ inl P Q) :=
                (PEq.compR _ (Term.sumF_as_either h' h)).trans (comm_either _ _)
              exact (either_congr he he').trans (PEq.symm key)
          | @right h' hd' he' =>
              refine .right (IsDrop.comp (IsDrop.sumF hd hd') (IsDrop.codiag _)) ?_
              exact (either_congr he he').trans (PEq.symm (either_comp h h' (inr P Q)))
          | @both B₁ B₂ b h₁ h₂ hb hd₁ hd₂ he' =>
              refine .both
                (IsLift.comp (IsLift.sumF (IsLift.id _) hb)
                  (Term.isLift_sumSwapMid' A₁ B₁ B₂))
                hd₁ (IsDrop.comp (IsDrop.sumF hd hd₂) (IsDrop.codiag _)) ?_
              have key : ((sumF (Term.id A₁) b ⨟ Term.sumSwapMid' A₁ B₁ B₂) ⨟
                  sumF h₁ (either h h₂)) ≡ₜ either (h ⨟ inr P Q) (b ⨟ sumF h₁ h₂) := by
                calc ((sumF (Term.id A₁) b ⨟ Term.sumSwapMid' A₁ B₁ B₂) ⨟
                      sumF h₁ (either h h₂))
                    ≡ₜ (sumF (Term.id A₁) b ⨟ (Term.sumSwapMid' A₁ B₁ B₂ ⨟
                        sumF h₁ (either h h₂))) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ (Term.sumSwapMid' A₁ B₁ B₂ ⨟
                        either (h₁ ⨟ inl P Q) (either h h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (Term.sumF_as_either _ _))
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ (Term.sumSwapMid' A₁ B₁ B₂ ⨟
                        either (h₁ ⨟ inl P Q)
                          (either (h ⨟ inr P Q) (h₂ ⨟ inr P Q)))) :=
                      PEq.compR _ (PEq.compR _ (either_congr (PEq.refl _)
                        (either_comp _ _ _)))
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟
                        either (h ⨟ inr P Q) (either (h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (Term.sumSwapMid'_either _ _ _)
                  _ ≡ₜ (sumF (Term.id A₁) b ⨟ either (h ⨟ inr P Q) (sumF h₁ h₂)) :=
                      PEq.compR _ (either_congr (PEq.refl _)
                        (PEq.symm (Term.sumF_as_either _ _)))
                  _ ≡ₜ either (Term.id A₁ ⨟ (h ⨟ inr P Q)) (b ⨟ sumF h₁ h₂) :=
                      sumF_either _ _ _ _
                  _ ≡ₜ either (h ⨟ inr P Q) (b ⨟ sumF h₁ h₂) :=
                      either_congr (PEq.id_comp _) (PEq.refl _)
              exact (either_congr he he').trans (PEq.symm key)
      | @both B₁ B₂ b h₁ h₂ hb hd₁ hd₂ he =>
          cases ih₂ with
          | @left h' hd' he' =>
              refine .both
                (IsLift.comp (IsLift.sumF hb (IsLift.id _))
                  (Term.isLift_sumSwapMid B₁ B₂ A₂))
                (IsDrop.comp (IsDrop.sumF hd₁ hd') (IsDrop.codiag _)) hd₂ ?_
              have key : ((sumF b (Term.id A₂) ⨟ Term.sumSwapMid B₁ B₂ A₂) ⨟
                  sumF (either h₁ h') h₂) ≡ₜ
                  either (b ⨟ sumF h₁ h₂) (h' ⨟ inl P Q) := by
                calc ((sumF b (Term.id A₂) ⨟ Term.sumSwapMid B₁ B₂ A₂) ⨟
                      sumF (either h₁ h') h₂)
                    ≡ₜ (sumF b (Term.id A₂) ⨟ (Term.sumSwapMid B₁ B₂ A₂ ⨟
                        sumF (either h₁ h') h₂)) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ (Term.sumSwapMid B₁ B₂ A₂ ⨟
                        either (either h₁ h' ⨟ inl P Q) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (Term.sumF_as_either _ _))
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ (Term.sumSwapMid B₁ B₂ A₂ ⨟
                        either (either (h₁ ⨟ inl P Q) (h' ⨟ inl P Q)) (h₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (either_congr (either_comp _ _ _)
                        (PEq.refl _)))
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟
                        either (either (h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q)) (h' ⨟ inl P Q)) :=
                      PEq.compR _ (Term.sumSwapMid_either _ _ _)
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ either (sumF h₁ h₂) (h' ⨟ inl P Q)) :=
                      PEq.compR _ (either_congr (PEq.symm (Term.sumF_as_either _ _))
                        (PEq.refl _))
                  _ ≡ₜ either (b ⨟ sumF h₁ h₂) (Term.id A₂ ⨟ (h' ⨟ inl P Q)) :=
                      sumF_either _ _ _ _
                  _ ≡ₜ either (b ⨟ sumF h₁ h₂) (h' ⨟ inl P Q) :=
                      either_congr (PEq.refl _) (PEq.id_comp _)
              exact (either_congr he he').trans (PEq.symm key)
          | @right h' hd' he' =>
              refine .both
                (IsLift.comp (IsLift.sumF hb (IsLift.id _)) (IsLift.sumAssocR _ _ _))
                hd₁ (IsDrop.comp (IsDrop.sumF hd₂ hd') (IsDrop.codiag _)) ?_
              have key : ((sumF b (Term.id A₂) ⨟ sumAssocR B₁ B₂ A₂) ⨟
                  sumF h₁ (either h₂ h')) ≡ₜ
                  either (b ⨟ sumF h₁ h₂) (h' ⨟ inr P Q) := by
                calc ((sumF b (Term.id A₂) ⨟ sumAssocR B₁ B₂ A₂) ⨟ sumF h₁ (either h₂ h'))
                    ≡ₜ (sumF b (Term.id A₂) ⨟ (sumAssocR B₁ B₂ A₂ ⨟
                        sumF h₁ (either h₂ h'))) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ (sumAssocR B₁ B₂ A₂ ⨟
                        either (h₁ ⨟ inl P Q) (either h₂ h' ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (Term.sumF_as_either _ _))
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ (sumAssocR B₁ B₂ A₂ ⨟
                        either (h₁ ⨟ inl P Q)
                          (either (h₂ ⨟ inr P Q) (h' ⨟ inr P Q)))) :=
                      PEq.compR _ (PEq.compR _ (either_congr (PEq.refl _)
                        (either_comp _ _ _)))
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟
                        either (either (h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q)) (h' ⨟ inr P Q)) :=
                      PEq.compR _ (PEq.symm (either_assocR _ _ _))
                  _ ≡ₜ (sumF b (Term.id A₂) ⨟ either (sumF h₁ h₂) (h' ⨟ inr P Q)) :=
                      PEq.compR _ (either_congr (PEq.symm (Term.sumF_as_either _ _))
                        (PEq.refl _))
                  _ ≡ₜ either (b ⨟ sumF h₁ h₂) (Term.id A₂ ⨟ (h' ⨟ inr P Q)) :=
                      sumF_either _ _ _ _
                  _ ≡ₜ either (b ⨟ sumF h₁ h₂) (h' ⨟ inr P Q) :=
                      either_congr (PEq.refl _) (PEq.id_comp _)
              exact (either_congr he he').trans (PEq.symm key)
          | @both C₁ C₂ c k₁ k₂ hc hk₁ hk₂ he' =>
              refine .both
                (IsLift.comp (IsLift.sumF hb hc) (Term.isLift_sumInter B₁ B₂ C₁ C₂))
                (IsDrop.comp (IsDrop.sumF hd₁ hk₁) (IsDrop.codiag _))
                (IsDrop.comp (IsDrop.sumF hd₂ hk₂) (IsDrop.codiag _)) ?_
              have key : ((sumF b c ⨟ Term.sumInter B₁ B₂ C₁ C₂) ⨟
                  sumF (either h₁ k₁) (either h₂ k₂)) ≡ₜ
                  either (b ⨟ sumF h₁ h₂) (c ⨟ sumF k₁ k₂) := by
                calc ((sumF b c ⨟ Term.sumInter B₁ B₂ C₁ C₂) ⨟
                      sumF (either h₁ k₁) (either h₂ k₂))
                    ≡ₜ (sumF b c ⨟ (Term.sumInter B₁ B₂ C₁ C₂ ⨟
                        sumF (either h₁ k₁) (either h₂ k₂))) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (sumF b c ⨟ (Term.sumInter B₁ B₂ C₁ C₂ ⨟
                        either (either h₁ k₁ ⨟ inl P Q) (either h₂ k₂ ⨟ inr P Q))) :=
                      PEq.compR _ (PEq.compR _ (Term.sumF_as_either _ _))
                  _ ≡ₜ (sumF b c ⨟ (Term.sumInter B₁ B₂ C₁ C₂ ⨟
                        either (either (h₁ ⨟ inl P Q) (k₁ ⨟ inl P Q))
                          (either (h₂ ⨟ inr P Q) (k₂ ⨟ inr P Q)))) :=
                      PEq.compR _ (PEq.compR _ (either_congr (either_comp _ _ _)
                        (either_comp _ _ _)))
                  _ ≡ₜ (sumF b c ⨟
                        either (either (h₁ ⨟ inl P Q) (h₂ ⨟ inr P Q))
                          (either (k₁ ⨟ inl P Q) (k₂ ⨟ inr P Q))) :=
                      PEq.compR _ (Term.sumInter_either _ _ _ _)
                  _ ≡ₜ (sumF b c ⨟ either (sumF h₁ h₂) (sumF k₁ k₂)) :=
                      PEq.compR _ (either_congr (PEq.symm (Term.sumF_as_either _ _))
                        (PEq.symm (Term.sumF_as_either _ _)))
                  _ ≡ₜ either (b ⨟ sumF h₁ h₂) (c ⨟ sumF k₁ k₂) := sumF_either _ _ _ _
              exact (either_congr he he').trans (PEq.symm key)

/-- **Every drop with a co-product codomain has, after a lift, a split shape.** -/
theorem sumSplitShape_of_drop {A P Q : Ty} {f : Term A (P ⊕' Q)} (hf : IsDrop f) :
    ∃ (D : Ty) (alpha : Term A D) (g : Term D (P ⊕' Q)),
      IsLift alpha ∧ SumSplitShape g ∧ f ≡ₜ (alpha ⨟ g) := by
  obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_sum_codomain_tree f hf
  exact ⟨D, alpha, g, ha, sumSplitShape_of_tree hg, he⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
