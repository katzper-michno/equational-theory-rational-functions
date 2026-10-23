import Lax149335Proofs.Appendix.Drops.SplitMerge

/-!
# Naturality of `split` (appendix, *Proof of Exchange Lemma*, case *Split*)

The case *Split* of the exchange lemma has to treat the star node of a drop in normal form,
and for that it needs one instance of the exchange lemma for `split` itself: a homomorphic
image `listF g` of a drop `g : C ⇒ P + Q`, followed by `split P Q`, has a lift-drop
factorisation (`Lax149335Proofs.liftDrop_listF_split`).

The proof uses the split shape of a drop with a co-product codomain
(`Lax149335Proofs.sumSplitShape_of_drop`).  When both summands are used, the naturality of `split`
(Axiom 4) applies directly.  When only one of them is used, `split` is computed explicitly on
a list of left injections (`Lax149335Proofs.listF_inl_split`) and on a list of right injections
(`Lax149335Proofs.listF_inr_split`); both computations are done through the injectivity of `unsplit`
(`Lax149335Proofs.unsplit_inj`), and the resulting factorisations are lifts admitting exchange
followed by drops.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

/-! ### The inverse of `split` is provably injective -/

/-- `unsplit` has a left inverse, hence terms into the co-domain of `split` may be compared
through their contents. -/
theorem unsplit_inj {P Q A : Ty} {u v : Term A (splitCod P Q)}
    (h : (u ⨟ Term.unsplit P Q) ≡ₜ (v ⨟ Term.unsplit P Q)) : u ≡ₜ v := by
  calc u ≡ₜ (u ⨟ Term.id (splitCod P Q)) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (u ⨟ (Term.unsplit P Q ⨟ Term.split P Q)) :=
        PEq.compR _ (PEq.symm (PEq.unsplit_split P Q))
    _ ≡ₜ ((u ⨟ Term.unsplit P Q) ⨟ Term.split P Q) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((v ⨟ Term.unsplit P Q) ⨟ Term.split P Q) := PEq.compL _ h
    _ ≡ₜ (v ⨟ (Term.unsplit P Q ⨟ Term.split P Q)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (v ⨟ Term.id (splitCod P Q)) := PEq.compR _ (PEq.unsplit_split P Q)
    _ ≡ₜ v := PEq.comp_id _

/-- Splitting a list all of whose entries are left injections. -/
theorem listF_inl_split (P Q : Ty) :
    (listF (inl P Q) ⨟ Term.split P Q) ≡ₜ
      (unitR (P⋆) ⨟ prodF (Term.id (P⋆)) (nilT (Q ⊗ P⋆))) := by
  refine unsplit_inj ?_
  calc ((listF (inl P Q) ⨟ Term.split P Q) ⨟ Term.unsplit P Q)
      ≡ₜ (listF (inl P Q) ⨟ (Term.split P Q ⨟ Term.unsplit P Q)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF (inl P Q) ⨟ Term.id ((P ⊕' Q)⋆)) := PEq.compR _ (PEq.split_unsplit P Q)
    _ ≡ₜ listF (inl P Q) := PEq.comp_id _
    _ ≡ₜ Term.sWord P Q := PEq.symm (Term.sWord_eq P Q)
    _ ≡ₜ (Term.id (P⋆) ⨟ Term.sWord P Q) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((unitR (P⋆) ⨟ fst (P⋆) Ty.unit) ⨟ Term.sWord P Q) :=
        PEq.compL _ (PEq.symm (PEq.unitR_fst _))
    _ ≡ₜ (unitR (P⋆) ⨟ (fst (P⋆) Ty.unit ⨟ Term.sWord P Q)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR (P⋆) ⨟ (Term.sWord P Q ⊙ nilT (P ⊕' Q))) :=
        PEq.compR _ (PEq.symm (fdot_nil_right _))
    _ ≡ₜ (unitR (P⋆) ⨟ ((Term.id (P⋆) ⨟ Term.sWord P Q) ⊙
          (nilT (Q ⊗ P⋆) ⨟ Term.zWord P Q))) :=
        PEq.compR _ (fdot_congr (PEq.symm (PEq.id_comp _)) (PEq.symm Term.nilT_zWord))
    _ ≡ₜ (unitR (P⋆) ⨟ (prodF (Term.id (P⋆)) (nilT (Q ⊗ P⋆)) ⨟ Term.unsplit P Q)) :=
        PEq.compR _ (PEq.symm (fdot_precomp _ _ _ _))
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- Splitting a list all of whose entries are right injections. -/
theorem listF_inr_split (P Q : Ty) :
    (listF (inr P Q) ⨟ Term.split P Q) ≡ₜ
      ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
        prodF (nilT P) (listF (prodF (Term.id Q) (nilT P)))) := by
  refine unsplit_inj ?_
  have hblock : (prodF (Term.id Q) (nilT P) ⨟ Term.zBlock P Q) ≡ₜ
      (fst Q Ty.unit ⨟ tLetter P Q) := by
    calc (prodF (Term.id Q) (nilT P) ⨟ (tLetter P Q ⊙ Term.sWord P Q))
        ≡ₜ ((Term.id Q ⨟ tLetter P Q) ⊙ (nilT P ⨟ Term.sWord P Q)) := fdot_precomp _ _ _ _
      _ ≡ₜ (tLetter P Q ⊙ nilT (P ⊕' Q)) :=
          fdot_congr (PEq.id_comp _) Term.nilT_sWord
      _ ≡ₜ (fst Q Ty.unit ⨟ tLetter P Q) := fdot_nil_right _
  have hz : (listF (prodF (Term.id Q) (nilT P)) ⨟ Term.zWord P Q) ≡ₜ
      (listF (fst Q Ty.unit) ⨟ listF (inr P Q)) := by
    calc (listF (prodF (Term.id Q) (nilT P)) ⨟ Term.zWord P Q)
        ≡ₜ homT (prodF (Term.id Q) (nilT P) ⨟ Term.zBlock P Q) := PEq.symm (homT_precomp _ _)
      _ ≡ₜ homT (fst Q Ty.unit ⨟ tLetter P Q) := homT_congr hblock
      _ ≡ₜ (listF (fst Q Ty.unit) ⨟ homT (tLetter P Q)) := homT_precomp _ _
      _ ≡ₜ (listF (fst Q Ty.unit) ⨟ listF (inr P Q)) :=
          PEq.compR _ (Term.homT_tLetter P Q)
  have hD : (prodF (nilT P) (listF (prodF (Term.id Q) (nilT P))) ⨟ Term.unsplit P Q) ≡ₜ
      (snd Ty.unit ((Q ⊗ Ty.unit)⋆) ⨟ (listF (fst Q Ty.unit) ⨟ listF (inr P Q))) := by
    calc (prodF (nilT P) (listF (prodF (Term.id Q) (nilT P))) ⨟
          (Term.sWord P Q ⊙ Term.zWord P Q))
        ≡ₜ ((nilT P ⨟ Term.sWord P Q) ⊙
            (listF (prodF (Term.id Q) (nilT P)) ⨟ Term.zWord P Q)) := fdot_precomp _ _ _ _
      _ ≡ₜ (nilT (P ⊕' Q) ⊙ (listF (fst Q Ty.unit) ⨟ listF (inr P Q))) :=
          fdot_congr Term.nilT_sWord hz
      _ ≡ₜ _ := fdot_nil_left _
  have hL : ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
      (snd Ty.unit ((Q ⊗ Ty.unit)⋆) ⨟ listF (fst Q Ty.unit))) ≡ₜ Term.id (Q⋆) := by
    calc ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
          (snd Ty.unit ((Q ⊗ Ty.unit)⋆) ⨟ listF (fst Q Ty.unit)))
        ≡ₜ (unitL (Q⋆) ⨟ ((prodF (Term.id Ty.unit) (listF (unitR Q)) ⨟
            snd Ty.unit ((Q ⊗ Ty.unit)⋆)) ⨟ listF (fst Q Ty.unit))) := by
          refine (PEq.comp_assoc _ _ _).trans (PEq.compR _ ?_)
          exact PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitL (Q⋆) ⨟ ((snd Ty.unit (Q⋆) ⨟ listF (unitR Q)) ⨟ listF (fst Q Ty.unit))) :=
          PEq.compR _ (PEq.compL _ (PEq.nat_snd _ _))
      _ ≡ₜ ((unitL (Q⋆) ⨟ snd Ty.unit (Q⋆)) ⨟ (listF (unitR Q) ⨟ listF (fst Q Ty.unit))) := by
          refine (PEq.compR _ (PEq.comp_assoc _ _ _)).trans ?_
          exact PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (Q⋆) ⨟ listF (unitR Q ⨟ fst Q Ty.unit)) :=
          PEq.congr_comp (PEq.unitL_snd _) (PEq.list_comp _ _)
      _ ≡ₜ (Term.id (Q⋆) ⨟ listF (Term.id Q)) :=
          PEq.compR _ (PEq.congr_listF (PEq.unitR_fst Q))
      _ ≡ₜ Term.id (Q⋆) := (PEq.compR _ (PEq.list_id Q)).trans (PEq.id_comp _)
  calc ((listF (inr P Q) ⨟ Term.split P Q) ⨟ Term.unsplit P Q)
      ≡ₜ (listF (inr P Q) ⨟ (Term.split P Q ⨟ Term.unsplit P Q)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF (inr P Q) ⨟ Term.id ((P ⊕' Q)⋆)) := PEq.compR _ (PEq.split_unsplit P Q)
    _ ≡ₜ listF (inr P Q) := PEq.comp_id _
    _ ≡ₜ (Term.id (Q⋆) ⨟ listF (inr P Q)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ (((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
          (snd Ty.unit ((Q ⊗ Ty.unit)⋆) ⨟ listF (fst Q Ty.unit))) ⨟ listF (inr P Q)) :=
        PEq.compL _ (PEq.symm hL)
    _ ≡ₜ ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
          (snd Ty.unit ((Q ⊗ Ty.unit)⋆) ⨟ (listF (fst Q Ty.unit) ⨟ listF (inr P Q)))) := by
        refine (PEq.comp_assoc _ _ _).trans (PEq.compR _ ?_)
        exact PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
          (prodF (nilT P) (listF (prodF (Term.id Q) (nilT P))) ⨟ Term.unsplit P Q)) :=
        PEq.compR _ (PEq.symm hD)
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- A drop followed by a lift that admits exchange and then a drop has a lift-drop
factorisation. -/
theorem liftDrop_of_admitsExchange {A B C D : Ty} {e : Term A B} (he : IsDrop e)
    {l : Term B C} (hl : AdmitsExchange l) {d : Term C D} (hd : IsEqDrop d) :
    IsLiftDrop (e ⨟ (l ⨟ d)) :=
  IsLiftDrop.congr (PEq.symm (PEq.comp_assoc _ _ _)) ((hl he).comp_eqDrop hd)

/-- **The claim of the appendix**: a homomorphic image of a drop, followed by the prime lift
`split`, has a lift-drop factorisation.  This is the instance of the exchange lemma for
`split` that the case *Split* uses for its own star node; it is available because a drop with
a co-product codomain is, after a lift, a co-product of two drops, and `split` is natural. -/
theorem liftDrop_listF_split {P Q C : Ty} {g : Term C (P ⊕' Q)} (hg : IsDrop g) :
    IsLiftDrop (listF g ⨟ Term.split P Q) := by
  obtain ⟨D, alpha, g₀, ha, hshape, he⟩ := sumSplitShape_of_drop hg
  have key : IsLiftDrop (listF g₀ ⨟ Term.split P Q) := by
    cases hshape with
    | @left h hh het =>
        refine IsLiftDrop.congr ?_
          (liftDrop_of_admitsExchange (IsDrop.listF hh) (admitsExchange_unitR (P⋆))
            ((IsEqDrop.of_isDrop (IsDrop.id (P⋆))).prodF (isEqDrop_nilT (Q ⊗ P⋆))))
        calc (listF g₀ ⨟ Term.split P Q)
            ≡ₜ (listF (h ⨟ inl P Q) ⨟ Term.split P Q) := PEq.compL _ (PEq.congr_listF het)
          _ ≡ₜ ((listF h ⨟ listF (inl P Q)) ⨟ Term.split P Q) :=
              PEq.compL _ (PEq.symm (PEq.list_comp _ _))
          _ ≡ₜ (listF h ⨟ (listF (inl P Q) ⨟ Term.split P Q)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (listF h ⨟ (unitR (P⋆) ⨟ prodF (Term.id (P⋆)) (nilT (Q ⊗ P⋆)))) :=
              PEq.compR _ (listF_inl_split P Q)
    | @right h hh het =>
        have hlift : AdmitsExchange
            (unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) :=
          AdmitsExchange.comp (admitsExchange_unitL (Q⋆))
            (AdmitsExchange.prodF (admitsExchange_of_isDrop (IsDrop.id Ty.unit))
              (AdmitsExchange.listF (admitsExchange_unitR Q)))
        refine IsLiftDrop.congr ?_
          (liftDrop_of_admitsExchange (IsDrop.listF hh) hlift
            ((isEqDrop_nilT P).prodF
              (IsEqDrop.listF ((IsEqDrop.of_isDrop (IsDrop.id Q)).prodF (isEqDrop_nilT P)))))
        calc (listF g₀ ⨟ Term.split P Q)
            ≡ₜ (listF (h ⨟ inr P Q) ⨟ Term.split P Q) := PEq.compL _ (PEq.congr_listF het)
          _ ≡ₜ ((listF h ⨟ listF (inr P Q)) ⨟ Term.split P Q) :=
              PEq.compL _ (PEq.symm (PEq.list_comp _ _))
          _ ≡ₜ (listF h ⨟ (listF (inr P Q) ⨟ Term.split P Q)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (listF h ⨟ ((unitL (Q⋆) ⨟ prodF (Term.id Ty.unit) (listF (unitR Q))) ⨟
                prodF (nilT P) (listF (prodF (Term.id Q) (nilT P))))) :=
              PEq.compR _ (listF_inr_split P Q)
    | @both A₁ A₂ b h₁ h₂ hb hh₁ hh₂ het =>
        refine IsLiftDrop.congr ?_ (IsLiftDrop.comp_left (IsLift.comp (IsLift.listF hb)
          (IsLift.split A₁ A₂)) (IsLiftDrop.of_isDrop (IsDrop.prodF (IsDrop.listF hh₁)
            (IsDrop.listF (IsDrop.prodF hh₂ (IsDrop.listF hh₁))))))
        calc (listF g₀ ⨟ Term.split P Q)
            ≡ₜ (listF (b ⨟ sumF h₁ h₂) ⨟ Term.split P Q) := PEq.compL _ (PEq.congr_listF het)
          _ ≡ₜ ((listF b ⨟ listF (sumF h₁ h₂)) ⨟ Term.split P Q) :=
              PEq.compL _ (PEq.symm (PEq.list_comp _ _))
          _ ≡ₜ (listF b ⨟ (listF (sumF h₁ h₂) ⨟ Term.split P Q)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (listF b ⨟ (Term.split A₁ A₂ ⨟
                prodF (listF h₁) (listF (prodF h₂ (listF h₁))))) :=
              PEq.compR _ (PEq.nat_split h₁ h₂)
          _ ≡ₜ ((listF b ⨟ Term.split A₁ A₂) ⨟
                prodF (listF h₁) (listF (prodF h₂ (listF h₁)))) :=
              PEq.symm (PEq.comp_assoc _ _ _)
  refine IsLiftDrop.congr ?_ (IsLiftDrop.comp_left (IsLift.listF ha) key)
  calc (listF g ⨟ Term.split P Q)
      ≡ₜ (listF (alpha ⨟ g₀) ⨟ Term.split P Q) := PEq.compL _ (PEq.congr_listF he)
    _ ≡ₜ ((listF alpha ⨟ listF g₀) ⨟ Term.split P Q) :=
        PEq.compL _ (PEq.symm (PEq.list_comp _ _))
    _ ≡ₜ (listF alpha ⨟ (listF g₀ ⨟ Term.split P Q)) := PEq.comp_assoc _ _ _

end Lax149335Proofs

bridge_export Lax149335Proofs
