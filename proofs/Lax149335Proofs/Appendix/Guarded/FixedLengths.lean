import Lax149335Proofs.Appendix.ConcatenationMaps
import Mathlib.Tactic.Set

/-!
# Extracting a prefix and a suffix of fixed length (appendix, proof of Lemma 6.4)

This file proves the appendix lemma *fixed lengths extracted*: for every type `C` and every
`k`, the concatenation map

`(C⁰ + ⋯ + C^{2k+1}) + C^{k+1} × C* × C^{k+1} ↣ C*`

is a provable isomorphism.  In other words, a list either has length at most `2k+1`, or a
prefix and a suffix of length `k+1` can be extracted from it, and this case distinction is
available inside the equational theory.

The proof follows the appendix: the inverse is built with the list deconstructors, by
induction on `k`, and the resulting composition is a concatenation map because each of its
steps is one — that is, because each step is a *rebracketing*.

To keep track of both facts at once, the file works with the structure
`Lax149335Proofs.Term.RIso`: an isomorphism between two list-polynomial shapes which commutes with
the concatenation maps.  Such isomorphisms compose, can be inverted, and are closed under
the type constructors; the atomic ones are `cons`, `snoc`, the distributivity maps, the
associators, the unit maps and the associativity of co-products.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Isomorphisms of list-polynomial shapes that commute with the concatenation maps -/

/-- An isomorphism `F(C) ≅ G(C)` which is a rebracketing, i.e. which commutes with the two
concatenation maps into `C*`. -/
structure RIso (C : Ty) (F G : TyF) where
  /-- The isomorphism. -/
  fwd : Term (F.app C) (G.app C)
  /-- Its inverse. -/
  bwd : Term (G.app C) (F.app C)
  /-- The two terms are mutually inverse. -/
  fwd_bwd : (fwd ⨟ bwd) ≡ₜ Term.id (F.app C)
  /-- The two terms are mutually inverse. -/
  bwd_fwd : (bwd ⨟ fwd) ≡ₜ Term.id (G.app C)
  /-- The isomorphism commutes with the concatenation maps. -/
  rebr : (fwd ⨟ G.concatMap C) ≡ₜ F.concatMap C

namespace RIso

variable {C : Ty}

/-- The identity is such an isomorphism. -/
def refl (C : Ty) (F : TyF) : RIso C F F where
  fwd := Term.id (F.app C)
  bwd := Term.id (F.app C)
  fwd_bwd := PEq.comp_id _
  bwd_fwd := PEq.comp_id _
  rebr := PEq.id_comp _

/-- Such isomorphisms can be inverted. -/
def symm {F G : TyF} (e : RIso C F G) : RIso C G F where
  fwd := e.bwd
  bwd := e.fwd
  fwd_bwd := e.bwd_fwd
  bwd_fwd := e.fwd_bwd
  rebr := by
    calc (e.bwd ⨟ F.concatMap C)
        ≡ₜ (e.bwd ⨟ (e.fwd ⨟ G.concatMap C)) := PEq.compR _ (PEq.symm e.rebr)
      _ ≡ₜ ((e.bwd ⨟ e.fwd) ⨟ G.concatMap C) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (G.app C) ⨟ G.concatMap C) := PEq.compL _ e.bwd_fwd
      _ ≡ₜ G.concatMap C := PEq.id_comp _

/-- Such isomorphisms compose. -/
def trans {F G H : TyF} (e : RIso C F G) (e' : RIso C G H) : RIso C F H where
  fwd := e.fwd ⨟ e'.fwd
  bwd := e'.bwd ⨟ e.bwd
  fwd_bwd := by
    calc ((e.fwd ⨟ e'.fwd) ⨟ (e'.bwd ⨟ e.bwd))
        ≡ₜ (e.fwd ⨟ (e'.fwd ⨟ (e'.bwd ⨟ e.bwd))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (e.fwd ⨟ ((e'.fwd ⨟ e'.bwd) ⨟ e.bwd)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (e.fwd ⨟ (Term.id (G.app C) ⨟ e.bwd)) := PEq.compR _ (PEq.compL _ e'.fwd_bwd)
      _ ≡ₜ (e.fwd ⨟ e.bwd) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id (F.app C) := e.fwd_bwd
  bwd_fwd := by
    calc ((e'.bwd ⨟ e.bwd) ⨟ (e.fwd ⨟ e'.fwd))
        ≡ₜ (e'.bwd ⨟ (e.bwd ⨟ (e.fwd ⨟ e'.fwd))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (e'.bwd ⨟ ((e.bwd ⨟ e.fwd) ⨟ e'.fwd)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (e'.bwd ⨟ (Term.id (G.app C) ⨟ e'.fwd)) := PEq.compR _ (PEq.compL _ e.bwd_fwd)
      _ ≡ₜ (e'.bwd ⨟ e'.fwd) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id (H.app C) := e'.bwd_fwd
  rebr := by
    calc ((e.fwd ⨟ e'.fwd) ⨟ H.concatMap C)
        ≡ₜ (e.fwd ⨟ (e'.fwd ⨟ H.concatMap C)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (e.fwd ⨟ G.concatMap C) := PEq.compR _ e'.rebr
      _ ≡ₜ F.concatMap C := e.rebr

/-- Such isomorphisms are closed under products. -/
def prod {F₁ F₂ G₁ G₂ : TyF} (e₁ : RIso C F₁ G₁) (e₂ : RIso C F₂ G₂) :
    RIso C (.prod F₁ F₂) (.prod G₁ G₂) where
  fwd := Term.prodF e₁.fwd e₂.fwd
  bwd := Term.prodF e₁.bwd e₂.bwd
  fwd_bwd :=
    (PEq.prod_comp _ _ _ _).trans
      ((PEq.congr_prodF e₁.fwd_bwd e₂.fwd_bwd).trans (PEq.prod_id _ _))
  bwd_fwd :=
    (PEq.prod_comp _ _ _ _).trans
      ((PEq.congr_prodF e₁.bwd_fwd e₂.bwd_fwd).trans (PEq.prod_id _ _))
  rebr := by
    show (Term.prodF e₁.fwd e₂.fwd ⨟ (G₁.concatMap C ⊙ G₂.concatMap C)) ≡ₜ _
    calc (Term.prodF e₁.fwd e₂.fwd ⨟
            (Term.prodF (G₁.concatMap C) (G₂.concatMap C) ⨟ binconcat C))
        ≡ₜ ((Term.prodF e₁.fwd e₂.fwd ⨟
            Term.prodF (G₁.concatMap C) (G₂.concatMap C)) ⨟ binconcat C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.prodF (e₁.fwd ⨟ G₁.concatMap C) (e₂.fwd ⨟ G₂.concatMap C) ⨟ binconcat C) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (Term.prodF (F₁.concatMap C) (F₂.concatMap C) ⨟ binconcat C) :=
          PEq.compL _ (PEq.congr_prodF e₁.rebr e₂.rebr)

/-- Such isomorphisms are closed under co-products. -/
def sum {F₁ F₂ G₁ G₂ : TyF} (e₁ : RIso C F₁ G₁) (e₂ : RIso C F₂ G₂) :
    RIso C (.sum F₁ F₂) (.sum G₁ G₂) where
  fwd := Term.sumF e₁.fwd e₂.fwd
  bwd := Term.sumF e₁.bwd e₂.bwd
  fwd_bwd :=
    (PEq.sum_comp _ _ _ _).trans
      ((PEq.congr_sumF e₁.fwd_bwd e₂.fwd_bwd).trans (PEq.sum_id _ _))
  bwd_fwd :=
    (PEq.sum_comp _ _ _ _).trans
      ((PEq.congr_sumF e₁.bwd_fwd e₂.bwd_fwd).trans (PEq.sum_id _ _))
  rebr := by
    show (Term.sumF e₁.fwd e₂.fwd ⨟ either (G₁.concatMap C) (G₂.concatMap C)) ≡ₜ _
    exact (sumF_either _ _ _ _).trans (either_congr e₁.rebr e₂.rebr)

/-- Such isomorphisms are closed under the list constructor. -/
def list {F G : TyF} (e : RIso C F G) : RIso C (.list F) (.list G) where
  fwd := Term.listF e.fwd
  bwd := Term.listF e.bwd
  fwd_bwd := (PEq.list_comp _ _).trans ((PEq.congr_listF e.fwd_bwd).trans (PEq.list_id _))
  bwd_fwd := (PEq.list_comp _ _).trans ((PEq.congr_listF e.bwd_fwd).trans (PEq.list_id _))
  rebr := by
    show (Term.listF e.fwd ⨟ homT (G.concatMap C)) ≡ₜ homT (F.concatMap C)
    exact (PEq.symm (homT_precomp _ _)).trans (homT_congr e.rebr)

end RIso

/-! ### The atomic isomorphisms -/

/-- `cons` is an isomorphism commuting with the concatenation maps. -/
def consRIso (C : Ty) : RIso C (.sum .unit (.prod .param (.list .param))) (.list .param) where
  fwd := cons C
  bwd := uncons C
  fwd_bwd := PEq.cons_uncons C
  bwd_fwd := PEq.uncons_cons C
  rebr := by
    show (cons C ⨟ homT (pureT C)) ≡ₜ either (nilT C) (pureT C ⊙ homT (pureT C))
    have hhom : homT (pureT C) ≡ₜ Term.id C⋆ := homT_pureT C
    calc (cons C ⨟ homT (pureT C))
        ≡ₜ (cons C ⨟ Term.id C⋆) := PEq.compR _ hhom
      _ ≡ₜ cons C := PEq.comp_id _
      _ ≡ₜ (Term.id (Ty.unit ⊕' (C ⊗ C⋆)) ⨟ cons C) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ (either (inl Ty.unit (C ⊗ C⋆)) (inr Ty.unit (C ⊗ C⋆)) ⨟ cons C) :=
          PEq.compL _ (PEq.symm (either_inl_inr _ _))
      _ ≡ₜ either (inl Ty.unit (C ⊗ C⋆) ⨟ cons C) (inr Ty.unit (C ⊗ C⋆) ⨟ cons C) :=
          either_comp _ _ _
      _ ≡ₜ either (nilT C) (pureT C ⊙ homT (pureT C)) := by
          refine either_congr (PEq.refl _) ?_
          calc prepend C
              ≡ₜ (Term.prodF (pureT C) (Term.id C⋆) ⨟ binconcat C) := PEq.prepend_def C
            _ ≡ₜ (pureT C ⊙ homT (pureT C)) :=
                PEq.compL _ (PEq.congr_prodF (PEq.refl _) (PEq.symm hhom))

/-- `snoc` is an isomorphism commuting with the concatenation maps. -/
def snocRIso (C : Ty) : RIso C (.sum .unit (.prod (.list .param) .param)) (.list .param) where
  fwd := snoc C
  bwd := unsnoc C
  fwd_bwd := PEq.snoc_unsnoc C
  bwd_fwd := PEq.unsnoc_snoc C
  rebr := by
    show (snoc C ⨟ homT (pureT C)) ≡ₜ either (nilT C) (homT (pureT C) ⊙ pureT C)
    have hhom : homT (pureT C) ≡ₜ Term.id C⋆ := homT_pureT C
    calc (snoc C ⨟ homT (pureT C))
        ≡ₜ (snoc C ⨟ Term.id C⋆) := PEq.compR _ hhom
      _ ≡ₜ snoc C := PEq.comp_id _
      _ ≡ₜ (Term.id (Ty.unit ⊕' (C⋆ ⊗ C)) ⨟ snoc C) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ (either (inl Ty.unit (C⋆ ⊗ C)) (inr Ty.unit (C⋆ ⊗ C)) ⨟ snoc C) :=
          PEq.compL _ (PEq.symm (either_inl_inr _ _))
      _ ≡ₜ either (inl Ty.unit (C⋆ ⊗ C) ⨟ snoc C) (inr Ty.unit (C⋆ ⊗ C) ⨟ snoc C) :=
          either_comp _ _ _
      _ ≡ₜ either (nilT C) (homT (pureT C) ⊙ pureT C) := by
          refine either_congr (PEq.inl_snoc_cons C) ?_
          calc append C
              ≡ₜ (Term.prodF (Term.id C⋆) (pureT C) ⨟ binconcat C) := PEq.append_def C
            _ ≡ₜ (homT (pureT C) ⊙ pureT C) :=
                PEq.compL _ (PEq.congr_prodF (PEq.symm hhom) (PEq.refl _))

/-- Distributivity on the right. -/
def distRRIso (C : Ty) (F G H : TyF) :
    RIso C (.prod F (.sum G H)) (.sum (.prod F G) (.prod F H)) where
  fwd := distR (F.app C) (G.app C) (H.app C)
  bwd := undistR (F.app C) (G.app C) (H.app C)
  fwd_bwd := PEq.distR_undistR _ _ _
  bwd_fwd := PEq.undistR_distR _ _ _
  rebr := PEq.symm (fdot_either_distR _ _ _)

/-- Distributivity on the left. -/
def distLRIso (C : Ty) (F G H : TyF) :
    RIso C (.prod (.sum F G) H) (.sum (.prod F H) (.prod G H)) where
  fwd := distL (F.app C) (G.app C) (H.app C)
  bwd := undistL (F.app C) (G.app C) (H.app C)
  fwd_bwd := PEq.distL_undistL _ _ _
  bwd_fwd := PEq.undistL_distL _ _ _
  rebr := PEq.symm (fdot_either_distL _ _ _)

/-- Right associativity of products. -/
def assocRRIso (C : Ty) (F G H : TyF) :
    RIso C (.prod (.prod F G) H) (.prod F (.prod G H)) where
  fwd := assocR (F.app C) (G.app C) (H.app C)
  bwd := assocL (F.app C) (G.app C) (H.app C)
  fwd_bwd := PEq.assocR_assocL _ _ _
  bwd_fwd := PEq.assocL_assocR _ _ _
  rebr := PEq.symm (fdot_assoc _ _ _)

/-- The right unit. -/
def unitRRIso (C : Ty) (F : TyF) : RIso C F (.prod F .unit) where
  fwd := unitR (F.app C)
  bwd := fst (F.app C) Ty.unit
  fwd_bwd := PEq.unitR_fst _
  bwd_fwd := PEq.fst_unitR _
  rebr := by
    show (unitR (F.app C) ⨟ (F.concatMap C ⊙ nilT C)) ≡ₜ F.concatMap C
    calc (unitR (F.app C) ⨟ (F.concatMap C ⊙ nilT C))
        ≡ₜ (unitR (F.app C) ⨟ (fst (F.app C) Ty.unit ⨟ F.concatMap C)) :=
          PEq.compR _ (fdot_nil_right _)
      _ ≡ₜ ((unitR (F.app C) ⨟ fst (F.app C) Ty.unit) ⨟ F.concatMap C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (F.app C) ⨟ F.concatMap C) := PEq.compL _ (PEq.unitR_fst _)
      _ ≡ₜ F.concatMap C := PEq.id_comp _

/-- The left unit. -/
def unitLRIso (C : Ty) (F : TyF) : RIso C F (.prod .unit F) where
  fwd := unitL (F.app C)
  bwd := snd Ty.unit (F.app C)
  fwd_bwd := PEq.unitL_snd _
  bwd_fwd := PEq.snd_unitL _
  rebr := by
    show (unitL (F.app C) ⨟ (nilT C ⊙ F.concatMap C)) ≡ₜ F.concatMap C
    calc (unitL (F.app C) ⨟ (nilT C ⊙ F.concatMap C))
        ≡ₜ (unitL (F.app C) ⨟ (snd Ty.unit (F.app C) ⨟ F.concatMap C)) :=
          PEq.compR _ (fdot_nil_left _)
      _ ≡ₜ ((unitL (F.app C) ⨟ snd Ty.unit (F.app C)) ⨟ F.concatMap C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (F.app C) ⨟ F.concatMap C) := PEq.compL _ (PEq.unitL_snd _)
      _ ≡ₜ F.concatMap C := PEq.id_comp _

/-- Associativity of co-products, as a term. -/
def sumAssocT (X Y Z : Ty) : Term ((X ⊕' Y) ⊕' Z) (X ⊕' (Y ⊕' Z)) :=
  either (sumF (Term.id X) (inl Y Z)) (inr Y Z ⨟ inr X (Y ⊕' Z))

/-- The inverse of `sumAssocT`. -/
def sumUnassocT (X Y Z : Ty) : Term (X ⊕' (Y ⊕' Z)) ((X ⊕' Y) ⊕' Z) :=
  either (inl X Y ⨟ inl (X ⊕' Y) Z)
    (either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z))

/-- Associativity of co-products. -/
def sumAssocRIso (C : Ty) (F G H : TyF) :
    RIso C (.sum (.sum F G) H) (.sum F (.sum G H)) where
  fwd := sumAssocT (F.app C) (G.app C) (H.app C)
  bwd := sumUnassocT (F.app C) (G.app C) (H.app C)
  fwd_bwd := by
    set X := F.app C
    set Y := G.app C
    set Z := H.app C
    refine either_ext _ _ ?_ ?_
    · refine either_ext _ _ ?_ ?_
      · calc (inl X Y ⨟ (inl (X ⊕' Y) Z ⨟ (sumAssocT X Y Z ⨟ sumUnassocT X Y Z)))
            ≡ₜ ((inl X Y ⨟ inl (X ⊕' Y) Z) ⨟ (sumAssocT X Y Z ⨟ sumUnassocT X Y Z)) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (((inl X Y ⨟ inl (X ⊕' Y) Z) ⨟ sumAssocT X Y Z) ⨟ sumUnassocT X Y Z) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inl X Y ⨟ (inl (X ⊕' Y) Z ⨟ sumAssocT X Y Z)) ⨟ sumUnassocT X Y Z) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inl X Y ⨟ sumF (Term.id X) (inl Y Z)) ⨟ sumUnassocT X Y Z) :=
              PEq.compL _ (PEq.compR _ (inl_either _ _))
          _ ≡ₜ ((Term.id X ⨟ inl X (Y ⊕' Z)) ⨟ sumUnassocT X Y Z) :=
              PEq.compL _ (PEq.nat_inl _ _)
          _ ≡ₜ (inl X (Y ⊕' Z) ⨟ sumUnassocT X Y Z) := PEq.compL _ (PEq.id_comp _)
          _ ≡ₜ (inl X Y ⨟ inl (X ⊕' Y) Z) := inl_either _ _
          _ ≡ₜ (inl X Y ⨟ (inl (X ⊕' Y) Z ⨟ Term.id ((X ⊕' Y) ⊕' Z))) :=
              PEq.compR _ (PEq.symm (PEq.comp_id _))
      · calc (inr X Y ⨟ (inl (X ⊕' Y) Z ⨟ (sumAssocT X Y Z ⨟ sumUnassocT X Y Z)))
            ≡ₜ (inr X Y ⨟ ((inl (X ⊕' Y) Z ⨟ sumAssocT X Y Z) ⨟ sumUnassocT X Y Z)) :=
              PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (inr X Y ⨟ (sumF (Term.id X) (inl Y Z) ⨟ sumUnassocT X Y Z)) :=
              PEq.compR _ (PEq.compL _ (inl_either _ _))
          _ ≡ₜ ((inr X Y ⨟ sumF (Term.id X) (inl Y Z)) ⨟ sumUnassocT X Y Z) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inl Y Z ⨟ inr X (Y ⊕' Z)) ⨟ sumUnassocT X Y Z) :=
              PEq.compL _ (PEq.nat_inr _ _)
          _ ≡ₜ (inl Y Z ⨟ (inr X (Y ⊕' Z) ⨟ sumUnassocT X Y Z)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (inl Y Z ⨟ either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z)) :=
              PEq.compR _ (inr_either _ _)
          _ ≡ₜ (inr X Y ⨟ inl (X ⊕' Y) Z) := inl_either _ _
          _ ≡ₜ (inr X Y ⨟ (inl (X ⊕' Y) Z ⨟ Term.id ((X ⊕' Y) ⊕' Z))) :=
              PEq.compR _ (PEq.symm (PEq.comp_id _))
    · calc (inr (X ⊕' Y) Z ⨟ (sumAssocT X Y Z ⨟ sumUnassocT X Y Z))
          ≡ₜ ((inr (X ⊕' Y) Z ⨟ sumAssocT X Y Z) ⨟ sumUnassocT X Y Z) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inr Y Z ⨟ inr X (Y ⊕' Z)) ⨟ sumUnassocT X Y Z) :=
            PEq.compL _ (inr_either _ _)
        _ ≡ₜ (inr Y Z ⨟ (inr X (Y ⊕' Z) ⨟ sumUnassocT X Y Z)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (inr Y Z ⨟ either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z)) :=
            PEq.compR _ (inr_either _ _)
        _ ≡ₜ inr (X ⊕' Y) Z := inr_either _ _
        _ ≡ₜ (inr (X ⊕' Y) Z ⨟ Term.id ((X ⊕' Y) ⊕' Z)) := PEq.symm (PEq.comp_id _)
  bwd_fwd := by
    set X := F.app C
    set Y := G.app C
    set Z := H.app C
    refine either_ext _ _ ?_ ?_
    · calc (inl X (Y ⊕' Z) ⨟ (sumUnassocT X Y Z ⨟ sumAssocT X Y Z))
          ≡ₜ ((inl X (Y ⊕' Z) ⨟ sumUnassocT X Y Z) ⨟ sumAssocT X Y Z) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inl X Y ⨟ inl (X ⊕' Y) Z) ⨟ sumAssocT X Y Z) :=
            PEq.compL _ (inl_either _ _)
        _ ≡ₜ (inl X Y ⨟ (inl (X ⊕' Y) Z ⨟ sumAssocT X Y Z)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (inl X Y ⨟ sumF (Term.id X) (inl Y Z)) := PEq.compR _ (inl_either _ _)
        _ ≡ₜ (Term.id X ⨟ inl X (Y ⊕' Z)) := PEq.nat_inl _ _
        _ ≡ₜ inl X (Y ⊕' Z) := PEq.id_comp _
        _ ≡ₜ (inl X (Y ⊕' Z) ⨟ Term.id (X ⊕' (Y ⊕' Z))) := PEq.symm (PEq.comp_id _)
    · refine either_ext _ _ ?_ ?_
      · calc (inl Y Z ⨟ (inr X (Y ⊕' Z) ⨟ (sumUnassocT X Y Z ⨟ sumAssocT X Y Z)))
            ≡ₜ (inl Y Z ⨟ ((inr X (Y ⊕' Z) ⨟ sumUnassocT X Y Z) ⨟ sumAssocT X Y Z)) :=
              PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (inl Y Z ⨟ (either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z) ⨟
                sumAssocT X Y Z)) := PEq.compR _ (PEq.compL _ (inr_either _ _))
          _ ≡ₜ ((inl Y Z ⨟ either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z)) ⨟
                sumAssocT X Y Z) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inr X Y ⨟ inl (X ⊕' Y) Z) ⨟ sumAssocT X Y Z) :=
              PEq.compL _ (inl_either _ _)
          _ ≡ₜ (inr X Y ⨟ (inl (X ⊕' Y) Z ⨟ sumAssocT X Y Z)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (inr X Y ⨟ sumF (Term.id X) (inl Y Z)) := PEq.compR _ (inl_either _ _)
          _ ≡ₜ (inl Y Z ⨟ inr X (Y ⊕' Z)) := PEq.nat_inr _ _
          _ ≡ₜ (inl Y Z ⨟ (inr X (Y ⊕' Z) ⨟ Term.id (X ⊕' (Y ⊕' Z)))) :=
              PEq.compR _ (PEq.symm (PEq.comp_id _))
      · calc (inr Y Z ⨟ (inr X (Y ⊕' Z) ⨟ (sumUnassocT X Y Z ⨟ sumAssocT X Y Z)))
            ≡ₜ (inr Y Z ⨟ ((inr X (Y ⊕' Z) ⨟ sumUnassocT X Y Z) ⨟ sumAssocT X Y Z)) :=
              PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (inr Y Z ⨟ (either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z) ⨟
                sumAssocT X Y Z)) := PEq.compR _ (PEq.compL _ (inr_either _ _))
          _ ≡ₜ ((inr Y Z ⨟ either (inr X Y ⨟ inl (X ⊕' Y) Z) (inr (X ⊕' Y) Z)) ⨟
                sumAssocT X Y Z) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (inr (X ⊕' Y) Z ⨟ sumAssocT X Y Z) := PEq.compL _ (inr_either _ _)
          _ ≡ₜ (inr Y Z ⨟ inr X (Y ⊕' Z)) := inr_either _ _
          _ ≡ₜ (inr Y Z ⨟ (inr X (Y ⊕' Z) ⨟ Term.id (X ⊕' (Y ⊕' Z)))) :=
              PEq.compR _ (PEq.symm (PEq.comp_id _))
  rebr := by
    set X := F.app C
    set Y := G.app C
    set Z := H.app C
    show (sumAssocT X Y Z ⨟
        either (F.concatMap C) (either (G.concatMap C) (H.concatMap C))) ≡ₜ
      either (either (F.concatMap C) (G.concatMap C)) (H.concatMap C)
    set cF := F.concatMap C
    set cG := G.concatMap C
    set cH := H.concatMap C
    calc (either (sumF (Term.id X) (inl Y Z)) (inr Y Z ⨟ inr X (Y ⊕' Z)) ⨟
            either cF (either cG cH))
        ≡ₜ either (sumF (Term.id X) (inl Y Z) ⨟ either cF (either cG cH))
            ((inr Y Z ⨟ inr X (Y ⊕' Z)) ⨟ either cF (either cG cH)) := either_comp _ _ _
      _ ≡ₜ either (either cF cG) cH := by
          refine either_congr ?_ ?_
          · calc (sumF (Term.id X) (inl Y Z) ⨟ either cF (either cG cH))
                ≡ₜ either (Term.id X ⨟ cF) (inl Y Z ⨟ either cG cH) := sumF_either _ _ _ _
              _ ≡ₜ either cF cG := either_congr (PEq.id_comp _) (inl_either _ _)
          · calc ((inr Y Z ⨟ inr X (Y ⊕' Z)) ⨟ either cF (either cG cH))
                ≡ₜ (inr Y Z ⨟ (inr X (Y ⊕' Z) ⨟ either cF (either cG cH))) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ (inr Y Z ⨟ either cG cH) := PEq.compR _ (inr_either _ _)
              _ ≡ₜ cH := inr_either _ _

/-! ### The isomorphisms built by induction -/

/-- Appending one more factor to a power: `Cᵐ × C ≅ C^{m+1}`. -/
def powSnocRIso (C : Ty) : (m : ℕ) → RIso C (.prod (TyF.pow m) .param) (TyF.pow (m + 1))
  | 0 => ((unitLRIso C .param).symm).trans (unitRRIso C .param)
  | (m + 1) =>
      (assocRRIso C .param (TyF.pow m) .param).trans
        (RIso.prod (RIso.refl C .param) (powSnocRIso C m))

/-- The isomorphism that collects a list of length at most `m + 2`: a list is empty, or a
single letter, or a letter, a list of length at most `m`, and a letter. -/
def lengthRIso (C : Ty) : (m : ℕ) →
    RIso C (.sum .unit (.sum (.prod .param .unit) (.prod .param (.prod (TyF.lt m) .param))))
      (TyF.lt (m + 2))
  | 0 =>
      ((sumAssocRIso C .unit (.prod .param .unit)
          (.prod .param (.prod (TyF.lt 0) .param))).symm).trans
        (RIso.sum (RIso.refl C (TyF.lt 1))
          (RIso.prod (RIso.refl C .param) (powSnocRIso C 0)))
  | (m + 1) =>
      -- distribute the co-product `Cᵐ⁺¹ + (C⁰ + ⋯ + Cᵐ)` out of the middle component
      (RIso.sum (RIso.refl C .unit)
        (RIso.sum (RIso.refl C (.prod .param .unit))
          ((RIso.prod (RIso.refl C .param)
              (distLRIso C (TyF.lt m) (TyF.pow (m + 1)) .param)).trans
            (distRRIso C .param (.prod (TyF.lt m) .param)
              (.prod (TyF.pow (m + 1)) .param))))).trans
      (((RIso.sum (RIso.refl C .unit)
          ((sumAssocRIso C (.prod .param .unit)
            (.prod .param (.prod (TyF.lt m) .param))
            (.prod .param (.prod (TyF.pow (m + 1)) .param))).symm)).trans
        ((sumAssocRIso C .unit
            (.sum (.prod .param .unit) (.prod .param (.prod (TyF.lt m) .param)))
            (.prod .param (.prod (TyF.pow (m + 1)) .param))).symm)).trans
        (RIso.sum (lengthRIso C m)
          (RIso.prod (RIso.refl C .param) (powSnocRIso C (m + 1)))))

/-- The shape of the second summand of the statement: `C^{k+1} × C* × C^{k+1}`. -/
def midShape (k : ℕ) : TyF :=
  .prod (.prod (TyF.pow (k + 1)) (.list .param)) (TyF.pow (k + 1))

/-- One letter on each side of a middle shape gives the middle shape for `k+1`. -/
def midStepRIso (C : Ty) (k : ℕ) :
    RIso C (.prod .param (.prod (midShape k) .param)) (midShape (k + 1)) :=
  (RIso.prod (RIso.refl C .param)
      ((assocRRIso C (.prod (TyF.pow (k + 1)) (.list .param)) (TyF.pow (k + 1)) .param).trans
        (RIso.prod (RIso.refl C (.prod (TyF.pow (k + 1)) (.list .param)))
          (powSnocRIso C (k + 1))))).trans
    (((assocRRIso C .param (.prod (TyF.pow (k + 1)) (.list .param))
        (TyF.pow (k + 2))).symm).trans
      (RIso.prod
        ((assocRRIso C .param (TyF.pow (k + 1)) (.list .param)).symm)
        (RIso.refl C (TyF.pow (k + 2)))))

/-- The shape of the statement: lists of length at most `2k+1`, or a prefix of length `k+1`,
a middle part and a suffix of length `k+1`. -/
def fixedShape (k : ℕ) : TyF := .sum (TyF.lt (2 * k + 1)) (midShape k)

/-- The first three steps of the decomposition of a list: remove the first letter, remove the
last letter of the rest, and distribute. -/
def peelRIso (C : Ty) :
    RIso C (.list .param)
      (.sum .unit (.sum (.prod .param .unit)
        (.prod .param (.prod (.list .param) .param)))) :=
  ((consRIso C).symm).trans
    ((RIso.sum (RIso.refl C .unit)
        (RIso.prod (RIso.refl C .param) ((snocRIso C).symm))).trans
      (RIso.sum (RIso.refl C .unit)
        (distRRIso C .param .unit (.prod (.list .param) .param))))

/-- **Lemma (fixed lengths extracted)**, as an isomorphism of shapes: a list either has
length at most `2k+1`, or splits into a prefix of length `k+1`, a middle part, and a suffix
of length `k+1`. -/
def fixedRIso (C : Ty) : (k : ℕ) → RIso C (.list .param) (fixedShape k)
  | 0 =>
      (peelRIso C).trans
        (((sumAssocRIso C .unit (.prod .param .unit)
            (.prod .param (.prod (.list .param) .param))).symm).trans
          (RIso.sum (RIso.refl C (TyF.lt 1))
            (((assocRRIso C .param (.list .param) .param).symm).trans
              (RIso.prod
                (RIso.prod (unitRRIso C .param) (RIso.refl C (.list .param)))
                (unitRRIso C .param)))))
  | (k + 1) => by
      have hk : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
      rw [fixedShape, hk]
      refine (peelRIso C).trans ?_
      -- decompose the middle part according to the induction hypothesis
      refine (RIso.sum (RIso.refl C .unit)
        (RIso.sum (RIso.refl C (.prod .param .unit))
          (RIso.prod (RIso.refl C .param)
            (RIso.prod (fixedRIso C k) (RIso.refl C .param))))).trans ?_
      -- distribute the two cases of the induction hypothesis out of the middle
      refine (RIso.sum (RIso.refl C .unit)
        (RIso.sum (RIso.refl C (.prod .param .unit))
          ((RIso.prod (RIso.refl C .param)
              (distLRIso C (TyF.lt (2 * k + 1)) (midShape k) .param)).trans
            (distRRIso C .param (.prod (TyF.lt (2 * k + 1)) .param)
              (.prod (midShape k) .param))))).trans ?_
      -- reassociate the co-products and use the two isomorphisms for the two cases
      refine ((RIso.sum (RIso.refl C .unit)
        ((sumAssocRIso C (.prod .param .unit)
          (.prod .param (.prod (TyF.lt (2 * k + 1)) .param))
          (.prod .param (.prod (midShape k) .param))).symm)).trans
        ((sumAssocRIso C .unit
            (.sum (.prod .param .unit)
              (.prod .param (.prod (TyF.lt (2 * k + 1)) .param)))
            (.prod .param (.prod (midShape k) .param))).symm)).trans ?_
      exact RIso.sum (lengthRIso C (2 * k + 1)) (midStepRIso C k)

/-- **Lemma (fixed lengths extracted)** (appendix, proof of Lemma 6.4).  For every type `C`
and every `k`, the concatenation map
`(C⁰ + ⋯ + C^{2k+1}) + C^{k+1} × C* × C^{k+1} ↣ C*` is a provable isomorphism. -/
theorem concatMap_fixedShape_iso (C : Ty) (k : ℕ) :
    ProvableIso (TyF.concatMap (fixedShape k) C) := by
  set e := (fixedRIso C k).symm with he
  have hlist : TyF.concatMap (.list (TyF.param)) C ≡ₜ Term.id C⋆ := homT_pureT C
  have hc : TyF.concatMap (fixedShape k) C ≡ₜ e.fwd := by
    calc TyF.concatMap (fixedShape k) C
        ≡ₜ (e.fwd ⨟ TyF.concatMap (.list (TyF.param)) C) := PEq.symm e.rebr
      _ ≡ₜ (e.fwd ⨟ Term.id C⋆) := PEq.compR _ hlist
      _ ≡ₜ e.fwd := PEq.comp_id _
  refine ⟨e.bwd, ?_, ?_⟩
  · exact ((PEq.compL _ hc).trans e.fwd_bwd)
  · exact ((PEq.compR _ hc).trans e.bwd_fwd)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
