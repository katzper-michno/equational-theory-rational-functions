import Lax149335Proofs.Appendix.Drops.SumSplitShape

/-!
# Split collectors (appendix, *Proof of Exchange Lemma*, case *Split*)

The case *Split* of the exchange lemma asks for a lift-drop factorisation of `f ; split`,
where `f : A ⇒ (S+T)*` is a drop.  Since `split` and `unsplit` are mutually inverse (Axiom
4), such a factorisation exists as soon as `f` itself factors as *lift ; drop ; unsplit*:
composing that factorisation with `split` cancels the `unsplit`.  This is the property
`Lax149335Proofs.SplitColl` of this file, which the case *Split* has to establish for every drop
`f`; `Lax149335Proofs.Appendix.Drops.SplitExchange` does so.

The content of the co-domain `S* × (T × S*)*` of `split` is read off by `unsplit`, which is
the concatenation map of the functor `S* × (T × S*)*`: it is the concatenation of the word
`Lax149335Proofs.Term.sWord` of the letters of `S` and of the list `Lax149335Proofs.Term.zWord` of the
blocks `t s*` (`Lax149335Proofs.Term.zBlock`).

This file sets up those notions, proves the closure properties of `Lax149335Proofs.SplitColl` that
do not need the exchange lemma (co-pairing and pre-composition with a lift), and treats the
three shapes of leaves of a drop in normal form with list codomain: a constant
(`Lax149335Proofs.splitColl_const`, through the normalisation of values), a singleton
(`Lax149335Proofs.splitColl_sing`, through the sum normalisation lemma) and a homomorphic image
(`Lax149335Proofs.splitColl_map`, through the split shape of a drop with co-product codomain and
the naturality of `split`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

/-- The type `T × S*` of the blocks of the co-domain of `split`. -/
abbrev ZTy (S T : Ty) : Ty := T ⊗ S⋆

/-- The co-domain `S* × (T × S*)*` of `split`. -/
abbrev splitCod (S T : Ty) : Ty := S⋆ ⊗ (ZTy S T)⋆

namespace Term

/-- The content of a word of letters of `S`. -/
def sWord (S T : Ty) : Term (S⋆) ((S ⊕' T)⋆) := homT (sLetter S T)

/-- The content of one block `t s*`. -/
def zBlock (S T : Ty) : Term (ZTy S T) ((S ⊕' T)⋆) := tLetter S T ⊙ sWord S T

/-- The content of a list of blocks `(t s*)*`. -/
def zWord (S T : Ty) : Term ((ZTy S T)⋆) ((S ⊕' T)⋆) := homT (zBlock S T)

theorem prodF_unsplit {X Y : Ty} (x : Term X (S⋆)) (y : Term Y ((ZTy S T)⋆)) :
    (prodF x y ⨟ Term.unsplit S T) ≡ₜ ((x ⨟ sWord S T) ⊙ (y ⨟ zWord S T)) :=
  fdot_precomp _ _ _ _

/-- The content of a one-block list. -/
theorem pureT_zWord : (pureT (ZTy S T) ⨟ zWord S T) ≡ₜ zBlock S T := homT_pure _

/-- The content of a one-letter word. -/
theorem pureT_sWord : (pureT S ⨟ sWord S T) ≡ₜ sLetter S T := homT_pure _

/-- The empty word has empty content. -/
theorem nilT_sWord : (nilT S ⨟ sWord S T) ≡ₜ nilT (S ⊕' T) := homT_nil _

/-- The empty list of blocks has empty content. -/
theorem nilT_zWord : (nilT (ZTy S T) ⨟ zWord S T) ≡ₜ nilT (S ⊕' T) := homT_nil _

/-- The homomorphic image of a singleton is the functorial image. -/
theorem homT_pure_comp {A B : Ty} (k : Term A B) : homT (k ⨟ pureT B) ≡ₜ listF k :=
  (homT_precomp k (pureT B)).trans ((PEq.compR _ (homT_pureT B)).trans (PEq.comp_id _))

/-- The content of a word of letters of `S` is the letterwise image. -/
theorem sWord_eq (S T : Ty) : sWord S T ≡ₜ listF (inl S T) := homT_pure_comp _

/-- The content of a word of letters of `T` is the letterwise image. -/
theorem homT_tLetter (S T : Ty) : homT (tLetter S T) ≡ₜ listF (inr S T) := homT_pure_comp _

end Term

/-- **The content of a split collector.**  A term `c : A ⇒ (S+T)*` is *split-collectable* if
it is provably equal to a lift followed by a drop into the co-domain `S* × (T × S*)*` of
`split`, followed by `unsplit`. -/
def SplitColl (S T : Ty) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (D : Ty) (beta : Term A D) (q : Term D (splitCod S T)),
    IsLift beta ∧ IsEqDrop q ∧ (beta ⨟ (q ⨟ Term.unsplit S T)) ≡ₜ c

namespace SplitColl

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : SplitColl S T c') :
    SplitColl S T c := by
  obtain ⟨D, beta, q, hb, hq, he⟩ := hc
  exact ⟨D, beta, q, hb, hq, he.trans (PEq.symm h)⟩

theorem lift_comp {A A' : Ty} {gamma : Term A' A} (hg : IsLift gamma)
    {c : Term A ((S ⊕' T)⋆)} (hc : SplitColl S T c) : SplitColl S T (gamma ⨟ c) := by
  obtain ⟨D, beta, q, hb, hq, he⟩ := hc
  exact ⟨D, gamma ⨟ beta, q, IsLift.comp hg hb, hq,
    (PEq.comp_assoc _ _ _).trans (PEq.compR _ he)⟩

theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitColl S T c₁) (h₂ : SplitColl S T c₂) :
    SplitColl S T (Term.either c₁ c₂) := by
  obtain ⟨D₁, b₁, q₁, hb₁, hq₁, he₁⟩ := h₁
  obtain ⟨D₂, b₂, q₂, hb₂, hq₂, he₂⟩ := h₂
  refine ⟨D₁ ⊕' D₂, sumF b₁ b₂, Term.either q₁ q₂, IsLift.sumF hb₁ hb₂,
    hq₁.either hq₂, ?_⟩
  calc (sumF b₁ b₂ ⨟ (Term.either q₁ q₂ ⨟ Term.unsplit S T))
      ≡ₜ (sumF b₁ b₂ ⨟ Term.either (q₁ ⨟ Term.unsplit S T) (q₂ ⨟ Term.unsplit S T)) :=
        PEq.compR _ (Term.either_comp _ _ _)
    _ ≡ₜ Term.either (b₁ ⨟ (q₁ ⨟ Term.unsplit S T)) (b₂ ⨟ (q₂ ⨟ Term.unsplit S T)) :=
        Term.sumF_either _ _ _ _
    _ ≡ₜ Term.either c₁ c₂ := Term.either_congr he₁ he₂

/-- A word of letters of `S` is split-collectable. -/
theorem sword {X : Ty} {a : Term X (S⋆)} (ha : IsEqDrop a) :
    SplitColl S T (a ⨟ Term.sWord S T) := by
  refine ⟨X ⊗ Ty.unit, Term.unitR X, prodF a (nilT (ZTy S T)), IsLift.unitR X,
    ha.prodF (isEqDrop_nilT (ZTy S T)), ?_⟩
  calc (Term.unitR X ⨟ (prodF a (nilT (ZTy S T)) ⨟ Term.unsplit S T))
      ≡ₜ (Term.unitR X ⨟ ((a ⨟ Term.sWord S T) ⊙ (nilT (ZTy S T) ⨟ Term.zWord S T))) :=
        PEq.compR _ (Term.prodF_unsplit _ _)
    _ ≡ₜ (Term.unitR X ⨟ ((a ⨟ Term.sWord S T) ⊙ nilT (S ⊕' T))) :=
        PEq.compR _ (Term.fdot_congr (PEq.refl _) Term.nilT_zWord)
    _ ≡ₜ (Term.unitR X ⨟ (Term.fst X Ty.unit ⨟ (a ⨟ Term.sWord S T))) :=
        PEq.compR _ (Term.fdot_nil_right _)
    _ ≡ₜ ((Term.unitR X ⨟ Term.fst X Ty.unit) ⨟ (a ⨟ Term.sWord S T)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id X ⨟ (a ⨟ Term.sWord S T)) := PEq.compL _ (PEq.unitR_fst X)
    _ ≡ₜ (a ⨟ Term.sWord S T) := PEq.id_comp _

/-- A list of blocks is split-collectable. -/
theorem zword {Y : Ty} {m : Term Y ((ZTy S T)⋆)} (hm : IsEqDrop m) :
    SplitColl S T (m ⨟ Term.zWord S T) := by
  refine ⟨Ty.unit ⊗ Y, Term.unitL Y, prodF (nilT S) m, IsLift.unitL Y,
    (isEqDrop_nilT S).prodF hm, ?_⟩
  calc (Term.unitL Y ⨟ (prodF (nilT S) m ⨟ Term.unsplit S T))
      ≡ₜ (Term.unitL Y ⨟ ((nilT S ⨟ Term.sWord S T) ⊙ (m ⨟ Term.zWord S T))) :=
        PEq.compR _ (Term.prodF_unsplit _ _)
    _ ≡ₜ (Term.unitL Y ⨟ (nilT (S ⊕' T) ⊙ (m ⨟ Term.zWord S T))) :=
        PEq.compR _ (Term.fdot_congr Term.nilT_sWord (PEq.refl _))
    _ ≡ₜ (Term.unitL Y ⨟ (Term.snd Ty.unit Y ⨟ (m ⨟ Term.zWord S T))) :=
        PEq.compR _ (Term.fdot_nil_left _)
    _ ≡ₜ ((Term.unitL Y ⨟ Term.snd Ty.unit Y) ⨟ (m ⨟ Term.zWord S T)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id Y ⨟ (m ⨟ Term.zWord S T)) := PEq.compL _ (PEq.unitL_snd Y)
    _ ≡ₜ (m ⨟ Term.zWord S T) := PEq.id_comp _

/-- A single letter of `S` is split-collectable. -/
theorem sletter {X : Ty} {g : Term X S} (hg : IsEqDrop g) :
    SplitColl S T (g ⨟ sLetter S T) := by
  refine SplitColl.congr ?_ (SplitColl.sword (T := T) (hg.comp (IsEqDrop.of_isDrop (IsDrop.pureT S))))
  calc (g ⨟ sLetter S T)
      ≡ₜ (g ⨟ (pureT S ⨟ Term.sWord S T)) := PEq.compR _ (PEq.symm Term.pureT_sWord)
    _ ≡ₜ ((g ⨟ pureT S) ⨟ Term.sWord S T) := PEq.symm (PEq.comp_assoc _ _ _)

/-- A single letter of `T` is split-collectable. -/
theorem tletter {X : Ty} {g : Term X T} (hg : IsEqDrop g) :
    SplitColl S T (g ⨟ tLetter S T) := by
  have hm : IsEqDrop (prodF g (nilT S) ⨟ pureT (ZTy S T)) :=
    (hg.prodF (isEqDrop_nilT S)).comp (IsEqDrop.of_isDrop (IsDrop.pureT _))
  have hc : ((prodF g (nilT S) ⨟ pureT (ZTy S T)) ⨟ Term.zWord S T) ≡ₜ
      (Term.fst X Ty.unit ⨟ (g ⨟ tLetter S T)) := by
    calc ((prodF g (nilT S) ⨟ pureT (ZTy S T)) ⨟ Term.zWord S T)
        ≡ₜ (prodF g (nilT S) ⨟ (pureT (ZTy S T) ⨟ Term.zWord S T)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF g (nilT S) ⨟ Term.zBlock S T) := PEq.compR _ Term.pureT_zWord
      _ ≡ₜ ((g ⨟ tLetter S T) ⊙ (nilT S ⨟ Term.sWord S T)) := Term.fdot_precomp _ _ _ _
      _ ≡ₜ ((g ⨟ tLetter S T) ⊙ nilT (S ⊕' T)) :=
          Term.fdot_congr (PEq.refl _) Term.nilT_sWord
      _ ≡ₜ (Term.fst X Ty.unit ⨟ (g ⨟ tLetter S T)) := Term.fdot_nil_right _
  have h1 : SplitColl S T (Term.fst X Ty.unit ⨟ (g ⨟ tLetter S T)) :=
    SplitColl.congr (PEq.symm hc) (SplitColl.zword hm)
  refine SplitColl.congr ?_ (SplitColl.lift_comp (IsLift.unitR X) h1)
  calc (g ⨟ tLetter S T)
      ≡ₜ (Term.id X ⨟ (g ⨟ tLetter S T)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((Term.unitR X ⨟ Term.fst X Ty.unit) ⨟ (g ⨟ tLetter S T)) :=
        PEq.compL _ (PEq.symm (PEq.unitR_fst X))
    _ ≡ₜ (Term.unitR X ⨟ (Term.fst X Ty.unit ⨟ (g ⨟ tLetter S T))) := PEq.comp_assoc _ _ _

end SplitColl

/-! ### The leaves of a normal drop with list codomain -/

/-- A singleton whose entry is a normal case tree is split-collectable. -/
theorem splitColl_normalSumTree_pure {r : ℕ} : {A B₁ B₂ : Ty} → {t : Term A (B₁ ⊕' B₂)} →
    IsNormalSumTree r t → SplitColl B₁ B₂ (t ⨟ pureT (B₁ ⊕' B₂)) := by
  intro A B₁ B₂ t ht
  induction ht with
  | @inl X _ _ h hh _ =>
      exact SplitColl.congr (PEq.comp_assoc _ _ _)
        (SplitColl.sletter (IsEqDrop.of_isDrop hh))
  | @inr X _ _ h hh _ =>
      exact SplitColl.congr (PEq.comp_assoc _ _ _)
        (SplitColl.tletter (IsEqDrop.of_isDrop hh))
  | @sumF X₁ X₂ _ _ h₁ h₂ hh₁ hh₂ _ _ =>
      refine SplitColl.congr ?_
        ((SplitColl.congr (PEq.comp_assoc _ _ _)
            (SplitColl.sletter (IsEqDrop.of_isDrop hh₁))).either
          (SplitColl.congr (PEq.comp_assoc _ _ _)
            (SplitColl.tletter (IsEqDrop.of_isDrop hh₂))))
      exact (PEq.compL _ (Term.sumF_as_either h₁ h₂)).trans (Term.either_comp _ _ _)
  | either _ _ ih₁ ih₂ =>
      exact SplitColl.congr (Term.either_comp _ _ _) (ih₁.either ih₂)

/-- **A singleton leaf is split-collectable.** -/
theorem splitColl_sing {A : Ty} {g : Term A (S ⊕' T)} (hg : IsDrop g) :
    SplitColl S T (g ⨟ pureT (S ⊕' T)) := by
  obtain ⟨D, alpha, t, ha, -, ht, he⟩ := drops_with_sum_codomain_tree g hg
  refine SplitColl.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact SplitColl.lift_comp ha (splitColl_normalSumTree_pure ht)

/-- **A constant leaf is split-collectable**: the constant `1 ; v` is collected by the
constant whose value is the split of `v`. -/
theorem splitColl_const (A : Ty) (v : Value ((S ⊕' T)⋆)) :
    SplitColl S T (toUnit A ⨟ v) := by
  refine ⟨A, Term.id A,
    toUnit A ⨟ encV (splitCod S T) (splitDen (v.den ())), IsLift.id A,
    IsEqDrop.of_isDrop (IsDrop.bangV A _), ?_⟩
  have hv : v ≡ₜ encV ((S ⊕' T)⋆) (v.den ()) :=
    (PEq.symm (PEq.id_comp v)).trans (computes v ())
  have hw : (encV (splitCod S T) (splitDen (v.den ())) ⨟ Term.unsplit S T) ≡ₜ
      encV ((S ⊕' T)⋆) (v.den ()) := by
    refine (computes (Term.unsplit S T) (splitDen (v.den ()))).trans ?_
    rw [den_unsplit, unsplitDen_splitDen]
    exact PEq.refl _
  calc (Term.id A ⨟ ((toUnit A ⨟ encV (splitCod S T) (splitDen (v.den ()))) ⨟
          Term.unsplit S T))
      ≡ₜ ((toUnit A ⨟ encV (splitCod S T) (splitDen (v.den ()))) ⨟ Term.unsplit S T) :=
        PEq.id_comp _
    _ ≡ₜ (toUnit A ⨟ (encV (splitCod S T) (splitDen (v.den ())) ⨟ Term.unsplit S T)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (toUnit A ⨟ encV ((S ⊕' T)⋆) (v.den ())) := PEq.compR _ hw
    _ ≡ₜ (toUnit A ⨟ v) := PEq.compR _ (PEq.symm hv)

/-- **A homomorphic-image leaf is split-collectable.** -/
theorem splitColl_map {A : Ty} {g : Term A (S ⊕' T)} (hg : IsDrop g) :
    SplitColl S T (listF g) := by
  obtain ⟨D, alpha, t, ha, hshape, he⟩ := sumSplitShape_of_drop hg
  refine SplitColl.congr ((PEq.congr_listF he).trans (PEq.symm (PEq.list_comp _ _))) ?_
  refine SplitColl.lift_comp (IsLift.listF ha) ?_
  clear he hg alpha ha
  cases hshape with
  | @left h hh he =>
      refine SplitColl.congr ?_ (SplitColl.sword (IsEqDrop.of_isDrop (IsDrop.listF hh)))
      calc listF t
          ≡ₜ listF (h ⨟ inl S T) := PEq.congr_listF he
        _ ≡ₜ (listF h ⨟ listF (inl S T)) := PEq.symm (PEq.list_comp _ _)
        _ ≡ₜ (listF h ⨟ Term.sWord S T) := PEq.compR _ (PEq.symm (Term.sWord_eq S T))
  | @right h hh he =>
      have hm : IsEqDrop (listF (prodF h (nilT S))) :=
        IsEqDrop.listF ((IsEqDrop.of_isDrop hh).prodF (isEqDrop_nilT S))
      have hc : (listF (prodF h (nilT S)) ⨟ Term.zWord S T) ≡ₜ
          (listF (Term.fst _ Ty.unit) ⨟ listF (h ⨟ inr S T)) := by
        calc (listF (prodF h (nilT S)) ⨟ Term.zWord S T)
            ≡ₜ homT (prodF h (nilT S) ⨟ Term.zBlock S T) := PEq.symm (homT_precomp _ _)
          _ ≡ₜ homT (Term.fst _ Ty.unit ⨟ (h ⨟ tLetter S T)) := by
              refine homT_congr ?_
              calc (prodF h (nilT S) ⨟ Term.zBlock S T)
                  ≡ₜ ((h ⨟ tLetter S T) ⊙ (nilT S ⨟ Term.sWord S T)) :=
                    Term.fdot_precomp _ _ _ _
                _ ≡ₜ ((h ⨟ tLetter S T) ⊙ nilT (S ⊕' T)) :=
                    Term.fdot_congr (PEq.refl _) Term.nilT_sWord
                _ ≡ₜ (Term.fst _ Ty.unit ⨟ (h ⨟ tLetter S T)) := Term.fdot_nil_right _
          _ ≡ₜ (listF (Term.fst _ Ty.unit) ⨟ homT (h ⨟ tLetter S T)) :=
              homT_precomp _ _
          _ ≡ₜ (listF (Term.fst _ Ty.unit) ⨟ (listF h ⨟ homT (tLetter S T))) :=
              PEq.compR _ (homT_precomp _ _)
          _ ≡ₜ (listF (Term.fst _ Ty.unit) ⨟ (listF h ⨟ listF (inr S T))) :=
              PEq.compR _ (PEq.compR _ (Term.homT_tLetter S T))
          _ ≡ₜ (listF (Term.fst _ Ty.unit) ⨟ listF (h ⨟ inr S T)) :=
              PEq.compR _ (PEq.list_comp _ _)
      have h1 : SplitColl S T (listF (Term.fst _ Ty.unit) ⨟ listF (h ⨟ inr S T)) :=
        SplitColl.congr (PEq.symm hc) (SplitColl.zword hm)
      refine SplitColl.congr ?_ (SplitColl.lift_comp (IsLift.listF (IsLift.unitR _)) h1)
      calc listF t
          ≡ₜ listF (h ⨟ inr S T) := PEq.congr_listF he
        _ ≡ₜ listF (Term.id _ ⨟ (h ⨟ inr S T)) := PEq.congr_listF (PEq.symm (PEq.id_comp _))
        _ ≡ₜ listF ((Term.unitR _ ⨟ Term.fst _ Ty.unit) ⨟ (h ⨟ inr S T)) :=
            PEq.congr_listF (PEq.compL _ (PEq.symm (PEq.unitR_fst _)))
        _ ≡ₜ (listF (Term.unitR _ ⨟ Term.fst _ Ty.unit) ⨟ listF (h ⨟ inr S T)) :=
            PEq.symm (PEq.list_comp _ _)
        _ ≡ₜ (listF (Term.unitR _) ⨟ (listF (Term.fst _ Ty.unit) ⨟ listF (h ⨟ inr S T))) :=
            (PEq.compL _ (PEq.symm (PEq.list_comp _ _))).trans (PEq.comp_assoc _ _ _)
  | @both A₁ A₂ b h₁ h₂ hb hh₁ hh₂ he =>
      have key : SplitColl S T (listF (sumF h₁ h₂)) := by
        refine ⟨splitCod A₁ A₂, Term.split A₁ A₂,
        prodF (listF h₁) (listF (prodF h₂ (listF h₁))), IsLift.split A₁ A₂,
        IsEqDrop.of_isDrop (IsDrop.prodF (IsDrop.listF hh₁)
          (IsDrop.listF (IsDrop.prodF hh₂ (IsDrop.listF hh₁)))), ?_⟩
        calc (Term.split A₁ A₂ ⨟ (prodF (listF h₁) (listF (prodF h₂ (listF h₁))) ⨟
                Term.unsplit S T))
            ≡ₜ ((Term.split A₁ A₂ ⨟ prodF (listF h₁) (listF (prodF h₂ (listF h₁)))) ⨟
                Term.unsplit S T) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((listF (sumF h₁ h₂) ⨟ Term.split S T) ⨟ Term.unsplit S T) :=
              PEq.compL _ (PEq.symm (PEq.nat_split h₁ h₂))
          _ ≡ₜ (listF (sumF h₁ h₂) ⨟ (Term.split S T ⨟ Term.unsplit S T)) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ (listF (sumF h₁ h₂) ⨟ Term.id ((S ⊕' T)⋆)) :=
              PEq.compR _ (PEq.split_unsplit S T)
          _ ≡ₜ listF (sumF h₁ h₂) := PEq.comp_id _
      exact SplitColl.congr ((PEq.congr_listF he).trans (PEq.symm (PEq.list_comp _ _)))
        (SplitColl.lift_comp (IsLift.listF hb) key)

/-- **Every leaf of a normal form with codomain `(S+T)*` is split-collectable.** -/
theorem splitColl_of_leaf {A : Ty} {f : Term A ((S ⊕' T)⋆)}
    (h : IsNormalListLeaf (S ⊕' T) f) : SplitColl S T f := by
  cases h with
  | const v => exact splitColl_const _ v
  | sing hg => exact splitColl_sing hg
  | map hg => exact splitColl_map hg

end Lax149335Proofs

bridge_export Lax149335Proofs
