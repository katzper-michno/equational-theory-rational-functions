import Lax149335Proofs.Appendix.Drops.InjectiveTypes
import Lax149335Proofs.Appendix.Drops.ListNormalForm

/-!
# The prime drop `unshift` is a lift followed by a normal shape

The list normalisation lemma of the appendix (`Lax149335Proofs.drops_with_list_codomain`, in
`Lax149335Proofs.Appendix.Drops.ListNormalisation`) is proved by induction on the composition rank,
and its base case has to treat every atomic drop with a list codomain, `unshift` included.

This file proves that base case: `unshift : 1 + S × (T × S)* × T ⇒ (S × T)*` is itself
provably equal to a lift followed by a drop in normal form, with the bound `0`
(`Lax149335Proofs.normListable_unshift_atom`).

The normal form is the one that the equational theory suggests: on the empty summand the
value is the empty list; on the non-empty summand the prime lift `shift`, applied to the
middle component `(T × S)*`, exposes the first `t` and the last `s` of that component, so
that the input `s ⊗ (w ⊗ t)` is re-organised as

* either `s ⊗ (1 ⊗ t)`, when `w` is empty, whose output is the one-element list `[(s,t)]`,
* or `s ⊗ ((t₁ ⊗ (m ⊗ sₙ)) ⊗ t)`, whose output is `[(s,t₁)] · m · [(sₙ,t)]`,

both of which are concatenations of leaves.  The two case distinctions are performed by the
prime lifts `distL` and `distR`, and the re-associations by `assocL` and `assocR`, so that
everything before the leaves is a lift.

The equation itself (`Lax149335Proofs.Term.unshift_normal_form`) is proved by comparing the contents
of the two sides in `(S + T)*`, which is legitimate because the type `(S × T)*` is injective
(`Lax149335Proofs.Term.listPair_injective`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The terms of the normal form -/

/-- The lift that performs the case distinction on the middle component of the non-empty
summand of the domain of `unshift`: it applies `shift` to that component and distributes the
resulting co-product to the outside. -/
def unshiftCase (S T : Ty) :
    Term (S ⊗ (((T ⊗ S)⋆) ⊗ T))
      ((S ⊗ (Ty.unit ⊗ T)) ⊕' (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T))) :=
  (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
      prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ⨟
    distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)

/-- The inverse of `unshiftCase`. -/
def unshiftUncase (S T : Ty) :
    Term ((S ⊗ (Ty.unit ⊗ T)) ⊕' (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)))
      (S ⊗ (((T ⊗ S)⋆) ⊗ T)) :=
  (undistR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T) ⨟
      prodF (Term.id S) (undistL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ⨟
    prodF (Term.id S) (prodF (unshift T S) (Term.id T))

/-- The lift that re-associates the non-empty case `s ⊗ ((t₁ ⊗ (m ⊗ sₙ)) ⊗ t)` into
`(s ⊗ t₁) ⊗ (m ⊗ (sₙ ⊗ t))`, the shape in which the three leaves of the normal form are
concatenated. -/
def unshiftRegroup (S T : Ty) :
    Term (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T))
      ((S ⊗ T) ⊗ (((S ⊗ T)⋆) ⊗ (S ⊗ T))) :=
  (prodF (Term.id S) (assocR T (((S ⊗ T)⋆) ⊗ S) T) ⨟
      assocL S T ((((S ⊗ T)⋆) ⊗ S) ⊗ T)) ⨟
    prodF (Term.id (S ⊗ T)) (assocR ((S ⊗ T)⋆) S T)

/-- The normal shape on the non-empty case with an empty middle component: the one-element
list `[(s,t)]`. -/
def unshiftLeafEmpty (S T : Ty) : Term (S ⊗ (Ty.unit ⊗ T)) ((S ⊗ T)⋆) :=
  prodF (Term.id S) (snd Ty.unit T) ⨟ pureT (S ⊗ T)

/-- The normal shape on the non-empty case with a non-empty middle component: the
concatenation of the head pair, the middle list and the last pair. -/
def unshiftShapeMain (S T : Ty) : Term ((S ⊗ T) ⊗ (((S ⊗ T)⋆) ⊗ (S ⊗ T))) ((S ⊗ T)⋆) :=
  (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⊙
    (listF (Term.id (S ⊗ T)) ⊙ (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)))

/-- The normal shape of `unshift`, after the lift `unshiftCase`. -/
def unshiftShape (S T : Ty) :
    Term ((S ⊗ (Ty.unit ⊗ T)) ⊕' (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T))) ((S ⊗ T)⋆) :=
  either (unshiftLeafEmpty S T) (unshiftRegroup S T ⨟ unshiftShapeMain S T)

/-! ### The two lifts -/

theorem isLift_unshiftCase (S T : Ty) : IsLift (unshiftCase S T) :=
  IsLift.comp
    (IsLift.comp (IsLift.prodF (IsLift.id _) (IsLift.prodF (IsLift.shift T S) (IsLift.id _)))
      (IsLift.prodF (IsLift.id _) (IsLift.distL _ _ _)))
    (IsLift.distR _ _ _)

theorem isLift_unshiftRegroup (S T : Ty) : IsLift (unshiftRegroup S T) :=
  IsLift.comp
    (IsLift.comp (IsLift.prodF (IsLift.id _) (IsLift.assocR _ _ _)) (IsLift.assocL _ _ _))
    (IsLift.prodF (IsLift.id _) (IsLift.assocR _ _ _))

/-! ### `unshiftCase` and `unshiftUncase` are mutually inverse -/

/-- Two mutually inverse pairs compose to a mutually inverse pair. -/
theorem uns_sandwich {A B C : Ty} {u : Term A B} {v : Term B A} {m : Term B C}
    {m' : Term C B} (hm : (m ⨟ m') ≡ₜ Term.id B) (h : (u ⨟ v) ≡ₜ Term.id A) :
    ((u ⨟ m) ⨟ (m' ⨟ v)) ≡ₜ Term.id A := by
  calc ((u ⨟ m) ⨟ (m' ⨟ v)) ≡ₜ (u ⨟ (m ⨟ (m' ⨟ v))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (u ⨟ ((m ⨟ m') ⨟ v)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (u ⨟ (Term.id B ⨟ v)) := PEq.compR _ (PEq.compL _ hm)
    _ ≡ₜ (u ⨟ v) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id A := h

theorem unshiftCase_unshiftUncase (S T : Ty) :
    (unshiftCase S T ⨟ unshiftUncase S T) ≡ₜ Term.id (S ⊗ (((T ⊗ S)⋆) ⊗ T)) := by
  have h₁ : (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
      prodF (Term.id S) (prodF (unshift T S) (Term.id T))) ≡ₜ
      Term.id (S ⊗ (((T ⊗ S)⋆) ⊗ T)) := by
    calc (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
          prodF (Term.id S) (prodF (unshift T S) (Term.id T)))
        ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (prodF (shift T S) (Term.id T) ⨟ prodF (unshift T S) (Term.id T)) :=
          PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S) (prodF (shift T S ⨟ unshift T S) (Term.id T ⨟ Term.id T)) :=
          PEq.congr_prodF (PEq.id_comp _) (PEq.prod_comp _ _ _ _)
      _ ≡ₜ prodF (Term.id S) (prodF (Term.id ((T ⊗ S)⋆)) (Term.id T)) :=
          PEq.congr_prodF (PEq.refl _)
            (PEq.congr_prodF (shift_unshift T S) (PEq.id_comp _))
      _ ≡ₜ prodF (Term.id S) (Term.id ((((T ⊗ S)⋆) ⊗ T))) :=
          PEq.congr_prodF (PEq.refl _) (PEq.prod_id _ _)
      _ ≡ₜ Term.id (S ⊗ (((T ⊗ S)⋆) ⊗ T)) := PEq.prod_id _ _
  have h₂ : (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
      prodF (Term.id S) (undistL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ≡ₜ
      Term.id (S ⊗ ((Ty.unit ⊕' (T ⊗ (((S ⊗ T)⋆) ⊗ S))) ⊗ T)) := by
    calc (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
          prodF (Term.id S) (undistL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T))
        ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T ⨟
              undistL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S) (Term.id ((Ty.unit ⊕' (T ⊗ (((S ⊗ T)⋆) ⊗ S))) ⊗ T)) :=
          PEq.congr_prodF (PEq.id_comp _) (PEq.distL_undistL _ _ _)
      _ ≡ₜ Term.id (S ⊗ ((Ty.unit ⊕' (T ⊗ (((S ⊗ T)⋆) ⊗ S))) ⊗ T)) := PEq.prod_id _ _
  have hinner := uns_sandwich h₂ h₁
  have houter := uns_sandwich (PEq.distR_undistR S (Ty.unit ⊗ T)
    ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) hinner
  simp only [unshiftCase, unshiftUncase]
  exact (PEq.compR _ (PEq.comp_assoc _ _ _)).trans houter

/-! ### The equation -/

/-- The empty summand of the domain of `unshift` produces the empty list. -/
theorem inl_unshift (A B : Ty) :
    (inl Ty.unit (A ⊗ (((B ⊗ A)⋆) ⊗ B)) ⨟ unshift A B) ≡ₜ nilT (A ⊗ B) := by
  calc (inl Ty.unit (A ⊗ (((B ⊗ A)⋆) ⊗ B)) ⨟
        (sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟
          assocL A B ((A ⊗ B)⋆)) ⨟ cons (A ⊗ B)))
      ≡ₜ ((inl Ty.unit (A ⊗ (((B ⊗ A)⋆) ⊗ B)) ⨟
          sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟
            assocL A B ((A ⊗ B)⋆))) ⨟ cons (A ⊗ B)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.id Ty.unit ⨟ inl Ty.unit ((A ⊗ B) ⊗ ((A ⊗ B)⋆))) ⨟ cons (A ⊗ B)) :=
        PEq.compL _ (PEq.nat_inl _ _)
    _ ≡ₜ (inl Ty.unit ((A ⊗ B) ⊗ ((A ⊗ B)⋆)) ⨟ cons (A ⊗ B)) := PEq.compL _ (PEq.id_comp _)

/-- Re-associating a concatenation, from right to left. -/
theorem uns_fdot_assocL {X Y Z D : Ty} (c₁ : Term X D⋆) (c₂ : Term Y D⋆) (c₃ : Term Z D⋆) :
    (c₁ ⊙ (c₂ ⊙ c₃)) ≡ₜ (assocL X Y Z ⨟ ((c₁ ⊙ c₂) ⊙ c₃)) := by
  calc (c₁ ⊙ (c₂ ⊙ c₃))
      ≡ₜ (Term.id (X ⊗ (Y ⊗ Z)) ⨟ (c₁ ⊙ (c₂ ⊙ c₃))) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocL X Y Z ⨟ assocR X Y Z) ⨟ (c₁ ⊙ (c₂ ⊙ c₃))) :=
        PEq.compL _ (PEq.symm (PEq.assocL_assocR X Y Z))
    _ ≡ₜ (assocL X Y Z ⨟ (assocR X Y Z ⨟ (c₁ ⊙ (c₂ ⊙ c₃)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL X Y Z ⨟ ((c₁ ⊙ c₂) ⊙ c₃)) := PEq.compR _ (PEq.symm (fdot_assoc _ _ _))

/-- The re-association performed by `unshiftRegroup`, read on contents. -/
theorem unshiftRegroup_fdot (S T D : Ty) (a a' : Term S D⋆) (b b' : Term T D⋆)
    (m : Term ((S ⊗ T)⋆) D⋆) :
    (a ⊙ ((b ⊙ (m ⊙ a')) ⊙ b')) ≡ₜ
      (unshiftRegroup S T ⨟ ((a ⊙ b) ⊙ (m ⊙ (a' ⊙ b')))) := by
  have h₁ : (prodF (Term.id (S ⊗ T)) (assocR ((S ⊗ T)⋆) S T) ⨟
      ((a ⊙ b) ⊙ (m ⊙ (a' ⊙ b')))) ≡ₜ ((a ⊙ b) ⊙ ((m ⊙ a') ⊙ b')) := by
    calc (prodF (Term.id (S ⊗ T)) (assocR ((S ⊗ T)⋆) S T) ⨟ ((a ⊙ b) ⊙ (m ⊙ (a' ⊙ b'))))
        ≡ₜ ((Term.id (S ⊗ T) ⨟ (a ⊙ b)) ⊙
            (assocR ((S ⊗ T)⋆) S T ⨟ (m ⊙ (a' ⊙ b')))) := fdot_precomp _ _ _ _
      _ ≡ₜ ((a ⊙ b) ⊙ ((m ⊙ a') ⊙ b')) :=
          fdot_congr (PEq.id_comp _) (PEq.symm (fdot_assoc _ _ _))
  have h₂ : (assocL S T ((((S ⊗ T)⋆) ⊗ S) ⊗ T) ⨟ ((a ⊙ b) ⊙ ((m ⊙ a') ⊙ b'))) ≡ₜ
      (a ⊙ (b ⊙ ((m ⊙ a') ⊙ b'))) := PEq.symm (uns_fdot_assocL _ _ _)
  have h₃ : (prodF (Term.id S) (assocR T ((((S ⊗ T)⋆) ⊗ S)) T) ⨟
      (a ⊙ (b ⊙ ((m ⊙ a') ⊙ b')))) ≡ₜ (a ⊙ ((b ⊙ (m ⊙ a')) ⊙ b')) := by
    calc (prodF (Term.id S) (assocR T ((((S ⊗ T)⋆) ⊗ S)) T) ⨟
          (a ⊙ (b ⊙ ((m ⊙ a') ⊙ b'))))
        ≡ₜ ((Term.id S ⨟ a) ⊙
            (assocR T ((((S ⊗ T)⋆) ⊗ S)) T ⨟ (b ⊙ ((m ⊙ a') ⊙ b')))) :=
          fdot_precomp _ _ _ _
      _ ≡ₜ (a ⊙ ((b ⊙ (m ⊙ a')) ⊙ b')) :=
          fdot_congr (PEq.id_comp _) (PEq.symm (fdot_assoc _ _ _))
  calc (a ⊙ ((b ⊙ (m ⊙ a')) ⊙ b'))
      ≡ₜ (prodF (Term.id S) (assocR T ((((S ⊗ T)⋆) ⊗ S)) T) ⨟
          (a ⊙ (b ⊙ ((m ⊙ a') ⊙ b')))) := PEq.symm h₃
    _ ≡ₜ (prodF (Term.id S) (assocR T ((((S ⊗ T)⋆) ⊗ S)) T) ⨟
          (assocL S T ((((S ⊗ T)⋆) ⊗ S) ⊗ T) ⨟ ((a ⊙ b) ⊙ ((m ⊙ a') ⊙ b')))) :=
        PEq.compR _ (PEq.symm h₂)
    _ ≡ₜ (prodF (Term.id S) (assocR T ((((S ⊗ T)⋆) ⊗ S)) T) ⨟
          (assocL S T ((((S ⊗ T)⋆) ⊗ S) ⊗ T) ⨟
            (prodF (Term.id (S ⊗ T)) (assocR ((S ⊗ T)⋆) S T) ⨟
              ((a ⊙ b) ⊙ (m ⊙ (a' ⊙ b')))))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm h₁))
    _ ≡ₜ (unshiftRegroup S T ⨟ ((a ⊙ b) ⊙ (m ⊙ (a' ⊙ b')))) := by
        simp only [unshiftRegroup]
        exact PEq.symm ((PEq.comp_assoc _ _ _).trans (PEq.comp_assoc _ _ _))

/-! ### Contents -/

/-- The content of the one-element leaf on the empty middle case. -/
theorem unshiftLeafEmpty_content (S T : Ty) :
    (unshiftLeafEmpty S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      ((inl S T ⨟ pureT (S ⊕' T)) ⊙
        (snd Ty.unit T ⨟ (inr S T ⨟ pureT (S ⊕' T)))) := by
  calc ((prodF (Term.id S) (snd Ty.unit T) ⨟ pureT (S ⊗ T)) ⨟
        TyF2.concatMap (.list (.prod .p1 .p2)) S T)
      ≡ₜ (prodF (Term.id S) (snd Ty.unit T) ⨟
          (pureT (S ⊗ T) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id S) (snd Ty.unit T) ⨟
          ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T)))) :=
        PEq.compR _ (homT_pure _)
    _ ≡ₜ ((Term.id S ⨟ (inl S T ⨟ pureT (S ⊕' T))) ⊙
          (snd Ty.unit T ⨟ (inr S T ⨟ pureT (S ⊕' T)))) := fdot_precomp _ _ _ _
    _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
          (snd Ty.unit T ⨟ (inr S T ⨟ pureT (S ⊕' T)))) :=
        fdot_congr (PEq.id_comp _) (PEq.refl _)

/-- The content of the main normal shape. -/
theorem unshiftShapeMain_content (S T : Ty) :
    (unshiftShapeMain S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      (((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
        (homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
          ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))))) := by
  have hpure : ((Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⨟
      TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) := by
    calc ((Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⨟
          TyF2.concatMap (.list (.prod .p1 .p2)) S T)
        ≡ₜ (pureT (S ⊗ T) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
          PEq.compL _ (PEq.id_comp _)
      _ ≡ₜ _ := homT_pure _
  have hmap : ((listF (Term.id (S ⊗ T))) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) := by
    calc ((listF (Term.id (S ⊗ T))) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)
        ≡ₜ (Term.id ((S ⊗ T)⋆) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
          PEq.compL _ (PEq.list_id _)
      _ ≡ₜ _ := PEq.id_comp _
  calc (unshiftShapeMain S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)
      ≡ₜ (((Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T) ⊙
          ((listF (Term.id (S ⊗ T)) ⊙ (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T))) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T)) := fdot_comp_homT _ _ _
    _ ≡ₜ (((Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T) ⊙
          (((listF (Term.id (S ⊗ T))) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) ⊙
            ((Term.id (S ⊗ T) ⨟ pureT (S ⊗ T)) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T))) :=
        fdot_congr (PEq.refl _) (fdot_comp_homT _ _ _)
    _ ≡ₜ _ := fdot_congr hpure (fdot_congr hmap hpure)

/-- The content of the non-empty middle component, obtained from the rebracketing property of
`unshift` for the pair `(T, S)` and the exchange of the two letters. -/
theorem unshift_middle_content (S T : Ty) :
    ((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) ⨟
        homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T)))) ≡ₜ
      ((inr S T ⨟ pureT (S ⊕' T)) ⊙
        (homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
          (inl S T ⨟ pureT (S ⊕' T)))) := by
  -- the two letters, in `(T + S)*` and in `(S + T)*`
  have hr₁ : ((inl T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ≡ₜ (inr S T ⨟ pureT (S ⊕' T)) :=
    leftLetter_comm S T
  have hr₂ : ((inr T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ≡ₜ (inl S T ⨟ pureT (S ⊕' T)) :=
    rightLetter_comm S T
  have hswapc : (((inr T S ⨟ pureT (T ⊕' S)) ⊙ (inl T S ⨟ pureT (T ⊕' S))) ⨟
      listF (comm T S)) ≡ₜ
      ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) :=
    (fdot_comp_listF _ _ _).trans (fdot_congr hr₂ hr₁)
  have hswaph : (homT ((inl T S ⨟ pureT (T ⊕' S)) ⊙ (inr T S ⨟ pureT (T ⊕' S))) ⨟
      listF (comm T S)) ≡ₜ
      homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) :=
    (homT_comp_listF _ _).trans
      (homT_congr ((fdot_comp_listF _ _ _).trans (fdot_congr hr₁ hr₂)))
  calc ((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) ⨟
        homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))))
      ≡ₜ ((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) ⨟
          (TyF2.concatMap (.list (.prod .p1 .p2)) T S ⨟ listF (comm T S))) :=
        PEq.compR _ (PEq.symm hswaph)
    _ ≡ₜ (((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) ⨟
          TyF2.concatMap (.list (.prod .p1 .p2)) T S) ⨟ listF (comm T S)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟
          (unshift T S ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) T S)) ⨟
          listF (comm T S)) := PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟
          TyF2.concatMap
            (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) T S) ⨟
          listF (comm T S)) := PEq.compL _ (PEq.compR _ (unshift_rebracketing T S))
    _ ≡ₜ (((inl T S ⨟ pureT (T ⊕' S)) ⊙
          (homT ((inr T S ⨟ pureT (T ⊕' S)) ⊙ (inl T S ⨟ pureT (T ⊕' S))) ⊙
            (inr T S ⨟ pureT (T ⊕' S)))) ⨟ listF (comm T S)) :=
        PEq.compL _ (inr_either _ _)
    _ ≡ₜ (((inl T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ⊙
          ((homT ((inr T S ⨟ pureT (T ⊕' S)) ⊙ (inl T S ⨟ pureT (T ⊕' S))) ⊙
            (inr T S ⨟ pureT (T ⊕' S))) ⨟ listF (comm T S))) :=
        fdot_comp_listF _ _ _
    _ ≡ₜ (((inl T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ⊙
          ((homT ((inr T S ⨟ pureT (T ⊕' S)) ⊙ (inl T S ⨟ pureT (T ⊕' S))) ⨟
              listF (comm T S)) ⊙
            ((inr T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)))) :=
        fdot_congr (PEq.refl _) (fdot_comp_listF _ _ _)
    _ ≡ₜ _ :=
        fdot_congr hr₁ (fdot_congr ((homT_comp_listF _ _).trans (homT_congr hswapc)) hr₂)

/-! ### The equation -/

/-- **`unshift` is a lift followed by a normal shape.** -/
theorem unshift_normal_form (S T : Ty) :
    unshift S T ≡ₜ either (nilT (S ⊗ T)) (unshiftCase S T ⨟ unshiftShape S T) := by
  refine (either_unique (unshift S T)).trans (either_congr (inl_unshift S T) ?_)
  -- the content of the non-empty summand of the domain of `unshift`
  have hLc : ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
      TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      ((inl S T ⨟ pureT (S ⊕' T)) ⊙
        (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
          (inr S T ⨟ pureT (S ⊕' T)))) := by
    calc ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
          TyF2.concatMap (.list (.prod .p1 .p2)) S T)
        ≡ₜ (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟
            (unshift S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟
            TyF2.concatMap
              (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T) :=
          PEq.compR _ (unshift_rebracketing S T)
      _ ≡ₜ _ := inr_either _ _
  -- the two branches of the inverse of the case lift
  have hinl : (inl (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
      unshiftUncase S T) ≡ₜ
      prodF (Term.id S) (prodF (nilT (T ⊗ S)) (Term.id T)) := by
    simp only [unshiftUncase, undistR, undistL]
    calc (inl (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
          ((either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T))) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))))
        ≡ₜ ((inl _ _ ⨟
            (either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T))) ⨟
              prodF (Term.id S)
                (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                  (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((inl _ _ ⨟
            either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.compL _ (inl_either _ _))
      _ ≡ₜ (prodF (Term.id S ⨟ Term.id S)
            (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T) ⨟
              either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (inl_either _ _))
      _ ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T) ⨟
              prodF (unshift T S) (Term.id T)) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S)
            (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S)
              (Term.id T ⨟ Term.id T)) :=
          PEq.congr_prodF (PEq.id_comp _) (PEq.prod_comp _ _ _ _)
      _ ≡ₜ prodF (Term.id S) (prodF (nilT (T ⊗ S)) (Term.id T)) :=
          PEq.congr_prodF (PEq.refl _)
            (PEq.congr_prodF (inl_unshift T S) (PEq.id_comp _))
  have hinr : (inr (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
      unshiftUncase S T) ≡ₜ
      prodF (Term.id S)
        (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) (Term.id T)) := by
    simp only [unshiftUncase, undistR, undistL]
    calc (inr (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
          ((either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T))) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))))
        ≡ₜ ((inr _ _ ⨟
            (either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T))) ⨟
              prodF (Term.id S)
                (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                  (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((inr _ _ ⨟
            either (prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))
              (prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)))) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T)) ⨟
            prodF (Term.id S)
              (either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.compL _ (inr_either _ _))
      _ ≡ₜ (prodF (Term.id S ⨟ Term.id S)
            (inr (Ty.unit ⊗ T) ((T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⊗ T) ⨟
              either (prodF (inl Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T))) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T)) ⨟
            prodF (Term.id S) (prodF (unshift T S) (Term.id T))) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (inr_either _ _))
      _ ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S)))) (Term.id T) ⨟
              prodF (unshift T S) (Term.id T)) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S)
            (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S)
              (Term.id T ⨟ Term.id T)) :=
          PEq.congr_prodF (PEq.id_comp _) (PEq.prod_comp _ _ _ _)
      _ ≡ₜ _ := PEq.congr_prodF (PEq.refl _) (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))
  -- the key equation, after the injective content map has been cancelled
  have key : (unshiftUncase S T ⨟
      ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
        TyF2.concatMap (.list (.prod .p1 .p2)) S T)) ≡ₜ
      (unshiftShape S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) := by
    refine either_ext _ _ ?_ ?_
    · calc (inl _ _ ⨟ (unshiftUncase S T ⨟
            ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T)))
          ≡ₜ ((inl _ _ ⨟ unshiftUncase S T) ⨟
              ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
                TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (prodF (Term.id S) (prodF (nilT (T ⊗ S)) (Term.id T)) ⨟
              ((inl S T ⨟ pureT (S ⊕' T)) ⊙
                (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
                  (inr S T ⨟ pureT (S ⊕' T))))) := PEq.congr_comp hinl hLc
        _ ≡ₜ ((Term.id S ⨟ (inl S T ⨟ pureT (S ⊕' T))) ⊙
              (prodF (nilT (T ⊗ S)) (Term.id T) ⨟
                (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
                  (inr S T ⨟ pureT (S ⊕' T))))) := fdot_precomp _ _ _ _
        _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
              ((nilT (T ⊗ S) ⨟
                  homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T)))) ⊙
                (Term.id T ⨟ (inr S T ⨟ pureT (S ⊕' T))))) :=
            fdot_congr (PEq.id_comp _) (fdot_precomp _ _ _ _)
        _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
              (nilT (S ⊕' T) ⊙ (inr S T ⨟ pureT (S ⊕' T)))) :=
            fdot_congr (PEq.refl _) (fdot_congr (homT_nil _) (PEq.id_comp _))
        _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
              (snd Ty.unit T ⨟ (inr S T ⨟ pureT (S ⊕' T)))) :=
            fdot_congr (PEq.refl _) (fdot_nil_left _)
        _ ≡ₜ (unshiftLeafEmpty S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
            PEq.symm (unshiftLeafEmpty_content S T)
        _ ≡ₜ ((inl _ _ ⨟ unshiftShape S T) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
            PEq.compL _ (PEq.symm (inl_either _ _))
        _ ≡ₜ (inl _ _ ⨟ (unshiftShape S T ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T)) := PEq.comp_assoc _ _ _
    · calc (inr _ _ ⨟ (unshiftUncase S T ⨟
            ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T)))
          ≡ₜ ((inr _ _ ⨟ unshiftUncase S T) ⨟
              ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
                TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (prodF (Term.id S)
                (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) (Term.id T)) ⨟
              ((inl S T ⨟ pureT (S ⊕' T)) ⊙
                (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
                  (inr S T ⨟ pureT (S ⊕' T))))) := PEq.congr_comp hinr hLc
        _ ≡ₜ ((Term.id S ⨟ (inl S T ⨟ pureT (S ⊕' T))) ⊙
              (prodF (inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) (Term.id T) ⨟
                (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
                  (inr S T ⨟ pureT (S ⊕' T))))) := fdot_precomp _ _ _ _
        _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
              (((inr Ty.unit (T ⊗ ((((S ⊗ T)⋆) ⊗ S))) ⨟ unshift T S) ⨟
                  homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T)))) ⊙
                (Term.id T ⨟ (inr S T ⨟ pureT (S ⊕' T))))) :=
            fdot_congr (PEq.id_comp _) (fdot_precomp _ _ _ _)
        _ ≡ₜ ((inl S T ⨟ pureT (S ⊕' T)) ⊙
              (((inr S T ⨟ pureT (S ⊕' T)) ⊙
                  (homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
                    (inl S T ⨟ pureT (S ⊕' T)))) ⊙
                (inr S T ⨟ pureT (S ⊕' T)))) :=
            fdot_congr (PEq.refl _)
              (fdot_congr (unshift_middle_content S T) (PEq.id_comp _))
        _ ≡ₜ (unshiftRegroup S T ⨟
              (((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
                (homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))) ⊙
                  ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T)))))) :=
            unshiftRegroup_fdot S T (S ⊕' T) _ _ _ _ _
        _ ≡ₜ (unshiftRegroup S T ⨟
              (unshiftShapeMain S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
            PEq.compR _ (PEq.symm (unshiftShapeMain_content S T))
        _ ≡ₜ ((unshiftRegroup S T ⨟ unshiftShapeMain S T) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inr _ _ ⨟ unshiftShape S T) ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
            PEq.compL _ (PEq.symm (inr_either _ _))
        _ ≡ₜ (inr _ _ ⨟ (unshiftShape S T ⨟
              TyF2.concatMap (.list (.prod .p1 .p2)) S T)) := PEq.comp_assoc _ _ _
  -- conclude, by cancelling the injective content map
  refine ((cancel (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T)
    (unshiftCase S T ⨟ unshiftShape S T)).1 _
      (TyF2.concatMap (.list (.prod .p1 .p2)) S T) (listPair_injective S T)).2 ?_
  calc ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
        TyF2.concatMap (.list (.prod .p1 .p2)) S T)
      ≡ₜ (Term.id (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟
          ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((unshiftCase S T ⨟ unshiftUncase S T) ⨟
          ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
        PEq.compL _ (PEq.symm (unshiftCase_unshiftUncase S T))
    _ ≡ₜ (unshiftCase S T ⨟ (unshiftUncase S T ⨟
          ((inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unshiftCase S T ⨟
          (unshiftShape S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
        PEq.compR _ key
    _ ≡ₜ ((unshiftCase S T ⨟ unshiftShape S T) ⨟
          TyF2.concatMap (.list (.prod .p1 .p2)) S T) := PEq.symm (PEq.comp_assoc _ _ _)

end Term

/-- **The atom `unshift` of the list normalisation lemma.**  The prime drop `unshift` is
provably equal to a lift followed by a drop in normal form, whose leaves have components of
rank `0`. -/
theorem normListable_unshift_atom (S T : Ty) :
    NormListable (S ⊗ T) 0 (Term.unshift S T) := by
  refine NormListable.congr (Term.unshift_normal_form S T) ?_
  refine NormListable.either (NormListable.of_isListNormalForm .nil) ?_
  refine NormListable.lift_comp (Term.isLift_unshiftCase S T) ?_
  refine NormListable.either ?_ ?_
  · exact NormListable.of_leaf
      (.sing (IsDrop.prodF (IsDrop.id S) (IsDrop.snd Ty.unit T)) (by simp [rank]))
  · refine NormListable.lift_comp (Term.isLift_unshiftRegroup S T) ?_
    refine NormListable.fdot (NormListable.of_leaf (.sing (IsDrop.id (S ⊗ T)) le_rfl)) ?_
    exact NormListable.fdot (NormListable.of_leaf (.map (IsDrop.id (S ⊗ T)) le_rfl))
      (NormListable.of_leaf (.sing (IsDrop.id (S ⊗ T)) le_rfl))

end Lax149335Proofs

bridge_export Lax149335Proofs
