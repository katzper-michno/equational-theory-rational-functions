import Lax149335Proofs.Appendix.ConjugacyRule.Soundness
import Mathlib.Tactic.Set

/-!
# Injective types for the shift machinery (appendix, *Handling shift*)

The appendix section that develops the tools for `shift` uses two facts about concatenation
maps which are stated there without proof:

* the type `(S × T)*` is *injective*, i.e. its concatenation map `(S × T)* ↣ (S + T)*` is
  provably injective (`Lax149335Proofs.Term.listPair_injective`), and
* the type `1 + S × (T × S)* × T`, the codomain of `shift`, is injective
  (`Lax149335Proofs.Term.shiftCod_injective`).

The proof of the second fact goes through the rebracketing property of `unshift`
(`Lax149335Proofs.Term.unshift_rebracketing`), i.e. the statement that `unshift` does not change the
content of the list; this is Axiom 15 read through the co-product `S + T`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Auxiliary lemmas about homomorphisms -/

/-- Composing `cons` with a homomorphism: the empty list is mapped to the empty list and a
non-empty list is split into its head and its tail. -/
theorem cons_homT {A D : Ty} (c : Term A D⋆) :
    (cons A ⨟ homT c) ≡ₜ either (nilT D) (c ⊙ homT c) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ homT c))
        ≡ₜ ((inl Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ homT c) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ nilT D := homT_nil c
      _ ≡ₜ (inl Ty.unit (A ⊗ A⋆) ⨟ either (nilT D) (c ⊙ homT c)) := PEq.symm (inl_either _ _)
  · calc (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ homT c))
        ≡ₜ ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ homT c) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((pureT A ⊙ Term.id A⋆) ⨟ homT c) := PEq.compL _ (PEq.prepend_def A)
      _ ≡ₜ ((pureT A ⨟ homT c) ⊙ (Term.id A⋆ ⨟ homT c)) := fdot_comp_homT _ _ _
      _ ≡ₜ (c ⊙ homT c) := fdot_congr (homT_pure c) (PEq.id_comp _)
      _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ either (nilT D) (c ⊙ homT c)) := PEq.symm (inr_either _ _)

/-! ### The letter injections into `(S + T)*` -/

/-- The injection of the left letters into `(S + T)*`. -/
theorem leftLetter_comm (S T : Ty) :
    ((inl T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ≡ₜ (inr S T ⨟ pureT (S ⊕' T)) := by
  calc ((inl T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S))
      ≡ₜ (inl T S ⨟ (pureT (T ⊕' S) ⨟ listF (comm T S))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl T S ⨟ (comm T S ⨟ pureT (S ⊕' T))) :=
        PEq.compR _ (PEq.symm (pureT_natural (comm T S)))
    _ ≡ₜ ((inl T S ⨟ comm T S) ⨟ pureT (S ⊕' T)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (inr S T ⨟ pureT (S ⊕' T)) := PEq.compL _ (inl_either _ _)

/-- The injection of the right letters into `(S + T)*`. -/
theorem rightLetter_comm (S T : Ty) :
    ((inr T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S)) ≡ₜ (inl S T ⨟ pureT (S ⊕' T)) := by
  calc ((inr T S ⨟ pureT (T ⊕' S)) ⨟ listF (comm T S))
      ≡ₜ (inr T S ⨟ (pureT (T ⊕' S) ⨟ listF (comm T S))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inr T S ⨟ (comm T S ⨟ pureT (S ⊕' T))) :=
        PEq.compR _ (PEq.symm (pureT_natural (comm T S)))
    _ ≡ₜ ((inr T S ⨟ comm T S) ⨟ pureT (S ⊕' T)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (inl S T ⨟ pureT (S ⊕' T)) := PEq.compL _ (inr_either _ _)

/-! ### Axiom 15 read through the co-product `S + T` -/

/-- **Axiom 15 for the co-product `S + T`.**  `shiftR` does not change the content of the
list, read through the injections of `S` and `T` into `S + T` (Axiom 15 itself is stated
through the injections into `T + S`). -/
theorem shiftR_content_swap (S T : Ty) :
    (shiftR T S ⨟ ((inr S T ⨟ pureT (S ⊕' T)) ⊙
        homT ((inl S T ⨟ pureT (S ⊕' T)) ⊙ (inr S T ⨟ pureT (S ⊕' T))))) ≡ₜ
      (homT ((inr S T ⨟ pureT (S ⊕' T)) ⊙ (inl S T ⨟ pureT (S ⊕' T))) ⊙
        (inr S T ⨟ pureT (S ⊕' T))) := by
  set r₁ : Term T ((T ⊕' S)⋆) := inl T S ⨟ pureT (T ⊕' S) with hr₁
  set r₂ : Term S ((T ⊕' S)⋆) := inr T S ⨟ pureT (T ⊕' S) with hr₂
  set q₁ : Term S ((S ⊕' T)⋆) := inl S T ⨟ pureT (S ⊕' T) with hq₁
  set q₂ : Term T ((S ⊕' T)⋆) := inr S T ⨟ pureT (S ⊕' T) with hq₂
  have h₁ : (r₁ ⨟ listF (comm T S)) ≡ₜ q₂ := leftLetter_comm S T
  have h₂ : (r₂ ⨟ listF (comm T S)) ≡ₜ q₁ := rightLetter_comm S T
  -- the source of the axiom, transported along `comm`
  have hsrc : ((r₁ ⊙ homT (r₂ ⊙ r₁)) ⨟ listF (comm T S)) ≡ₜ (q₂ ⊙ homT (q₁ ⊙ q₂)) := by
    calc ((r₁ ⊙ homT (r₂ ⊙ r₁)) ⨟ listF (comm T S))
        ≡ₜ ((r₁ ⨟ listF (comm T S)) ⊙ (homT (r₂ ⊙ r₁) ⨟ listF (comm T S))) :=
          fdot_comp_listF _ _ _
      _ ≡ₜ (q₂ ⊙ homT ((r₂ ⊙ r₁) ⨟ listF (comm T S))) :=
          fdot_congr h₁ (homT_comp_listF _ _)
      _ ≡ₜ (q₂ ⊙ homT (q₁ ⊙ q₂)) :=
          fdot_congr (PEq.refl _)
            (homT_congr ((fdot_comp_listF _ _ _).trans (fdot_congr h₂ h₁)))
  -- the target of the axiom, transported along `comm`
  have htgt : ((homT (r₁ ⊙ r₂) ⊙ r₁) ⨟ listF (comm T S)) ≡ₜ (homT (q₂ ⊙ q₁) ⊙ q₂) := by
    calc ((homT (r₁ ⊙ r₂) ⊙ r₁) ⨟ listF (comm T S))
        ≡ₜ ((homT (r₁ ⊙ r₂) ⨟ listF (comm T S)) ⊙ (r₁ ⨟ listF (comm T S))) :=
          fdot_comp_listF _ _ _
      _ ≡ₜ (homT ((r₁ ⊙ r₂) ⨟ listF (comm T S)) ⊙ q₂) :=
          fdot_congr (homT_comp_listF _ _) h₁
      _ ≡ₜ (homT (q₂ ⊙ q₁) ⊙ q₂) :=
          fdot_congr (homT_congr ((fdot_comp_listF _ _ _).trans (fdot_congr h₁ h₂)))
            (PEq.refl _)
  calc (shiftR T S ⨟ (q₂ ⊙ homT (q₁ ⊙ q₂)))
      ≡ₜ (shiftR T S ⨟ ((r₁ ⊙ homT (r₂ ⊙ r₁)) ⨟ listF (comm T S))) :=
        PEq.compR _ (PEq.symm hsrc)
    _ ≡ₜ ((shiftR T S ⨟ (r₁ ⊙ homT (r₂ ⊙ r₁))) ⨟ listF (comm T S)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((homT (r₁ ⊙ r₂) ⊙ r₁) ⨟ listF (comm T S)) :=
        PEq.compL _ (PEq.shiftR_content T S)
    _ ≡ₜ (homT (q₂ ⊙ q₁) ⊙ q₂) := htgt

/-! ### The two injective types -/

/-- **The type `(S × T)*` is injective** (appendix, *Handling shift*): its concatenation map
into `(S + T)*` is provably injective. -/
theorem listPair_injective (S T : Ty) :
    ProvablyInjective (TyF2.concatMap (.list (.prod .p1 .p2)) S T) := by
  have hfac : (pairR (Term.id ((S ⊗ T)⋆)) (inl Ty.unit S) ⨟
      TyF2.concatMap (.prod (.list (.prod .p1 .p2)) (.sum .unit .p1)) S T) ≡ₜ
      TyF2.concatMap (.list (.prod .p1 .p2)) S T := by
    calc (pairR (Term.id ((S ⊗ T)⋆)) (inl Ty.unit S) ⨟
          (prodF (TyF2.concatMap (.list (.prod .p1 .p2)) S T)
              (either (nilT (S ⊕' T)) (inl S T ⨟ pureT (S ⊕' T))) ⨟ binconcat (S ⊕' T)))
        ≡ₜ ((pairR (Term.id ((S ⊗ T)⋆)) (inl Ty.unit S) ⨟
            prodF (TyF2.concatMap (.list (.prod .p1 .p2)) S T)
              (either (nilT (S ⊕' T)) (inl S T ⨟ pureT (S ⊕' T)))) ⨟ binconcat (S ⊕' T)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (Term.id ((S ⊗ T)⋆) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)
            (inl Ty.unit S ⨟ either (nilT (S ⊕' T)) (inl S T ⨟ pureT (S ⊕' T))) ⨟
            binconcat (S ⊕' T)) := PEq.compL _ (pairR_prodF _ _ _ _)
      _ ≡ₜ (pairR (TyF2.concatMap (.list (.prod .p1 .p2)) S T) (nilT (S ⊕' T)) ⨟
            binconcat (S ⊕' T)) :=
          PEq.compL _ (pairR_congr (PEq.id_comp _) (inl_either _ _))
      _ ≡ₜ (unitR ((S ⊗ T)⋆) ⨟
            ((TyF2.concatMap (.list (.prod .p1 .p2)) S T) ⊙ nilT (S ⊕' T))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR ((S ⊗ T)⋆) ⨟
            (fst ((S ⊗ T)⋆) Ty.unit ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
          PEq.compR _ (fdot_nil_right _)
      _ ≡ₜ ((unitR ((S ⊗ T)⋆) ⨟ fst ((S ⊗ T)⋆) Ty.unit) ⨟
            TyF2.concatMap (.list (.prod .p1 .p2)) S T) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id ((S ⊗ T)⋆) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
          PEq.compL _ (PEq.unitR_fst _)
      _ ≡ₜ TyF2.concatMap (.list (.prod .p1 .p2)) S T := PEq.id_comp _
  exact ProvablyInjective.of_peq (PEq.symm hfac)
    (ProvablyInjective.comp ⟨fst _ _, pairR_fst _ _⟩ (cyclic_annotation_injective S T))

/-- **`unshift` is a rebracketing**: it does not change the content of the list, read through
the injections of `S` and `T` into `S + T`. -/
theorem unshift_rebracketing (S T : Ty) :
    (unshift S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) ≡ₜ
      TyF2.concatMap (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T := by
  set q₁ : Term S ((S ⊕' T)⋆) := inl S T ⨟ pureT (S ⊕' T) with hq₁
  set q₂ : Term T ((S ⊕' T)⋆) := inr S T ⨟ pureT (S ⊕' T) with hq₂
  set K : Term (S ⊗ ((T ⊗ S)⋆ ⊗ T)) ((S ⊗ T) ⊗ (S ⊗ T)⋆) :=
    prodF (Term.id S) (shiftR T S) ⨟ assocL S T ((S ⊗ T)⋆) with hK
  -- the second component of the co-pairing
  have hmain : (K ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂))) ≡ₜ (q₁ ⊙ (homT (q₂ ⊙ q₁) ⊙ q₂)) := by
    have hassoc : (assocL S T ((S ⊗ T)⋆) ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂))) ≡ₜ
        (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂))) := by
      calc (assocL S T ((S ⊗ T)⋆) ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂)))
          ≡ₜ (assocL S T ((S ⊗ T)⋆) ⨟
              (assocR S T ((S ⊗ T)⋆) ⨟ (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂))))) :=
            PEq.compR _ (fdot_assoc _ _ _)
        _ ≡ₜ ((assocL S T ((S ⊗ T)⋆) ⨟ assocR S T ((S ⊗ T)⋆)) ⨟
              (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂)))) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id (S ⊗ (T ⊗ (S ⊗ T)⋆)) ⨟ (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂)))) :=
            PEq.compL _ (PEq.assocL_assocR S T ((S ⊗ T)⋆))
        _ ≡ₜ (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂))) := PEq.id_comp _
    calc (K ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂)))
        ≡ₜ (prodF (Term.id S) (shiftR T S) ⨟
            (assocL S T ((S ⊗ T)⋆) ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂)))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id S) (shiftR T S) ⨟ (q₁ ⊙ (q₂ ⊙ homT (q₁ ⊙ q₂)))) :=
          PEq.compR _ hassoc
      _ ≡ₜ ((Term.id S ⨟ q₁) ⊙ (shiftR T S ⨟ (q₂ ⊙ homT (q₁ ⊙ q₂)))) := fdot_precomp _ _ _ _
      _ ≡ₜ (q₁ ⊙ (homT (q₂ ⊙ q₁) ⊙ q₂)) :=
          fdot_congr (PEq.id_comp _) (shiftR_content_swap S T)
  calc (unshift S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)
      ≡ₜ ((sumF (Term.id Ty.unit) K) ⨟ (cons (S ⊗ T) ⨟ homT (q₁ ⊙ q₂))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((sumF (Term.id Ty.unit) K) ⨟
          either (nilT (S ⊕' T)) ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂))) :=
        PEq.compR _ (cons_homT _)
    _ ≡ₜ either (Term.id Ty.unit ⨟ nilT (S ⊕' T)) (K ⨟ ((q₁ ⊙ q₂) ⊙ homT (q₁ ⊙ q₂))) :=
        sumF_either _ _ _ _
    _ ≡ₜ either (nilT (S ⊕' T)) (q₁ ⊙ (homT (q₂ ⊙ q₁) ⊙ q₂)) :=
        either_congr (PEq.id_comp _) hmain

/-- **`shift` is a rebracketing**: it does not change the content of the list, read through
the injections of `S` and `T` into `S + T`. -/
theorem shift_rebracketing (S T : Ty) :
    (shift S T ⨟
        TyF2.concatMap (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T) ≡ₜ
      TyF2.concatMap (.list (.prod .p1 .p2)) S T := by
  calc (shift S T ⨟
        TyF2.concatMap (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T)
      ≡ₜ (shift S T ⨟ (unshift S T ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T)) :=
        PEq.compR _ (PEq.symm (unshift_rebracketing S T))
    _ ≡ₜ ((shift S T ⨟ unshift S T) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((S ⊗ T)⋆) ⨟ TyF2.concatMap (.list (.prod .p1 .p2)) S T) :=
        PEq.compL _ (shift_unshift S T)
    _ ≡ₜ TyF2.concatMap (.list (.prod .p1 .p2)) S T := PEq.id_comp _

/-- **The codomain of `shift` is an injective type** (appendix, *Handling shift*): the
concatenation map `1 + S × (T × S)* × T ↣ (S + T)*` is provably injective. -/
theorem shiftCod_injective (S T : Ty) :
    ProvablyInjective
      (TyF2.concatMap (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T) :=
  ProvablyInjective.of_peq (PEq.symm (unshift_rebracketing S T))
    (ProvablyInjective.comp ⟨shift S T, unshift_shift S T⟩ (listPair_injective S T))

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
