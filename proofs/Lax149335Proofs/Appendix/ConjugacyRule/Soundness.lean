import Lax149335Proofs.SimpleCompleteness.Statements
import Lax149335Proofs.Appendix.Groups.Unprefixing
import Lax149335Proofs.Appendix.Guarded.FixedLengths
import Mathlib.Tactic.Set

/-!
# Proofs for the conjugacy rule (appendix, *Proofs for soundness of the conjugacy rule*)

This file proves the two ingredients of the proof of Lemma 6.7 (the bundle lemma) that the
appendix section contributes: the fact that `pure` is provably injective, which is the heart
of it, and provable injectivity of the concatenation map used by the cyclic annotation.

The other results of that appendix section are proved elsewhere: Lemma 6.2
(`Lax149335Proofs.conjugacy_of_syntactic`) and Claim 6.6 (`Lax149335Proofs.hom_factors`) in
`Lax149335Proofs.SimpleCompleteness.Statements`, the *value extraction* lemma behind Lemma 6.4
(`Lax149335Proofs.value_extraction`) in `Lax149335Proofs.SimpleCompleteness.ValueExtractionProof`, and
the extraction of a prefix and a suffix of fixed length
(`Lax149335Proofs.Term.concatMap_fixedShape_iso`) in `Lax149335Proofs.Appendix.Guarded.FixedLengths`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The bundle lemma (Lemma 6.7)

The two ingredients of the proof of Lemma 6.7 in the appendix.  The first one is that `pure`
is provably injective, which the appendix singles out as the interesting case, because the
one-sided inverse has to escape the list monad and can only be constructed in a non-natural
way, using a value of the type. -/

-- (the head term `Term.headT w` for a value `w` is defined in `Lax149335Proofs.Terms.Derived`,
-- since the bundle term of Axiom 16 already uses it)

/-- The head term is a one-sided inverse of `pure`, for every choice of the value `w`. -/
theorem pureT_headT {A : Ty} (w : Value A) : (pureT A ⨟ headT w) ≡ₜ Term.id A := by
  have h1 : (prepend A ⨟ uncons A) ≡ₜ inr Ty.unit (A ⊗ A⋆) := by
    calc ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ uncons A)
        ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ uncons A)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ Term.id (Ty.unit ⊕' (A ⊗ A⋆))) :=
          PEq.compR _ (PEq.cons_uncons A)
      _ ≡ₜ inr Ty.unit (A ⊗ A⋆) := PEq.comp_id _
  calc ((unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A) ⨟ (uncons A ⨟ either w (fst A A⋆)))
      ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
          (prepend A ⨟ (uncons A ⨟ either w (fst A A⋆)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
          ((prepend A ⨟ uncons A) ⨟ either w (fst A A⋆))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
          (inr Ty.unit (A ⊗ A⋆) ⨟ either w (fst A A⋆))) :=
        PEq.compR _ (PEq.compL _ h1)
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ fst A A⋆) :=
        PEq.compR _ (inr_either _ _)
    _ ≡ₜ (unitR A ⨟ (prodF (Term.id A) (nilT A) ⨟ fst A A⋆)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR A ⨟ (fst A Ty.unit ⨟ Term.id A)) := PEq.compR _ (PEq.nat_fst _ _)
    _ ≡ₜ (unitR A ⨟ fst A Ty.unit) := PEq.compR _ (PEq.comp_id _)
    _ ≡ₜ Term.id A := PEq.unitR_fst A

/-- `pure` is provably injective. -/
theorem pureT_injective (A : Ty) : ProvablyInjective (pureT A) :=
  ⟨headT (defaultValue A), pureT_headT _⟩

/-- **Lemma (injectivity of the cyclic annotation)** (appendix, proof of Lemma 6.7).  For all
types `A` and `B`, the concatenation map `(A × B)* × A^{<2} ↣ (A + B)*` is provably
injective. -/
theorem cyclic_annotation_injective (A B : Ty) :
    ProvablyInjective
      (TyF2.concatMap (.prod (.list (.prod .p1 .p2)) (.sum .unit .p1)) A B) := by
  set p₁ : Term A ((A ⊕' B)⋆) := inl A B ⨟ pureT (A ⊕' B) with hp₁
  set p₂ : Term B ((A ⊕' B)⋆) := inr A B ⨟ pureT (A ⊕' B) with hp₂
  -- the concatenation map factors through the symmetric variant of `block`
  have hfac : (prodF (listF (prodF (pureT A) (Term.id B))) (either (nilT A) (pureT A)) ⨟
      cmBlockL A B) ≡ₜ
      TyF2.concatMap (.prod (.list (.prod .p1 .p2)) (.sum .unit .p1)) A B := by
    have hfst : (listF (prodF (pureT A) (Term.id B)) ⨟ homT (homT p₁ ⊙ p₂)) ≡ₜ
        homT (p₁ ⊙ p₂) := by
      calc (listF (prodF (pureT A) (Term.id B)) ⨟ homT (homT p₁ ⊙ p₂))
          ≡ₜ homT (prodF (pureT A) (Term.id B) ⨟ (homT p₁ ⊙ p₂)) :=
            PEq.symm (homT_precomp _ _)
        _ ≡ₜ homT ((pureT A ⨟ homT p₁) ⊙ (Term.id B ⨟ p₂)) := by
            refine homT_congr ?_
            calc (prodF (pureT A) (Term.id B) ⨟ (prodF (homT p₁) p₂ ⨟ binconcat (A ⊕' B)))
                ≡ₜ ((prodF (pureT A) (Term.id B) ⨟ prodF (homT p₁) p₂) ⨟
                    binconcat (A ⊕' B)) := PEq.symm (PEq.comp_assoc _ _ _)
              _ ≡ₜ (prodF (pureT A ⨟ homT p₁) (Term.id B ⨟ p₂) ⨟ binconcat (A ⊕' B)) :=
                  PEq.compL _ (PEq.prod_comp _ _ _ _)
        _ ≡ₜ homT (p₁ ⊙ p₂) := homT_congr (fdot_congr (homT_pure p₁) (PEq.id_comp _))
    have hsnd : (either (nilT A) (pureT A) ⨟ homT p₁) ≡ₜ
        either (nilT (A ⊕' B)) p₁ := by
      calc (either (nilT A) (pureT A) ⨟ homT p₁)
          ≡ₜ either (nilT A ⨟ homT p₁) (pureT A ⨟ homT p₁) := either_comp _ _ _
        _ ≡ₜ either (nilT (A ⊕' B)) p₁ := either_congr (homT_nil p₁) (homT_pure p₁)
    calc (prodF (listF (prodF (pureT A) (Term.id B))) (either (nilT A) (pureT A)) ⨟
            (prodF (homT (homT p₁ ⊙ p₂)) (homT p₁) ⨟ binconcat (A ⊕' B)))
        ≡ₜ ((prodF (listF (prodF (pureT A) (Term.id B))) (either (nilT A) (pureT A)) ⨟
            prodF (homT (homT p₁ ⊙ p₂)) (homT p₁)) ⨟ binconcat (A ⊕' B)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B)) ⨟ homT (homT p₁ ⊙ p₂))
            (either (nilT A) (pureT A) ⨟ homT p₁) ⨟ binconcat (A ⊕' B)) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (homT (p₁ ⊙ p₂)) (either (nilT (A ⊕' B)) p₁) ⨟ binconcat (A ⊕' B)) :=
          PEq.compL _ (PEq.congr_prodF hfst hsnd)
  -- each of the two factors is provably injective
  have hinj₁ : ProvablyInjective (listF (prodF (pureT A) (Term.id B))) :=
    ProvablyInjective.listF (ProvablyInjective.prodF (pureT_injective A)
      (ProvablyInjective.id B))
  have hinj₂ : ProvablyInjective (either (nilT A) (pureT A)) := by
    refine ⟨uncons A ⨟ sumF (Term.id Ty.unit) (fst A A⋆), ?_⟩
    calc (either (nilT A) (pureT A) ⨟ (uncons A ⨟ sumF (Term.id Ty.unit) (fst A A⋆)))
        ≡ₜ ((either (nilT A) (pureT A) ⨟ uncons A) ⨟
            sumF (Term.id Ty.unit) (fst A A⋆)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (either (nilT A ⨟ uncons A) (pureT A ⨟ uncons A) ⨟
            sumF (Term.id Ty.unit) (fst A A⋆)) := PEq.compL _ (either_comp _ _ _)
      _ ≡ₜ (either (inl Ty.unit (A ⊗ A⋆))
              (pairR (Term.id A) (nilT A) ⨟ inr Ty.unit (A ⊗ A⋆)) ⨟
            sumF (Term.id Ty.unit) (fst A A⋆)) :=
          PEq.compL _ (either_congr (nilT_uncons A) (pureT_uncons A))
      _ ≡ₜ either (inl Ty.unit (A ⊗ A⋆) ⨟ sumF (Term.id Ty.unit) (fst A A⋆))
            ((pairR (Term.id A) (nilT A) ⨟ inr Ty.unit (A ⊗ A⋆)) ⨟
              sumF (Term.id Ty.unit) (fst A A⋆)) := either_comp _ _ _
      _ ≡ₜ either (Term.id Ty.unit ⨟ inl Ty.unit A) (Term.id A ⨟ inr Ty.unit A) := by
          refine either_congr ((PEq.nat_inl _ _).trans (PEq.refl _)) ?_
          calc ((pairR (Term.id A) (nilT A) ⨟ inr Ty.unit (A ⊗ A⋆)) ⨟
                  sumF (Term.id Ty.unit) (fst A A⋆))
              ≡ₜ (pairR (Term.id A) (nilT A) ⨟
                  (inr Ty.unit (A ⊗ A⋆) ⨟ sumF (Term.id Ty.unit) (fst A A⋆))) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (pairR (Term.id A) (nilT A) ⨟ (fst A A⋆ ⨟ inr Ty.unit A)) :=
                PEq.compR _ (PEq.nat_inr _ _)
            _ ≡ₜ ((pairR (Term.id A) (nilT A) ⨟ fst A A⋆) ⨟ inr Ty.unit A) :=
                PEq.symm (PEq.comp_assoc _ _ _)
            _ ≡ₜ (Term.id A ⨟ inr Ty.unit A) :=
                PEq.compL _ (pairR_fst (Term.id A) (nilT A))
      _ ≡ₜ either (inl Ty.unit A) (inr Ty.unit A) :=
          either_congr (PEq.id_comp _) (PEq.id_comp _)
      _ ≡ₜ Term.id (Ty.unit ⊕' A) := either_inl_inr _ _
  have hcm : ProvablyInjective (cmBlockL A B) :=
    ⟨blockLT A B, (blockLT_iso A B).2⟩
  exact ProvablyInjective.of_peq (PEq.symm hfac)
    (ProvablyInjective.comp (ProvablyInjective.prodF hinj₁ hinj₂) hcm)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
