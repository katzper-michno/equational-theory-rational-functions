import Lax149335Proofs.RationalFunctions.SimpleRational
import Lax149335Proofs.SimpleCompleteness.Statements
import Lax149335Proofs.Appendix.Groups.ShiftScan
import Lax149335Proofs.Appendix.ConcatenationMaps

/-!
# The bridge between the two syntaxes for simple rational terms

Simple rational terms appear in the paper in two guises: as the terms of Definition 2.5,
formalised by `Lax149335Proofs.SimpleTerm`, for which Theorem 2.6 gives a complete equational theory
(`Lax149335Proofs.SimpleTerm.SEq`), and as the rational terms of Section 3 that are built by the
combinators of Definition 2.5, formalised by `Lax149335Proofs.IsSimple`.

This file relates the two.  Every term of the first kind is interpreted as a rational term
(`Lax149335Proofs.SimpleTerm.interp`), the interpretation is simple and denotation preserving, and
conversely every simple rational term is provably equal to the interpretation of a term of
the first kind.  Finally, every rule of the equational theory of Theorem 2.6 is admissible
for provable equality of rational terms, *provided* the conjugacy rule of Lemma 6.1 is
available for input types of smaller list nesting depth (`Lax149335Proofs.ConjBelow`); this is the
form in which the proof of Lemma 6.1 uses Theorem 2.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Values are determined by their denotation -/

/-- Two values with the same denotation are provably equal. -/
theorem value_eq_of_den {A : Ty} (v u : Value A) (h : v.den () = u.den ()) : v ≡ₜ u := by
  have hv : v ≡ₜ encV A (v.den ()) := (PEq.symm (PEq.id_comp v)).trans (computes v ())
  have hu : u ≡ₜ encV A (u.den ()) := (PEq.symm (PEq.id_comp u)).trans (computes u ())
  rw [h] at hv
  exact hv.trans (PEq.symm hu)

/-- The denotation of the value representing an element is that element. -/
theorem den_encV : (A : Ty) → (x : ⟦A⟧) → (encV A x).den () = x
  | .unit, x => by cases x; rfl
  | .prod A B, x => by
      show ((encV A x.1).den (), (encV B x.2).den ()) = x
      rw [den_encV A x.1, den_encV B x.2]
      rfl
  | .sum A B, x => by
      match x with
      | .inl a => show Sum.inl ((encV A a).den ()) = _; rw [den_encV A a]
      | .inr b => show Sum.inr ((encV B b).den ()) = _; rw [den_encV B b]
  | .list A, l => by
      induction l with
      | nil => rfl
      | cons a t ih =>
          show (Term.dotL (Term.sing (encV A a)) (encV A⋆ t)).den () = a :: t
          rw [den_dotL, ih]
          show ((encV A a).den () :: []) ++ t = a :: t
          rw [den_encV A a]
          rfl

namespace Term

/-- Pre-composition commutes with prepending a value. -/
theorem comp_dotL {X A B : Ty} (p : Term X A) (w : Value B⋆) (f : Term A B⋆) :
    (p ⨟ dotL w f) ≡ₜ dotL w (p ⨟ f) :=
  (PEq.symm (PEq.comp_assoc _ _ _)).trans
    (PEq.compL _ (comp_pairL p w f))

/-- Pre-composition commutes with appending a value. -/
theorem comp_dotR {X A B : Ty} (p : Term X A) (f : Term A B⋆) (w : Value B⋆) :
    (p ⨟ dotR f w) ≡ₜ dotR (p ⨟ f) w :=
  (PEq.symm (PEq.comp_assoc _ _ _)).trans
    (PEq.compL _ (comp_pairR p f w))

/-- Prepending a value distributes over a co-pairing. -/
theorem dotL_either {A₁ A₂ B : Ty} (w : Value B⋆) (f₁ : Term A₁ B⋆) (f₂ : Term A₂ B⋆) :
    dotL w (either f₁ f₂) ≡ₜ either (dotL w f₁) (dotL w f₂) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A₁ A₂ ⨟ dotL w (either f₁ f₂))
        ≡ₜ dotL w (inl A₁ A₂ ⨟ either f₁ f₂) := comp_dotL _ _ _
      _ ≡ₜ dotL w f₁ := dotL_congr (PEq.refl _) (inl_either f₁ f₂)
      _ ≡ₜ (inl A₁ A₂ ⨟ either (dotL w f₁) (dotL w f₂)) :=
          PEq.symm (inl_either _ _)
  · calc (inr A₁ A₂ ⨟ dotL w (either f₁ f₂))
        ≡ₜ dotL w (inr A₁ A₂ ⨟ either f₁ f₂) := comp_dotL _ _ _
      _ ≡ₜ dotL w f₂ := dotL_congr (PEq.refl _) (inr_either f₁ f₂)
      _ ≡ₜ (inr A₁ A₂ ⨟ either (dotL w f₁) (dotL w f₂)) :=
          PEq.symm (inr_either _ _)

/-- Appending a value distributes over a co-pairing. -/
theorem dotR_either {A₁ A₂ B : Ty} (f₁ : Term A₁ B⋆) (f₂ : Term A₂ B⋆) (w : Value B⋆) :
    dotR (either f₁ f₂) w ≡ₜ either (dotR f₁ w) (dotR f₂ w) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A₁ A₂ ⨟ dotR (either f₁ f₂) w)
        ≡ₜ dotR (inl A₁ A₂ ⨟ either f₁ f₂) w := comp_dotR _ _ _
      _ ≡ₜ dotR f₁ w := dotR_congr (inl_either f₁ f₂) (PEq.refl _)
      _ ≡ₜ (inl A₁ A₂ ⨟ either (dotR f₁ w) (dotR f₂ w)) :=
          PEq.symm (inl_either _ _)
  · calc (inr A₁ A₂ ⨟ dotR (either f₁ f₂) w)
        ≡ₜ dotR (inr A₁ A₂ ⨟ either f₁ f₂) w := comp_dotR _ _ _
      _ ≡ₜ dotR f₂ w := dotR_congr (inr_either f₁ f₂) (PEq.refl _)
      _ ≡ₜ (inr A₁ A₂ ⨟ either (dotR f₁ w) (dotR f₂ w)) :=
          PEq.symm (inr_either _ _)

end Term

namespace SimpleTerm

variable {B : Ty}

/-- The interpretation of a simple rational term of Definition 2.5 as a rational term of
Section 3. -/
def interp (B : Ty) : {A : Ty} → SimpleTerm ⟦B⟧ A → Term A B⋆
  | _, .empty => nilT B
  | _, .either t₁ t₂ => Term.either (interp B t₁) (interp B t₂)
  | _, .conc t₁ t₂ => (interp B t₁) ⊙ (interp B t₂)
  | _, .hom t => homT (interp B t)
  | _, .pre w t => Term.dotL (encV B⋆ w) (interp B t)
  | _, .post t w => Term.dotR (interp B t) (encV B⋆ w)

/-- The interpretation of a simple rational term is a simple rational term in the sense of
`Lax149335Proofs.IsSimple`. -/
theorem interp_isSimple : {A : Ty} → (t : SimpleTerm ⟦B⟧ A) → IsSimple B (interp B t)
  | _, .empty => IsSimple.nil
  | _, .either t₁ t₂ => IsSimple.either (interp_isSimple t₁) (interp_isSimple t₂)
  | _, .conc t₁ t₂ => IsSimple.fdot (interp_isSimple t₁) (interp_isSimple t₂)
  | _, .hom t => IsSimple.hom (interp_isSimple t)
  | _, .pre _ t => IsSimple.dotL _ (interp_isSimple t)
  | _, .post t _ => IsSimple.dotR _ (interp_isSimple t)

/-- The interpretation preserves the denotation. -/
theorem den_interp : {A : Ty} → (t : SimpleTerm ⟦B⟧ A) → (interp B t).den = t.den
  | _, .empty => rfl
  | _, .either t₁ t₂ => by
      funext x
      match x with
      | .inl a =>
          show (interp B t₁).den a = SimpleTerm.den t₁ a
          rw [den_interp t₁]
      | .inr b =>
          show (interp B t₂).den b = SimpleTerm.den t₂ b
          rw [den_interp t₂]
  | _, .conc t₁ t₂ => by
      funext x
      simp only [interp, den_fdot, den_interp t₁, den_interp t₂]
      rfl
  | _, .hom t => by
      funext l
      show (l.map (interp B t).den).flatten = (l.map (SimpleTerm.den t)).flatten
      rw [den_interp t]
  | _, .pre w t => by
      funext x
      simp only [interp, den_dotL, den_interp t, den_encV]
      rfl
  | _, .post t w => by
      funext x
      simp only [interp, den_dotR, den_interp t, den_encV]
      rfl

/-- Every simple rational term is provably equal to the interpretation of a simple rational
term of Definition 2.5. -/
theorem exists_interp {A : Ty} {f : Term A B⋆} (hf : IsSimple B f) :
    ∃ t : SimpleTerm ⟦B⟧ A, interp B t ≡ₜ f := by
  induction hf with
  | nil => exact ⟨.empty, PEq.refl _⟩
  | either _ _ ih₁ ih₂ =>
      obtain ⟨t₁, h₁⟩ := ih₁
      obtain ⟨t₂, h₂⟩ := ih₂
      exact ⟨.either t₁ t₂, Term.either_congr h₁ h₂⟩
  | fdot _ _ ih₁ ih₂ =>
      obtain ⟨t₁, h₁⟩ := ih₁
      obtain ⟨t₂, h₂⟩ := ih₂
      exact ⟨.conc t₁ t₂, Term.fdot_congr h₁ h₂⟩
  | hom _ ih =>
      obtain ⟨t, h⟩ := ih
      exact ⟨.hom t, Term.homT_congr h⟩
  | dotL w _ ih =>
      obtain ⟨t, h⟩ := ih
      refine ⟨.pre (w.den ()) t, Term.dotL_congr ?_ h⟩
      exact value_eq_of_den _ _ (by rw [den_encV])
  | dotR w _ ih =>
      obtain ⟨t, h⟩ := ih
      refine ⟨.post t (w.den ()), Term.dotR_congr h ?_⟩
      exact value_eq_of_den _ _ (by rw [den_encV])

/-! ### Transporting the equational theory of Theorem 2.6 -/

/-- The conjugacy rule (18) of Lemma 6.1, for input types of list nesting depth smaller than
`d`.  This is the induction hypothesis under which the proof of Lemma 6.1 uses the
completeness of the equational theory of Theorem 2.6. -/
def _root_.Lax149335Proofs.ConjBelow (B : Ty) (d : ℕ) : Prop :=
  ∀ {A : Ty}, A.listDepth < d → ∀ (f g : Term A B⋆), IsSimple B f → IsSimple B g →
    ∀ w : Value B⋆, dotR f w ≡ₜ dotL w g → dotR (homT f) w ≡ₜ dotL w (homT g)

/-- The value representing the concatenation of two lists is the concatenation of the two
values representing them. -/
theorem encV_append (B : Ty) (w v : List ⟦B⟧) :
    encV B⋆ (w ++ v) ≡ₜ Term.dotL (encV B⋆ w) (encV B⋆ v) :=
  value_eq_of_den _ _ (by simp only [Term.den_dotL, den_encV]; rfl)

/-- **Every rule of the equational theory of Theorem 2.6 is admissible** for provable
equality of rational terms, as long as the conjugacy rule is available for input types of
smaller list nesting depth. -/
theorem interp_of_SEq {d : ℕ} (hconj : ConjBelow B d) :
    ∀ {A : Ty} {t₁ t₂ : SimpleTerm ⟦B⟧ A}, SEq t₁ t₂ → A.listDepth ≤ d →
      interp B t₁ ≡ₜ interp B t₂ := by
  intro A t₁ t₂ h
  induction h with
  | refl f => exact fun _ => PEq.refl _
  | symm _ ih => exact fun hA => PEq.symm (ih hA)
  | trans _ _ ih₁ ih₂ => exact fun hA => (ih₁ hA).trans (ih₂ hA)
  | congr_either _ _ ih₁ ih₂ =>
      intro hA
      simp only [Ty.listDepth, max_le_iff] at hA
      exact Term.either_congr (ih₁ hA.1) (ih₂ hA.2)
  | congr_conc _ _ ih₁ ih₂ =>
      intro hA
      simp only [Ty.listDepth, max_le_iff] at hA
      exact Term.fdot_congr (ih₁ hA.1) (ih₂ hA.2)
  | congr_hom _ ih =>
      intro hA
      simp only [Ty.listDepth] at hA
      exact Term.homT_congr (ih (by omega))
  | congr_pre w _ ih => exact fun hA => Term.dotL_congr (PEq.refl _) (ih hA)
  | congr_post w _ ih => exact fun hA => Term.dotR_congr (ih hA) (PEq.refl _)
  | post_post f w v =>
      intro _
      exact (Term.dotR_dotR (interp B f) _ _).trans
        (Term.dotR_congr (PEq.refl _) (PEq.symm (encV_append B w v)))
  | pre_pre f w v =>
      intro _
      exact (Term.dotL_dotL _ _ (interp B f)).trans
        (Term.dotL_congr (PEq.symm (encV_append B w v)) (PEq.refl _))
  | post_nil f => exact fun _ => Term.dotR_nil (interp B f)
  | pre_nil f => exact fun _ => Term.dotL_nil (interp B f)
  | pre_post f w v => exact fun _ => Term.dotR_dotL _ (interp B f) _
  | conc_shift f g w => exact fun _ => Term.fdot_dotR_dotL (interp B f) (interp B g) _
  | case_left _ ih =>
      intro hA
      simp only [Ty.listDepth, max_le_iff] at hA
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hA
      exact (Term.fdot_either_distL _ _ _).trans
        ((PEq.compR _ (ih (by
            simp only [Ty.listDepth, max_le_iff]; exact ⟨⟨h₁, h₃⟩, ⟨h₂, h₃⟩⟩))).trans
          (PEq.symm (Term.fdot_either_distL _ _ _)))
  | case_right _ ih =>
      intro hA
      simp only [Ty.listDepth, max_le_iff] at hA
      obtain ⟨h₁, h₂, h₃⟩ := hA
      exact (Term.fdot_either_distR _ _ _).trans
        ((PEq.compR _ (ih (by
            simp only [Ty.listDepth, max_le_iff]; exact ⟨⟨h₁, h₂⟩, ⟨h₁, h₃⟩⟩))).trans
          (PEq.symm (Term.fdot_either_distR _ _ _)))
  | @conjugacy A f g w _ ih =>
      intro hA
      simp only [Ty.listDepth] at hA
      exact hconj (by omega) _ _ (interp_isSimple f) (interp_isSimple g) _ (ih (by omega))
  | move_empty w =>
      intro _
      exact value_eq_of_den _ _ (by
        simp only [Term.den_dotL, Term.den_dotR, den_encV, interp, Term.den_nilT]
        simp)
  | pre_either w f₁ f₂ => exact fun _ => Term.dotL_either _ _ _
  | post_either w f₁ f₂ => exact fun _ => Term.dotR_either _ _ _
  | pre_conc w f₁ f₂ => exact fun _ => PEq.symm (Term.dotL_fdot _ _ _)
  | post_conc w f₁ f₂ => exact fun _ => PEq.symm (Term.dotR_fdot _ _ _)

end SimpleTerm

/-! ### The completeness rule of Lemma 6.1 -/

/-- **The completeness rule (17) of Lemma 6.1**, given the conjugacy rule (18) for input
types of smaller list nesting depth: two simple rational terms with the same denotation are
provably equal.  This is the step of the proof of Lemma 6.1 that appeals to Theorem 2.6. -/
theorem completeness_rule_of_conjBelow {B : Ty} {d : ℕ} (hconj : ConjBelow B d)
    {A : Ty} (hA : A.listDepth ≤ d) (f g : Term A B⋆)
    (hf : IsSimple B f) (hg : IsSimple B g) (hden : f.den = g.den) : f ≡ₜ g := by
  obtain ⟨tf, hft⟩ := SimpleTerm.exists_interp hf
  obtain ⟨tg, hgt⟩ := SimpleTerm.exists_interp hg
  have hdent : tf.den = tg.den := by
    rw [← SimpleTerm.den_interp tf, ← SimpleTerm.den_interp tg, PEq.sound hft, PEq.sound hgt,
      hden]
  exact (PEq.symm hft).trans
    ((SimpleTerm.interp_of_SEq hconj (SimpleTerm.SEq.complete tf tg hdent) hA).trans hgt)

end Lax149335Proofs
