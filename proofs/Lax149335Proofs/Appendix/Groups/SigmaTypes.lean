import Lax149335Proofs.Appendix.Groups.Unprefixing
import Lax149335Proofs.Appendix.Groups.ConstFin
import Lax149335Proofs.GeneralCompleteness.Statements
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Set

/-!
# The `Σ`-encoding of the group annotations (appendix, *Completeness in the presence of
groups*)

The last appendix section finishes the completeness proof by taking the group prefix
multiplication into account.  It works with the co-product notation `Σ A = Σ_{g ∈ G} A`
rather than with `A × G`, so that the group annotation of a letter is a co-product index.
This file sets up that encoding and the notions built on it:

* the type `Σ A`, the co-projections `injSigma` and the case combinator `sigmaCase`, the
  isomorphism `A × G ≃ Σ A` (`sigmaEnc`, `sigmaDec`), distributivity over `Σ`, the type
  `T A = 1 + (Σ A)* × A` and the term `toT`;
* the variant `spref : (Σ A)* → T A` of the group prefix multiplication, with the more
  lifted output type;
* *group injections* (`Lax149335Proofs.Term.IsGroupInjection`) and *group lifts*
  (`Lax149335Proofs.Term.IsGroupLift`): a group injection is an aperiodic term which is provably
  injective with a drop one-sided inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Co-product notation

The type `A × G` is isomorphic to the co-product `Σ A = Σ_{g ∈ G} A` of `|G|` copies of `A`;
the appendix works with the latter. -/

/-- The co-product `Σ A = Σ_{g ∈ G} A` of one copy of `A` for each letter of the finite
alphabet `1 + ⋯ + 1` with `n+1` letters. -/
def sigmaTy (A : Ty) : ℕ → Ty
  | 0 => A
  | (n + 1) => A ⊕' sigmaTy A n

/-- The co-projection of `A` into the summand of `Σ A` indexed by a group element. -/
def injSigma (A : Ty) : {n : ℕ} → ⟦Ty.finAlph n⟧ → Term A (sigmaTy A n)
  | 0, _ => Term.id A
  | (n + 1), .inl _ => inl A (sigmaTy A n)
  | (n + 1), .inr g => injSigma A g ⨟ inr A (sigmaTy A n)

/-- Case reasoning on the summands of `Σ A`. -/
def sigmaCase {A B : Ty} : {n : ℕ} → (⟦Ty.finAlph n⟧ → Term A B) → Term (sigmaTy A n) B
  | 0, t => t ()
  | (_ + 1), t => either (t (.inl ())) (sigmaCase (fun g => t (.inr g)))

/-- One half of the isomorphism `A × G ≃ Σ A`. -/
def sigmaEnc (A : Ty) (n : ℕ) : Term (A ⊗ Ty.finAlph n) (sigmaTy A n) :=
  caseR (fun g => injSigma A g)

/-- The other half of the isomorphism `A × G ≃ Σ A`. -/
def sigmaDec (A : Ty) : (n : ℕ) → Term (sigmaTy A n) (A ⊗ Ty.finAlph n)
  | 0 => pairR (Term.id A) (Term.id Ty.unit)
  | (n + 1) =>
      either (pairR (Term.id A) (inl Ty.unit (Ty.finAlph n)))
        (sigmaDec A n ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)))

/-- Distributing a product over the co-product `Σ`. -/
def distSigmaR (X A : Ty) : (n : ℕ) → Term (X ⊗ sigmaTy A n) (sigmaTy (X ⊗ A) n)
  | 0 => Term.id (X ⊗ A)
  | (n + 1) => distR X A (sigmaTy A n) ⨟ sumF (Term.id (X ⊗ A)) (distSigmaR X A n)

/-- The type `T A = 1 + Σ((Σ A)* × A)`, in which the last group element of a list is directly
accessible. -/
def tTy (A : Ty) (n : ℕ) : Ty := Ty.unit ⊕' sigmaTy (((sigmaTy A n)⋆) ⊗ A) n

/-- The isomorphism `(Σ A)* → T A`, given by `unsnoc` followed by distributivity; it is a
lift. -/
def toT (A : Ty) (n : ℕ) : Term ((sigmaTy A n)⋆) (tTy A n) :=
  unsnoc (sigmaTy A n) ⨟
    sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n)

/-- The variant `spref : (Σ A)* → T A` of the group prefix multiplication used in the
appendix: the input type is the less lifted one, the output type the more lifted one. -/
def spref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) : Term ((sigmaTy A n)⋆) (tTy A n) :=
  listF (sigmaDec A n) ⨟ pref A G ⨟ listF (sigmaEnc A n) ⨟ toT A n

/-- **Definition (Group injection).**  A term is a *group injection* if it is aperiodic, it
is provably injective, and its one-sided inverse is a drop. -/
def IsGroupInjection {A B : Ty} (f : Term A B) : Prop :=
  IsAperiodic f ∧ ∃ f' : Term B A, (f ⨟ f') ≡ₜ Term.id A ∧ IsDrop f'
/-! Basic computation rules for the co-product notation. -/

/-- The co-projections into `Σ A` are drops. -/
theorem isDrop_injSigma (A : Ty) : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) → IsDrop (injSigma A g)
  | 0, _ => IsDrop.id A
  | (_ + 1), .inl _ => IsDrop.inl _ _
  | (_ + 1), .inr g => IsDrop.comp (isDrop_injSigma A g) (IsDrop.inr _ _)

/-- The co-projections into `Σ A` are aperiodic. -/
theorem isAperiodic_injSigma (A : Ty) : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) →
    IsAperiodic (injSigma A g)
  | 0, _ => by simp [IsAperiodic, usesPref, injSigma]
  | (_ + 1), .inl _ => by simp [IsAperiodic, usesPref, injSigma]
  | (_ + 1), .inr g => by
      simpa [IsAperiodic, usesPref, injSigma] using isAperiodic_injSigma A g

/-- Case reasoning on `Σ A` yields an aperiodic term as soon as all the cases are
aperiodic. -/
theorem isAperiodic_sigmaCase {A B : Ty} : {n : ℕ} → {t : ⟦Ty.finAlph n⟧ → Term A B} →
    (∀ g, IsAperiodic (t g)) → IsAperiodic (sigmaCase (n := n) t)
  | 0, _, h => h ()
  | (_ + 1), _, h => by
      have htail := isAperiodic_sigmaCase (fun g => h (Sum.inr g))
      have hhead := h (Sum.inl ())
      simp only [IsAperiodic, sigmaCase, either, usesPref, Bool.or_eq_false_iff] at htail hhead ⊢
      exact ⟨⟨hhead, htail⟩, trivial⟩

/-- Case reasoning on `Σ A` yields a drop as soon as all the cases are drops. -/
theorem isDrop_sigmaCase {A B : Ty} : {n : ℕ} → {t : ⟦Ty.finAlph n⟧ → Term A B} →
    (∀ g, IsDrop (t g)) → IsDrop (sigmaCase (n := n) t)
  | 0, _, h => h ()
  | (_ + 1), _, h =>
      IsDrop.comp (IsDrop.sumF (h (.inl ())) (isDrop_sigmaCase (fun g => h (.inr g))))
        (IsDrop.codiag _)

/-- Case reasoning computes on the co-projections. -/
theorem injSigma_sigmaCase {A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (g : ⟦Ty.finAlph n⟧) → (injSigma A g ⨟ sigmaCase t) ≡ₜ t g
  | 0, t, () => PEq.id_comp _
  | (_ + 1), t, .inl () => inl_either _ _
  | (n + 1), t, .inr g => by
      calc ((injSigma A g ⨟ inr A (sigmaTy A n)) ⨟
              either (t (.inl ())) (sigmaCase (fun g' => t (.inr g'))))
          ≡ₜ (injSigma A g ⨟ (inr A (sigmaTy A n) ⨟
              either (t (.inl ())) (sigmaCase (fun g' => t (.inr g'))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (injSigma A g ⨟ sigmaCase (fun g' => t (.inr g'))) :=
            PEq.compR _ (inr_either _ _)
        _ ≡ₜ t (.inr g) := injSigma_sigmaCase (fun g' => t (.inr g')) g

/-- Case reasoning is a congruence. -/
theorem sigmaCase_congr {A B : Ty} : {n : ℕ} → {t t' : ⟦Ty.finAlph n⟧ → Term A B} →
    (∀ g, t g ≡ₜ t' g) → sigmaCase t ≡ₜ sigmaCase t'
  | 0, _, _, h => h ()
  | (_ + 1), _, _, h =>
      either_congr (h (.inl ())) (sigmaCase_congr (fun g => h (.inr g)))

/-- Case reasoning commutes with post-composition. -/
theorem sigmaCase_comp {A B C : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (u : Term B C) → (sigmaCase t ⨟ u) ≡ₜ sigmaCase (fun g => t g ⨟ u)
  | 0, _, _ => PEq.refl _
  | (_ + 1), t, u =>
      (either_comp _ _ _).trans
        (either_congr (PEq.refl _) (sigmaCase_comp (fun g => t (.inr g)) u))

/-- Case reasoning on the co-projections themselves is the identity. -/
theorem sigmaCase_injSigma (A : Ty) : (n : ℕ) →
    sigmaCase (n := n) (fun g => injSigma A g) ≡ₜ Term.id (sigmaTy A n)
  | 0 => PEq.refl _
  | (n + 1) => by
      calc either (inl A (sigmaTy A n))
              (sigmaCase (fun g => injSigma A g ⨟ inr A (sigmaTy A n)))
          ≡ₜ either (inl A (sigmaTy A n))
              (sigmaCase (fun g => injSigma A g) ⨟ inr A (sigmaTy A n)) :=
            either_congr (PEq.refl _) (PEq.symm (sigmaCase_comp _ _))
        _ ≡ₜ either (inl A (sigmaTy A n)) (Term.id (sigmaTy A n) ⨟ inr A (sigmaTy A n)) :=
            either_congr (PEq.refl _) (PEq.compL _ (sigmaCase_injSigma A n))
        _ ≡ₜ either (inl A (sigmaTy A n)) (inr A (sigmaTy A n)) :=
            either_congr (PEq.refl _) (PEq.id_comp _)
        _ ≡ₜ Term.id (A ⊕' sigmaTy A n) := either_inl_inr _ _

/-- **Definition (Grouplift).**  Grouplifts are defined like lifts, except that two new kinds
of atomic lifts are allowed: group injections and Simon lifts.  A *Simon lift* is a
composition of `spref` with a lift which is an isomorphism whose inverse is a drop; the
existence of such a lift is the content of the Simon lift lemma below. -/
inductive IsGroupLift : {A B : Ty} → Term A B → Prop
  /-- Every lift is a grouplift. -/
  | ofLift {A B : Ty} {f : Term A B} : IsLift f → IsGroupLift f
  /-- Every group injection is a grouplift. -/
  | groupInj {A B : Ty} {f : Term A B} : IsGroupInjection f → IsGroupLift f
  /-- Simon lifts are grouplifts. -/
  | simon {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) {S : Ty} (lam : Term (tTy A n) S)
      (inv : Term S ((sigmaTy A n)⋆)) : IsLift lam → IsDrop inv →
      ((spref A G ⨟ lam) ⨟ inv) ≡ₜ Term.id ((sigmaTy A n)⋆) →
      (inv ⨟ (spref A G ⨟ lam)) ≡ₜ Term.id S →
      IsGroupLift (spref A G ⨟ lam)
  /-- Grouplifts are closed under composition. -/
  | comp {A B C : Ty} {f : Term A B} {g : Term B C} :
      IsGroupLift f → IsGroupLift g → IsGroupLift (f ⨟ g)
  /-- Grouplifts are closed under functoriality of products. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsGroupLift f → IsGroupLift g → IsGroupLift (Term.prodF f g)
  /-- Grouplifts are closed under functoriality of co-products. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsGroupLift f → IsGroupLift g → IsGroupLift (Term.sumF f g)
  /-- Grouplifts are closed under functoriality of lists. -/
  | listF {A B : Ty} {f : Term A B} : IsGroupLift f → IsGroupLift (Term.listF f)
/- **Lemma (Simon lift)** (appendix, *Grouplifts*).  There is a list-polynomial functor `S`
such that every type `A` carries a Simon lift `(Σ A)* → S A`, namely `spref` followed by a
lift, which is an isomorphism with a drop inverse, and which makes `spref` factor through a
drop `δ : S A ⇒ T A`.  Moreover there is a drop injection `σ` making `δ` commute with `last`,
and all of this is natural in `A`.

The statement and its proof are in `Lax149335Proofs.Appendix.SimonLiftGeneral`
(`Lax149335Proofs.Term.simon_lift`): the construction of the Simon lift needs the whole appendix
development, which is downstream of this file. -/

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
