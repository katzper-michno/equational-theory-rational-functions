import Lax149335Proofs.Appendix.Drops.ShiftExchange
import Lax149335Proofs.Appendix.Drops.UnshiftNormalForm
import Lax149335Proofs.Appendix.Drops.DropNormalisation

/-!
# The case of `unshift` of the list normalisation lemma (appendix, *Normalisation with list
co-domain*)

This file proves the one step of the list normalisation lemma
(`Lax149335Proofs.Appendix.Drops.ListNormalisation`) that needs the shift exchange lemma of
`Lax149335Proofs.Appendix.Drops.ShiftExchange`: a drop `f : A ⇒ 1 + S × (T × S)* × T` followed by
the atom `unshift : 1 + S × (T × S)* × T ⇒ (S × T)*` is normalisable
(`Lax149335Proofs.normListable_comp_unshift`).

The argument is the case *Shift* of the appendix proof.

* The drop `f` is normalised with the co-product normalisation lemma
  (`Lax149335Proofs.drops_with_sum_codomain_tree`) and then, on the non-empty summand, twice with
  the product normalisation lemma (`Lax149335Proofs.drops_with_prod_codomain`).  This exhibits `f`,
  after a lift, as a co-pairing whose leaves are the erased empty summand and the terms
  `x × (m × y)` with `x : X ⇒ S`, `m : M ⇒ (T × S)*` and `y : Y ⇒ T` drops of at most the
  rank of `f`.
* The prime drop `unshift` is itself a lift followed by a normal shape
  (`Lax149335Proofs.Term.unshift_normal_form`), and the lift in question applies `shift` to the
  middle component `(T × S)*` and distributes the resulting co-product to the outside; this
  is the vertical lift `id × shift × id` of the diagram of the appendix.
* The middle component `m` has a list codomain and at most the rank of `f`, so the induction
  hypothesis of the list normalisation lemma puts it in normal form, and the shift exchange
  lemma (`Lax149335Proofs.exchange_normal_shift`) pushes it through `shift`: `m ; shift` becomes a
  lift followed by a co-pairing of the shapes `(1;1); Left` and
  `((snd; x') × (m' × (fst; y'))); Right`.
* Each of those two shapes, plugged into the remaining part of the normal form of `unshift`
  (`Lax149335Proofs.Term.unshiftTail`), produces a normal shape: the drop `k` of the appendix
  diagram, which is the co-pairing of `[id × snd]` and `[id] ⊙ id ⊙ [id]`.  The first shape
  gives the single pair `[x × y]`, the second one the concatenation
  `[x × (snd; x')] ⊙ m' ⊙ [(fst; y') × y]`.

The bound obtained on the leaves of the resulting normal shape is `rank f + 1`, which is
exactly what the induction of the list normalisation lemma needs, since
`rank (f ⨟ unshift) = rank f + 1`.  The extra composition is the one paid for by the
projections `snd` and `fst` that the shift exchange lemma exposes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty} {r : ℕ}

namespace Term

/-! ### The re-association of the non-empty case

The lift `Lax149335Proofs.Term.unshiftRegroup` of `Lax149335Proofs.Appendix.Drops.UnshiftNormalForm`
re-associates `s ⊗ ((t ⊗ (m ⊗ s')) ⊗ t')` into `(s ⊗ t) ⊗ (m ⊗ (s' ⊗ t'))`.  Here is that
re-association at arbitrary types, together with its naturality. -/

/-- The re-association `A₁ ⊗ ((A₂ ⊗ (A₃ ⊗ A₄)) ⊗ A₅) ⊸ (A₁ ⊗ A₂) ⊗ (A₃ ⊗ (A₄ ⊗ A₅))`. -/
def regroup5 (A₁ A₂ A₃ A₄ A₅ : Ty) :
    Term (A₁ ⊗ ((A₂ ⊗ (A₃ ⊗ A₄)) ⊗ A₅)) ((A₁ ⊗ A₂) ⊗ (A₃ ⊗ (A₄ ⊗ A₅))) :=
  (prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟ assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅)) ⨟
    prodF (Term.id (A₁ ⊗ A₂)) (assocR A₃ A₄ A₅)

theorem isLift_regroup5 (A₁ A₂ A₃ A₄ A₅ : Ty) : IsLift (regroup5 A₁ A₂ A₃ A₄ A₅) :=
  IsLift.comp
    (IsLift.comp (IsLift.prodF (IsLift.id _) (IsLift.assocR _ _ _)) (IsLift.assocL _ _ _))
    (IsLift.prodF (IsLift.id _) (IsLift.assocR _ _ _))

/-- `unshiftRegroup` is the re-association `regroup5` at the types of the appendix. -/
theorem unshiftRegroup_eq (S T : Ty) :
    unshiftRegroup S T = regroup5 S T ((S ⊗ T)⋆) S T := rfl

/-- Naturality of the re-association. -/
theorem regroup5_natural {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Ty} (f₁ : Term A₁ B₁)
    (f₂ : Term A₂ B₂) (f₃ : Term A₃ B₃) (f₄ : Term A₄ B₄) (f₅ : Term A₅ B₅) :
    (prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟ regroup5 B₁ B₂ B₃ B₄ B₅) ≡ₜ
      (regroup5 A₁ A₂ A₃ A₄ A₅ ⨟ prodF (prodF f₁ f₂) (prodF f₃ (prodF f₄ f₅))) := by
  have step₁ :
      (prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟
          prodF (Term.id B₁) (assocR B₂ (B₃ ⊗ B₄) B₅)) ≡ₜ
        (prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
          prodF f₁ (prodF f₂ (prodF (prodF f₃ f₄) f₅))) := by
    calc (prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟
            prodF (Term.id B₁) (assocR B₂ (B₃ ⊗ B₄) B₅))
        ≡ₜ prodF (f₁ ⨟ Term.id B₁)
            (prodF (prodF f₂ (prodF f₃ f₄)) f₅ ⨟ assocR B₂ (B₃ ⊗ B₄) B₅) :=
          PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id A₁ ⨟ f₁)
            (assocR A₂ (A₃ ⊗ A₄) A₅ ⨟ prodF f₂ (prodF (prodF f₃ f₄) f₅)) :=
          PEq.congr_prodF ((PEq.comp_id _).trans (PEq.symm (PEq.id_comp _)))
            (PEq.nat_assocR _ _ _)
      _ ≡ₜ (prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            prodF f₁ (prodF f₂ (prodF (prodF f₃ f₄) f₅))) :=
          PEq.symm (PEq.prod_comp _ _ _ _)
  have step₂ :
      (prodF f₁ (prodF f₂ (prodF (prodF f₃ f₄) f₅)) ⨟ assocL B₁ B₂ ((B₃ ⊗ B₄) ⊗ B₅)) ≡ₜ
        (assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅) ⨟
          prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅)) := PEq.nat_assocL _ _ _
  have step₃ :
      (prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅) ⨟
          prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) ≡ₜ
        (prodF (Term.id (A₁ ⊗ A₂)) (assocR A₃ A₄ A₅) ⨟
          prodF (prodF f₁ f₂) (prodF f₃ (prodF f₄ f₅))) := by
    calc (prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅))
        ≡ₜ prodF (prodF f₁ f₂ ⨟ Term.id (B₁ ⊗ B₂))
            (prodF (prodF f₃ f₄) f₅ ⨟ assocR B₃ B₄ B₅) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id (A₁ ⊗ A₂) ⨟ prodF f₁ f₂)
            (assocR A₃ A₄ A₅ ⨟ prodF f₃ (prodF f₄ f₅)) :=
          PEq.congr_prodF ((PEq.comp_id _).trans (PEq.symm (PEq.id_comp _)))
            (PEq.nat_assocR _ _ _)
      _ ≡ₜ (prodF (Term.id (A₁ ⊗ A₂)) (assocR A₃ A₄ A₅) ⨟
            prodF (prodF f₁ f₂) (prodF f₃ (prodF f₄ f₅))) :=
          PEq.symm (PEq.prod_comp _ _ _ _)
  calc (prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟ regroup5 B₁ B₂ B₃ B₄ B₅)
      ≡ₜ ((prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟
            (prodF (Term.id B₁) (assocR B₂ (B₃ ⊗ B₄) B₅) ⨟
              assocL B₁ B₂ ((B₃ ⊗ B₄) ⊗ B₅))) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF f₁ (prodF (prodF f₂ (prodF f₃ f₄)) f₅) ⨟
            prodF (Term.id B₁) (assocR B₂ (B₃ ⊗ B₄) B₅)) ⨟
              assocL B₁ B₂ ((B₃ ⊗ B₄) ⊗ B₅)) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            prodF f₁ (prodF f₂ (prodF (prodF f₃ f₄) f₅))) ⨟
              assocL B₁ B₂ ((B₃ ⊗ B₄) ⊗ B₅)) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.compL _ (PEq.compL _ step₁)
    _ ≡ₜ ((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            (prodF f₁ (prodF f₂ (prodF (prodF f₃ f₄) f₅)) ⨟
              assocL B₁ B₂ ((B₃ ⊗ B₄) ⊗ B₅))) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            (assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅) ⨟
              prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅))) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.compL _ (PEq.compR _ step₂)
    _ ≡ₜ (((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅)) ⨟
              prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅)) ⨟
            prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅)) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅)) ⨟
              (prodF (prodF f₁ f₂) (prodF (prodF f₃ f₄) f₅) ⨟
                prodF (Term.id (B₁ ⊗ B₂)) (assocR B₃ B₄ B₅))) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((prodF (Term.id A₁) (assocR A₂ (A₃ ⊗ A₄) A₅) ⨟
            assocL A₁ A₂ ((A₃ ⊗ A₄) ⊗ A₅)) ⨟
              (prodF (Term.id (A₁ ⊗ A₂)) (assocR A₃ A₄ A₅) ⨟
                prodF (prodF f₁ f₂) (prodF f₃ (prodF f₄ f₅)))) := PEq.compR _ step₃
    _ ≡ₜ (regroup5 A₁ A₂ A₃ A₄ A₅ ⨟ prodF (prodF f₁ f₂) (prodF f₃ (prodF f₄ f₅))) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-! ### The normal form of `unshift`, after the `shift` on the middle component -/

/-- The part of the normal form of `unshift` that follows the application of `shift` to the
middle component: the distribution of the resulting co-product, followed by the two normal
shapes.  This is the drop `k` of the diagram of the appendix. -/
def unshiftTail (S T : Ty) : Term (S ⊗ (shiftCod T S ⊗ T)) ((S ⊗ T)⋆) :=
  (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
      distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T

/-- The normal form of `unshift` on the non-empty summand, read through `unshiftTail`. -/
theorem inr_unshift_tail (S T : Ty) :
    (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T) ≡ₜ
      (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟ unshiftTail S T) := by
  calc (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟ unshift S T)
      ≡ₜ (inr Ty.unit (S ⊗ ((((T ⊗ S)⋆) ⊗ T))) ⨟
          either (nilT (S ⊗ T)) (unshiftCase S T ⨟ unshiftShape S T)) :=
        PEq.compR _ (unshift_normal_form S T)
    _ ≡ₜ (unshiftCase S T ⨟ unshiftShape S T) := inr_either _ _
    _ ≡ₜ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟ unshiftTail S T) := by
        calc (unshiftCase S T ⨟ unshiftShape S T)
            ≡ₜ ((prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                  prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ⨟
                (distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T) ⨟
                  unshiftShape S T)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
                  (distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T) ⨟
                    unshiftShape S T))) := PEq.comp_assoc _ _ _
          _ ≡ₜ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟ unshiftTail S T) :=
              PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))

/-- On the empty summand of the shifted middle component, `unshiftTail` produces the single
pair. -/
theorem unshiftTail_inl (S T : Ty) :
    (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
        unshiftTail S T) ≡ₜ
      (prodF (Term.id S) (snd Ty.unit T) ⨟ pureT (S ⊗ T)) := by
  have hdistL :
      (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
          prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ≡ₜ
        prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) := by
    calc (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T))
        ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T) ⨟
              distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) :=
          PEq.congr_prodF (PEq.id_comp _) (prodF_inl_distL _ _ _)
  calc (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
          unshiftTail S T)
      ≡ₜ ((prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
              distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T))) ⨟ unshiftShape S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ⨟
              distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (Term.id S) (inl (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟
            distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (PEq.compL _ hdistL)
    _ ≡ₜ (inl (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (prodF_inl_distR _ _ _)
    _ ≡ₜ unshiftLeafEmpty S T := inl_either _ _

/-- On the non-empty summand of the shifted middle component, `unshiftTail` produces the
concatenation of the head pair, the middle list and the last pair. -/
theorem unshiftTail_inr (S T : Ty) :
    (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
        unshiftTail S T) ≡ₜ
      (unshiftRegroup S T ⨟ unshiftShapeMain S T) := by
  have hdistL :
      (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
          prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ≡ₜ
        prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) := by
    calc (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T))
        ≡ₜ prodF (Term.id S ⨟ Term.id S)
            (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T) ⨟
              distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) :=
          PEq.congr_prodF (PEq.id_comp _) (prodF_inr_distL _ _ _)
  calc (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
          unshiftTail S T)
      ≡ₜ ((prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            (prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T) ⨟
              distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T))) ⨟ unshiftShape S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            prodF (Term.id S) (distL Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)) T)) ⨟
              distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (Term.id S) (inr (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟
            distR S (Ty.unit ⊗ T) ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (PEq.compL _ hdistL)
    _ ≡ₜ (inr (S ⊗ (Ty.unit ⊗ T)) (S ⊗ ((T ⊗ (((S ⊗ T)⋆) ⊗ S)) ⊗ T)) ⨟ unshiftShape S T) :=
        PEq.compL _ (prodF_inr_distR _ _ _)
    _ ≡ₜ (unshiftRegroup S T ⨟ unshiftShapeMain S T) := inr_either _ _

end Term

/-! ### The two shapes of the shift exchange lemma, plugged into `unshiftTail` -/

/-- The empty shape: the middle component of the input carries no letter, so the output is
the single pair of the two exposed letters. -/
theorem normListable_tail_empty {X Y D : Ty} {x : Term X S} {y : Term Y T}
    (hx : IsDrop x) (hrx : rank x ≤ r) (hy : IsDrop y) (hry : rank y ≤ r) :
    NormListable (S ⊗ T) (r + 1)
      (prodF x (prodF (toUnit D ⨟ inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y) ⨟
        Term.unshiftTail S T) := by
  have hsplit :
      (prodF x (prodF (toUnit D ⨟ inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y) ⨟
          Term.unshiftTail S T) ≡ₜ
        (prodF x (prodF (toUnit D) y) ⨟
          (prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            Term.unshiftTail S T)) := by
    refine PEq.compL _ ?_ |>.trans (PEq.comp_assoc _ _ _)
    calc prodF x (prodF (toUnit D ⨟ inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y)
        ≡ₜ prodF (x ⨟ Term.id S)
            (prodF (toUnit D ⨟ inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (y ⨟ Term.id T)) :=
          PEq.congr_prodF (PEq.symm (PEq.comp_id _))
            (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.comp_id _)))
      _ ≡ₜ (prodF x (prodF (toUnit D) y) ⨟
            prodF (Term.id S) (prodF (inl Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T))) :=
          PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.refl _) (PEq.prod_comp _ _ _ _)))
  refine NormListable.congr (hsplit.trans (PEq.compR _ (Term.unshiftTail_inl S T))) ?_
  refine NormListable.congr ?_ (NormListable.of_leaf
    (IsNormalListLeafLe.sing (IsDrop.prodF hx (IsDrop.comp (IsDrop.snd D Y) hy)) ?_))
  · calc (prodF x (prodF (toUnit D) y) ⨟
          (prodF (Term.id S) (snd Ty.unit T) ⨟ pureT (S ⊗ T)))
        ≡ₜ ((prodF x (prodF (toUnit D) y) ⨟ prodF (Term.id S) (snd Ty.unit T)) ⨟
            pureT (S ⊗ T)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (x ⨟ Term.id S) (prodF (toUnit D) y ⨟ snd Ty.unit T) ⨟ pureT (S ⊗ T)) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF x (snd D Y ⨟ y) ⨟ pureT (S ⊗ T)) :=
          PEq.compL _ (PEq.congr_prodF (PEq.comp_id _) (PEq.nat_snd _ _))
  · simp only [rank]
    split <;> omega

/-- The non-empty shape: the letters exposed by the shift exchange lemma are paired with the
two letters of the input, and the middle normal form is concatenated in between. -/
theorem normListable_tail_inner {X Y W X' M Y' V : Ty} {x : Term X S} {y : Term Y T}
    {x' : Term X' T} {y' : Term Y' S} {m : Term M ((S ⊗ T)⋆)}
    (hx : IsDrop x) (hrx : rank x ≤ r) (hy : IsDrop y) (hry : rank y ≤ r)
    (hx' : IsDrop x') (hrx' : rank x' ≤ r) (hy' : IsDrop y') (hry' : rank y' ≤ r)
    (hm : IsShiftInnerForm T S r m) :
    NormListable (S ⊗ T) (r + 1)
      (prodF x (prodF (prodF (Term.snd W X' ⨟ x') (prodF m (Term.fst Y' V ⨟ y')) ⨟
        inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y) ⨟ Term.unshiftTail S T) := by
  set a : Term (W ⊗ X') T := Term.snd W X' ⨟ x' with ha
  set b : Term (Y' ⊗ V) S := Term.fst Y' V ⨟ y' with hb
  -- factor out the co-projection
  have hsplit :
      (prodF x (prodF (prodF a (prodF m b) ⨟ inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y) ⨟
          Term.unshiftTail S T) ≡ₜ
        (prodF x (prodF (prodF a (prodF m b)) y) ⨟
          (prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T)) ⨟
            Term.unshiftTail S T)) := by
    refine PEq.compL _ ?_ |>.trans (PEq.comp_assoc _ _ _)
    calc prodF x (prodF (prodF a (prodF m b) ⨟ inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) y)
        ≡ₜ prodF (x ⨟ Term.id S)
            (prodF (prodF a (prodF m b) ⨟ inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S)))
              (y ⨟ Term.id T)) :=
          PEq.congr_prodF (PEq.symm (PEq.comp_id _))
            (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.comp_id _)))
      _ ≡ₜ (prodF x (prodF (prodF a (prodF m b)) y) ⨟
            prodF (Term.id S) (prodF (inr Ty.unit (T ⊗ (((S ⊗ T)⋆) ⊗ S))) (Term.id T))) :=
          PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.refl _) (PEq.prod_comp _ _ _ _)))
  -- push the drop through the re-association
  have hreg :
      (prodF x (prodF (prodF a (prodF m b)) y) ⨟ Term.unshiftRegroup S T) ≡ₜ
        (Term.regroup5 X (W ⊗ X') M (Y' ⊗ V) Y ⨟
          prodF (prodF x a) (prodF m (prodF b y))) := by
    rw [Term.unshiftRegroup_eq]
    exact Term.regroup5_natural x a m b y
  refine NormListable.congr (hsplit.trans (PEq.compR _ (Term.unshiftTail_inr S T))) ?_
  refine NormListable.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine NormListable.congr (PEq.compL _ hreg) ?_
  refine NormListable.congr (PEq.comp_assoc _ _ _) ?_
  refine NormListable.lift_comp (Term.isLift_regroup5 _ _ _ _ _) ?_
  -- the three leaves
  have hmain :
      (prodF (prodF x a) (prodF m (prodF b y)) ⨟ Term.unshiftShapeMain S T) ≡ₜ
        ((prodF x a ⨟ pureT (S ⊗ T)) ⊙ (m ⊙ (prodF b y ⨟ pureT (S ⊗ T)))) := by
    calc (prodF (prodF x a) (prodF m (prodF b y)) ⨟ Term.unshiftShapeMain S T)
        ≡ₜ ((prodF x a ⨟ (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T))) ⊙
            (prodF m (prodF b y) ⨟ (listF (Term.id (S ⊗ T)) ⊙
              (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T))))) := fdot_precomp _ _ _ _
      _ ≡ₜ ((prodF x a ⨟ pureT (S ⊗ T)) ⊙
            ((m ⨟ listF (Term.id (S ⊗ T))) ⊙
              (prodF b y ⨟ (Term.id (S ⊗ T) ⨟ pureT (S ⊗ T))))) :=
          fdot_congr (PEq.compR _ (PEq.id_comp _)) (fdot_precomp _ _ _ _)
      _ ≡ₜ ((prodF x a ⨟ pureT (S ⊗ T)) ⊙ (m ⊙ (prodF b y ⨟ pureT (S ⊗ T)))) :=
          fdot_congr (PEq.refl _)
            (fdot_congr ((PEq.compR _ (PEq.list_id _)).trans (PEq.comp_id _))
              (PEq.compR _ (PEq.id_comp _)))
  refine NormListable.congr hmain ?_
  refine NormListable.fdot ?_ (NormListable.fdot ?_ ?_)
  · refine NormListable.of_leaf (IsNormalListLeafLe.sing
      (IsDrop.prodF hx (IsDrop.comp (IsDrop.snd W X') hx')) ?_)
    simp only [ha, rank]
    split <;> omega
  · exact NormListable.of_isListNormalForm hm.isListNormalForm
  · refine NormListable.of_leaf (IsNormalListLeafLe.sing
      (IsDrop.prodF (IsDrop.comp (IsDrop.fst Y' V) hy') hy) ?_)
    simp only [hb, rank]
    split <;> omega

/-- Every shape of the shift exchange lemma, plugged into `unshiftTail`, produces a normal
shape. -/
theorem normListable_tail_shape {X Y : Ty} {x : Term X S} {y : Term Y T}
    (hx : IsDrop x) (hrx : rank x ≤ r) (hy : IsDrop y) (hry : rank y ≤ r) :
    {D : Ty} → {g : Term D (shiftCod T S)} → IsShiftExchangeShape T S r g →
      NormListable (S ⊗ T) (r + 1) (prodF x (prodF g y) ⨟ Term.unshiftTail S T)
  | _, _, .empty D => normListable_tail_empty hx hrx hy hry
  | _, _, .inner hx' hrx' hy' hry' hm =>
      normListable_tail_inner hx hrx hy hry hx' hrx' hy' hry' hm
  | _, _, @IsShiftExchangeShape.either _ _ _ D₁ D₂ g₁ g₂ h₁ h₂ => by
      have hdist :
          (prodF x (prodF (Term.either g₁ g₂) y) ⨟ Term.unshiftTail S T) ≡ₜ
            ((prodF (Term.id X) (distL D₁ D₂ Y) ⨟ distR X (D₁ ⊗ Y) (D₂ ⊗ Y)) ⨟
              Term.either (prodF x (prodF g₁ y) ⨟ Term.unshiftTail S T)
                (prodF x (prodF g₂ y) ⨟ Term.unshiftTail S T)) := by
        calc (prodF x (prodF (Term.either g₁ g₂) y) ⨟ Term.unshiftTail S T)
            ≡ₜ (prodF x (distL D₁ D₂ Y ⨟ Term.either (prodF g₁ y) (prodF g₂ y)) ⨟
                Term.unshiftTail S T) :=
              PEq.compL _ (PEq.congr_prodF (PEq.refl _) (prodF_either_distL _ _ _))
          _ ≡ₜ ((prodF (Term.id X) (distL D₁ D₂ Y) ⨟
                prodF x (Term.either (prodF g₁ y) (prodF g₂ y))) ⨟
                Term.unshiftTail S T) :=
              PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
                (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))))
          _ ≡ₜ ((prodF (Term.id X) (distL D₁ D₂ Y) ⨟
                (distR X (D₁ ⊗ Y) (D₂ ⊗ Y) ⨟
                  Term.either (prodF x (prodF g₁ y)) (prodF x (prodF g₂ y)))) ⨟
                Term.unshiftTail S T) :=
              PEq.compL _ (PEq.compR _ (prodF_either_distR _ _ _))
          _ ≡ₜ (((prodF (Term.id X) (distL D₁ D₂ Y) ⨟ distR X (D₁ ⊗ Y) (D₂ ⊗ Y)) ⨟
                Term.either (prodF x (prodF g₁ y)) (prodF x (prodF g₂ y))) ⨟
                Term.unshiftTail S T) :=
              PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ ((prodF (Term.id X) (distL D₁ D₂ Y) ⨟ distR X (D₁ ⊗ Y) (D₂ ⊗ Y)) ⨟
                (Term.either (prodF x (prodF g₁ y)) (prodF x (prodF g₂ y)) ⨟
                  Term.unshiftTail S T)) := PEq.comp_assoc _ _ _
          _ ≡ₜ ((prodF (Term.id X) (distL D₁ D₂ Y) ⨟ distR X (D₁ ⊗ Y) (D₂ ⊗ Y)) ⨟
                Term.either (prodF x (prodF g₁ y) ⨟ Term.unshiftTail S T)
                  (prodF x (prodF g₂ y) ⨟ Term.unshiftTail S T)) :=
              PEq.compR _ (either_comp _ _ _)
      refine NormListable.congr hdist ?_
      refine NormListable.lift_comp
        (IsLift.comp (IsLift.prodF (IsLift.id _) (IsLift.distL _ _ _)) (IsLift.distR _ _ _)) ?_
      exact NormListable.either (normListable_tail_shape hx hrx hy hry h₁)
        (normListable_tail_shape hx hrx hy hry h₂)

/-! ### The leaves of the normalised drop -/

/-- The non-empty summand, with the letter of `S` and the letter of `T` already exposed. -/
theorem normListable_unshift_leaf {X M Y : Ty} {x : Term X S} {m : Term M ((T ⊗ S)⋆)}
    {y : Term Y T} (hx : IsDrop x) (hrx : rank x ≤ r) (hm : IsDrop m) (hrm : rank m ≤ r)
    (hy : IsDrop y) (hry : rank y ≤ r)
    (H : ∀ {N : Ty} (n : Term N ((T ⊗ S)⋆)), IsDrop n → rank n ≤ r →
      NormListable (T ⊗ S) r n) :
    NormListable (S ⊗ T) (r + 1)
      (prodF x (prodF m y) ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
        Term.unshiftTail S T)) := by
  obtain ⟨M₀, beta, m₀, hb, hm₀, hem⟩ := H m hm hrm
  obtain ⟨D, alpha, g, ha, hg, heg⟩ := exchange_normal_shift (S := T) (T := S) hm₀
  have hstep :
      (prodF x (prodF m y) ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
          Term.unshiftTail S T)) ≡ₜ
        (prodF (Term.id X) (prodF (beta ⨟ alpha) (Term.id Y)) ⨟
          (prodF x (prodF g y) ⨟ Term.unshiftTail S T)) := by
    have hmid : (m ⨟ shift T S) ≡ₜ ((beta ⨟ alpha) ⨟ g) :=
      ((PEq.compL _ hem).trans (PEq.comp_assoc _ _ _)).trans
        ((PEq.compR _ heg).trans (PEq.symm (PEq.comp_assoc _ _ _)))
    calc (prodF x (prodF m y) ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
            Term.unshiftTail S T))
        ≡ₜ ((prodF x (prodF m y) ⨟ prodF (Term.id S) (prodF (shift T S) (Term.id T))) ⨟
            Term.unshiftTail S T) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (x ⨟ Term.id S) (prodF (m ⨟ shift T S) (y ⨟ Term.id T)) ⨟
            Term.unshiftTail S T) :=
          PEq.compL _ ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.refl _) (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (prodF x (prodF ((beta ⨟ alpha) ⨟ g) y) ⨟ Term.unshiftTail S T) :=
          PEq.compL _ (PEq.congr_prodF (PEq.comp_id _)
            (PEq.congr_prodF hmid (PEq.comp_id _)))
      _ ≡ₜ ((prodF (Term.id X) (prodF (beta ⨟ alpha) (Term.id Y)) ⨟
            prodF x (prodF g y)) ⨟ Term.unshiftTail S T) :=
          PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.id_comp _)
              ((PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF (PEq.refl _)
                (PEq.id_comp _))))))
      _ ≡ₜ (prodF (Term.id X) (prodF (beta ⨟ alpha) (Term.id Y)) ⨟
            (prodF x (prodF g y) ⨟ Term.unshiftTail S T)) := PEq.comp_assoc _ _ _
  refine NormListable.congr hstep ?_
  refine NormListable.lift_comp
    (IsLift.prodF (IsLift.id X) (IsLift.prodF (IsLift.comp hb ha) (IsLift.id Y))) ?_
  exact normListable_tail_shape hx hrx hy hry hg

/-- The non-empty summand, after the product normalisation of the middle and last
components. -/
theorem normListable_unshift_prod_inner {X : Ty} {x : Term X S} (hx : IsDrop x)
    (hrx : rank x ≤ r)
    (H : ∀ {N : Ty} (n : Term N ((T ⊗ S)⋆)), IsDrop n → rank n ≤ r →
      NormListable (T ⊗ S) r n) :
    {P : Ty} → {p : Term P (((T ⊗ S)⋆) ⊗ T)} → IsNormalProdLe r p →
      NormListable (S ⊗ T) (r + 1)
        (prodF x p ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
          Term.unshiftTail S T))
  | _, _, .prodF hm hy hrm hry => normListable_unshift_leaf hx hrx hm hrm hy hry H
  | _, _, @IsNormalProdLe.either _ P₁ P₂ _ _ p₁ p₂ h₁ h₂ => by
      have hdist :
          (prodF x (Term.either p₁ p₂) ⨟ (prodF (Term.id S)
              (prodF (shift T S) (Term.id T)) ⨟ Term.unshiftTail S T)) ≡ₜ
            (distR X P₁ P₂ ⨟ Term.either
              (prodF x p₁ ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                Term.unshiftTail S T))
              (prodF x p₂ ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                Term.unshiftTail S T))) := by
        calc (prodF x (Term.either p₁ p₂) ⨟ (prodF (Term.id S)
                (prodF (shift T S) (Term.id T)) ⨟ Term.unshiftTail S T))
            ≡ₜ ((distR X P₁ P₂ ⨟ Term.either (prodF x p₁) (prodF x p₂)) ⨟
                (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                  Term.unshiftTail S T)) :=
              PEq.compL _ (prodF_either_distR _ _ _)
          _ ≡ₜ (distR X P₁ P₂ ⨟ (Term.either (prodF x p₁) (prodF x p₂) ⨟
                (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                  Term.unshiftTail S T))) := PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (either_comp _ _ _)
      refine NormListable.congr hdist ?_
      refine NormListable.lift_comp (IsLift.distR _ _ _) ?_
      exact NormListable.either (normListable_unshift_prod_inner hx hrx H h₁)
        (normListable_unshift_prod_inner hx hrx H h₂)

/-- The non-empty summand, after the product normalisation. -/
theorem normListable_unshift_prod
    (H : ∀ {N : Ty} (n : Term N ((T ⊗ S)⋆)), IsDrop n → rank n ≤ r →
      NormListable (T ⊗ S) r n) :
    {A : Ty} → {u : Term A (S ⊗ (((T ⊗ S)⋆) ⊗ T))} → IsNormalProdLe r u →
      NormListable (S ⊗ T) (r + 1)
        (u ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟ Term.unshiftTail S T))
  | _, _, @IsNormalProdLe.prodF _ X P _ _ x p hx hp hrx hrp => by
      obtain ⟨D, beta, p₀, hb, -, hnorm, hep⟩ := drops_with_prod_codomain p hp
      refine NormListable.congr ?_ (NormListable.lift_comp (IsLift.prodF (IsLift.id X) hb)
        (normListable_unshift_prod_inner hx hrx H (hnorm.mono hrp)))
      calc (prodF x p ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
              Term.unshiftTail S T))
          ≡ₜ (prodF (Term.id X ⨟ x) (beta ⨟ p₀) ⨟
              (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                Term.unshiftTail S T)) :=
            PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) hep)
        _ ≡ₜ ((prodF (Term.id X) beta ⨟ prodF x p₀) ⨟
              (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                Term.unshiftTail S T)) :=
            PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
        _ ≡ₜ (prodF (Term.id X) beta ⨟ (prodF x p₀ ⨟
              (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
                Term.unshiftTail S T))) := PEq.comp_assoc _ _ _
  | _, _, .either h₁ h₂ =>
      NormListable.congr (either_comp _ _ _)
        (NormListable.either (normListable_unshift_prod H h₁)
          (normListable_unshift_prod H h₂))

/-! ### The co-product normalisation -/

/-- A drop with codomain `1 + S × (T × S)* × T`, in normal form, followed by `unshift`, is
normalisable. -/
theorem normListable_sumTree_unshift
    (H : ∀ {N : Ty} (n : Term N ((T ⊗ S)⋆)), IsDrop n → rank n ≤ r →
      NormListable (T ⊗ S) r n) :
    {A : Ty} → {u : Term A (Ty.unit ⊕' (S ⊗ (((T ⊗ S)⋆) ⊗ T)))} → IsNormalSumTree r u →
      NormListable (S ⊗ T) (r + 1) (u ⨟ Term.unshift S T)
  | _, _, @IsNormalSumTree.inl _ _ _ _ g _ _ => by
      refine NormListable.congr ?_ (NormListable.of_leaf
        (IsNormalListLeafLe.const (A := _) (r := r + 1) (nilT (S ⊗ T))))
      calc ((g ⨟ inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T)
          ≡ₜ (g ⨟ (inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟ Term.unshift S T)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (g ⨟ nilT (S ⊗ T)) := PEq.compR _ (Term.inl_unshift S T)
        _ ≡ₜ (toUnit _ ⨟ nilT (S ⊗ T)) := PEq.compL _ (PEq.unit_unique _ _)
  | _, _, @IsNormalSumTree.inr _ _ _ _ g hg hrg => by
      obtain ⟨D, alpha, u, ha, -, hnorm, he⟩ := drops_with_prod_codomain g hg
      refine NormListable.congr ?_ (NormListable.lift_comp ha
        (normListable_unshift_prod H (hnorm.mono hrg)))
      calc ((g ⨟ inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T)
          ≡ₜ (g ⨟ (inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟ Term.unshift S T)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (g ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
              Term.unshiftTail S T)) := PEq.compR _ (Term.inr_unshift_tail S T)
        _ ≡ₜ ((alpha ⨟ u) ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
              Term.unshiftTail S T)) := PEq.compL _ he
        _ ≡ₜ (alpha ⨟ (u ⨟ (prodF (Term.id S) (prodF (shift T S) (Term.id T)) ⨟
              Term.unshiftTail S T))) := PEq.comp_assoc _ _ _
  | _, _, @IsNormalSumTree.sumF _ _ _ _ _ g₁ g₂ hg₁ hg₂ hr₁ hr₂ => by
      have h₁ : NormListable (S ⊗ T) (r + 1)
          ((g₁ ⨟ inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T) :=
        normListable_sumTree_unshift H (IsNormalSumTree.inl hg₁ hr₁)
      have h₂ : NormListable (S ⊗ T) (r + 1)
          ((g₂ ⨟ inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T) :=
        normListable_sumTree_unshift H (IsNormalSumTree.inr hg₂ hr₂)
      refine NormListable.congr ?_ (NormListable.either h₁ h₂)
      calc (sumF g₁ g₂ ⨟ Term.unshift S T)
          ≡ₜ ((sumF g₁ g₂ ⨟ Term.id (Ty.unit ⊕' (S ⊗ (((T ⊗ S)⋆) ⊗ T)))) ⨟
              Term.unshift S T) := PEq.compL _ (PEq.symm (PEq.comp_id _))
        _ ≡ₜ ((sumF g₁ g₂ ⨟ Term.either (inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)))
              (inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)))) ⨟ Term.unshift S T) :=
            PEq.compL _ (PEq.compR _ (PEq.symm (either_inl_inr _ _)))
        _ ≡ₜ (Term.either (g₁ ⨟ inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)))
              (g₂ ⨟ inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T) :=
            PEq.compL _ (Term.sumF_either _ _ _ _)
        _ ≡ₜ Term.either ((g₁ ⨟ inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T)
              ((g₂ ⨟ inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ Term.unshift S T) :=
            either_comp _ _ _
  | _, _, .either h₁ h₂ =>
      NormListable.congr (either_comp _ _ _)
        (NormListable.either (normListable_sumTree_unshift H h₁)
          (normListable_sumTree_unshift H h₂))

/-- **The `unshift` step of the list normalisation lemma** (appendix, the case *Shift* of the
proof of the list normalisation lemma).  A drop followed by `unshift` is normalisable, with
the bound `rank f + 1`, which is the rank of `f ⨟ unshift`.

The hypothesis `H` is the induction hypothesis of the list normalisation lemma, applied to
the middle component of the drop.

(As everywhere, the bound is the paper's `⪯`, read on the components of the leaves.) -/
theorem normListable_comp_unshift {A : Ty} (f : Term A (Ty.unit ⊕' (S ⊗ ((T ⊗ S)⋆ ⊗ T))))
    (hf : IsDrop f)
    (H : ∀ {M : Ty} (m : Term M ((T ⊗ S)⋆)), IsDrop m → rank m ≤ rank f →
      NormListable (T ⊗ S) (rank f) m) :
    NormListable (S ⊗ T) (rank f + 1) (f ⨟ Term.unshift S T) := by
  obtain ⟨D, alpha, N, ha, -, hN, he⟩ := drops_with_sum_codomain_tree f hf
  refine NormListable.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact NormListable.lift_comp ha (normListable_sumTree_unshift H hN)

end Lax149335Proofs

bridge_export Lax149335Proofs
