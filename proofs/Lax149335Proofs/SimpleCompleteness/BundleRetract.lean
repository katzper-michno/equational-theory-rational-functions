import Lax149335Proofs.Appendix.Naturality
import Lax149335Proofs.Preliminaries.StringRepresentation

/-!
# Transferring concatenation-map isomorphisms along retracts

This file proves the transfer principle that the proof of Lemma 6.7 (the bundle lemma,
`Lax149335Proofs.concatMap_bundle_iso_arbitrarily_large'`) uses to pass from binary strings to an
arbitrary parameter.

The concatenation map `F(A) ↣ A*` of a one-parameter list-polynomial functor `F` is natural
in `A` (`Lax149335Proofs.concatMap_natural`).  Naturality alone implies that the property of being a
provable isomorphism *transfers along retracts of the parameter*: if `A` is a retract of `X`,
i.e. there are terms `i : A → X` and `p : X → A` with `i; p ≡ id`, and the concatenation map
of `F` is a provable isomorphism for the parameter `X`, then it is one for the parameter `A`
as well (`Lax149335Proofs.concatMap_provableIso_of_retract`).

Every type is a retract of a type of strings over a finite alphabet (Claim F.1, the finite-alphabet step of Lemma 5.6, in the form
`Lax149335Proofs.exists_injective_encoding`).  Consequently the bundle lemma for *all* types follows
from the bundle lemma for types of the form `Ā*` with `Ā` a finite alphabet, which is how
`Lax149335Proofs.Appendix.Bundles.Window` proves it: the parameter may be assumed to be a list
type, so that, for instance, the "coercion of a block of length one into an element", which
the appendix proof of Lemma 6.7 performs with a head term, becomes the total operation
`concat`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Functoriality of the action of a one-parameter type constructor -/

/-- The functorial action of `F` preserves the identity. -/
theorem TyF.map_id : (F : TyF) → (A : Ty) → F.map (Term.id A) ≡ₜ Term.id (F.app A)
  | .param, _ => PEq.refl _
  | .unit, _ => PEq.refl _
  | .prod F G, A =>
      (PEq.congr_prodF (TyF.map_id F A) (TyF.map_id G A)).trans (PEq.prod_id _ _)
  | .sum F G, A =>
      (PEq.congr_sumF (TyF.map_id F A) (TyF.map_id G A)).trans (PEq.sum_id _ _)
  | .list F, A => (PEq.congr_listF (TyF.map_id F A)).trans (PEq.list_id _)

/-- The functorial action of `F` respects provable equality. -/
theorem TyF.map_congr : (F : TyF) → {A B : Ty} → {f g : Term A B} → f ≡ₜ g →
    F.map f ≡ₜ F.map g
  | .param, _, _, _, _, h => h
  | .unit, _, _, _, _, _ => PEq.refl _
  | .prod F G, _, _, _, _, h =>
      PEq.congr_prodF (TyF.map_congr F h) (TyF.map_congr G h)
  | .sum F G, _, _, _, _, h =>
      PEq.congr_sumF (TyF.map_congr F h) (TyF.map_congr G h)
  | .list F, _, _, _, _, h => PEq.congr_listF (TyF.map_congr F h)

/-- The functorial action of `F` preserves composition. -/
theorem TyF.map_comp : (F : TyF) → {A B C : Ty} → (f : Term A B) → (g : Term B C) →
    (F.map f ⨟ F.map g) ≡ₜ F.map (f ⨟ g)
  | .param, _, _, _, _, _ => PEq.refl _
  | .unit, _, _, _, _, _ => PEq.id_comp _
  | .prod F G, _, _, _, f, g =>
      (PEq.prod_comp _ _ _ _).trans
        (PEq.congr_prodF (TyF.map_comp F f g) (TyF.map_comp G f g))
  | .sum F G, _, _, _, f, g =>
      (PEq.sum_comp _ _ _ _).trans
        (PEq.congr_sumF (TyF.map_comp F f g) (TyF.map_comp G f g))
  | .list F, _, _, _, f, g =>
      (PEq.list_comp _ _).trans (PEq.congr_listF (TyF.map_comp F f g))

end Term

/-! ### Transfer along a retract of the parameter -/

/-- **Transfer of concatenation-map isomorphisms along retracts.**  If `A` is a retract of
`X`, witnessed by `i : A → X` and `p : X → A` with `i; p ≡ id`, and the concatenation map of
the shape `F` is a provable isomorphism for the parameter `X`, then it is a provable
isomorphism for the parameter `A`.

The inverse for the parameter `A` is `i*; (inverse for X); F(p)`; both triangles are checked
using the naturality of the concatenation map. -/
theorem concatMap_provableIso_of_retract (F : Term.TyF) {A X : Ty} (i : Term A X)
    (p : Term X A) (hip : (i ⨟ p) ≡ₜ Term.id A)
    (h : ProvableIso (F.concatMap X)) : ProvableIso (F.concatMap A) := by
  obtain ⟨q, hq₁, hq₂⟩ := h
  refine ⟨(Term.listF i ⨟ q) ⨟ F.map p, ?_, ?_⟩
  · calc (F.concatMap A ⨟ ((Term.listF i ⨟ q) ⨟ F.map p))
        ≡ₜ (((F.concatMap A ⨟ Term.listF i) ⨟ q) ⨟ F.map p) :=
          ((PEq.compR _ (PEq.comp_assoc _ _ _)).trans
            (PEq.symm (PEq.comp_assoc _ _ _))).trans (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((F.map i ⨟ F.concatMap X) ⨟ q) ⨟ F.map p) :=
          PEq.compL _ (PEq.compL _ (PEq.symm (concatMap_natural F i)))
      _ ≡ₜ ((F.map i ⨟ (F.concatMap X ⨟ q)) ⨟ F.map p) :=
          PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((F.map i ⨟ Term.id (F.app X)) ⨟ F.map p) :=
          PEq.compL _ (PEq.compR _ hq₁)
      _ ≡ₜ (F.map i ⨟ F.map p) := PEq.compL _ (PEq.comp_id _)
      _ ≡ₜ F.map (i ⨟ p) := Term.TyF.map_comp F i p
      _ ≡ₜ F.map (Term.id A) := Term.TyF.map_congr F hip
      _ ≡ₜ Term.id (F.app A) := Term.TyF.map_id F A
  · calc (((Term.listF i ⨟ q) ⨟ F.map p) ⨟ F.concatMap A)
        ≡ₜ ((Term.listF i ⨟ q) ⨟ (F.map p ⨟ F.concatMap A)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((Term.listF i ⨟ q) ⨟ (F.concatMap X ⨟ Term.listF p)) :=
          PEq.compR _ (concatMap_natural F p)
      _ ≡ₜ ((Term.listF i ⨟ (q ⨟ F.concatMap X)) ⨟ Term.listF p) :=
          ((PEq.comp_assoc _ _ _).trans
            (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))).trans
              (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.listF i ⨟ Term.id X⋆) ⨟ Term.listF p) := PEq.compL _ (PEq.compR _ hq₂)
      _ ≡ₜ (Term.listF i ⨟ Term.listF p) := PEq.compL _ (PEq.comp_id _)
      _ ≡ₜ Term.listF (i ⨟ p) := PEq.list_comp _ _
      _ ≡ₜ Term.listF (Term.id A) := PEq.congr_listF hip
      _ ≡ₜ Term.id A⋆ := PEq.list_id A

end Lax149335Proofs

bridge_export Lax149335Proofs
