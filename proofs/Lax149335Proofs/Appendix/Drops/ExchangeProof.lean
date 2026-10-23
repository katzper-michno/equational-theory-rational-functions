import Lax149335Proofs.Appendix.Drops.FunctorTools
import Lax149335Proofs.Appendix.Drops.ListNormalisation
import Mathlib.Tactic.Choose

/-!
# The exchange lemma (appendix, *Proof of Exchange Lemma*)

This file contains the proof of Lemma 7.5: every composition drop-lift is provably equal to a
composition lift-drop (`Lax149335Proofs.exchange_aux`; the lemma itself is stated at its place in the
paper, in `Lax149335Proofs.GeneralCompleteness.Statements`).

The proof is the induction on the lift of the appendix:

* the combinator cases (composition, product, co-product and list) are handled by the
  normalisation lemmas for drops with a product, a co-product and a list codomain: the normal
  form is a case tree whose leaves plug drops into the components of the codomain, and the
  induction hypothesis applies to each of those drops;
* the prime lifts `id`, `assocL`, `assocR` and `comm` are themselves drops, and the prime
  lifts `unitL` and `unitR` are handled by their naturality;
* the two distributivities are handled by the normalisation lemmas for drops with a product
  and with a co-product codomain, followed by naturality of distributivity;
* the two remaining prime lifts, `split` and `shift`, are the hard cases of the appendix;
  they are taken as hypotheses of `Lax149335Proofs.exchange_of_shift_split`, and discharged in
  `Lax149335Proofs.Appendix.Drops.ExchangeShiftSplit` and
  `Lax149335Proofs.Appendix.Drops.SplitExchange`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Constants

The leaves of a drop in normal form with list codomain may be constants, and the exchange
lemma has to know that a constant admits a lift-drop factorisation.  Since `1 ; v` is a
prime drop function this is immediate. -/

/-- **Every constant term admits a lift-drop factorisation.**  This is the instance of
Lemma 7.4 that the exchange lemma needs; it holds because `1 ; v` is a prime drop. -/
theorem isLiftDrop_constant (A : Ty) {B : Ty} (v : Value B) :
    IsLiftDrop (Term.toUnit A ⨟ v) :=
  IsLiftDrop.of_isDrop (IsDrop.bangV A v)

/-! ### Exchange for one lift

The induction of the appendix proves, for one prime lift at a time, that every drop followed
by it has a lift-drop factorisation.  This is the property `Lax149335Proofs.AdmitsExchange`. -/

/-- A term `l` *admits exchange* if every drop followed by `l` has a lift-drop
factorisation.  The exchange lemma says that every lift admits exchange. -/
def AdmitsExchange {B C : Ty} (l : Term B C) : Prop :=
  ∀ {A : Ty} {d : Term A B}, IsDrop d → IsLiftDrop (d ⨟ l)

/-- A term that is provably equal to a drop admits exchange: nothing has to be moved. -/
theorem admitsExchange_of_isEqDrop {B C : Ty} {l : Term B C} (hl : IsEqDrop l) :
    AdmitsExchange l := fun hd =>
  IsLiftDrop.of_isEqDrop (IsEqDrop.comp (IsEqDrop.of_isDrop hd) hl)

/-- A drop admits exchange. -/
theorem admitsExchange_of_isDrop {B C : Ty} {l : Term B C} (hl : IsDrop l) :
    AdmitsExchange l := admitsExchange_of_isEqDrop (IsEqDrop.of_isDrop hl)

/-- The prime lift `(id,1)` admits exchange, by its naturality. -/
theorem admitsExchange_unitR (A : Ty) : AdmitsExchange (Term.unitR A) := by
  intro X d hd
  exact IsLiftDrop.congr (PEq.nat_unitR d)
    (IsLiftDrop.comp_left (IsLift.unitR X)
      (IsLiftDrop.of_isDrop (IsDrop.prodF hd (IsDrop.id Ty.unit))))

/-- The prime lift `(1,id)` admits exchange, by its naturality. -/
theorem admitsExchange_unitL (A : Ty) : AdmitsExchange (Term.unitL A) := by
  intro X d hd
  exact IsLiftDrop.congr (PEq.nat_unitL d)
    (IsLiftDrop.comp_left (IsLift.unitL X)
      (IsLiftDrop.of_isDrop (IsDrop.prodF (IsDrop.id Ty.unit) hd)))

/-! ### The two distributivities

A drop into `A × (B + C)` is normalised by the product normalisation lemma; each leaf
`x × y` of the resulting case tree has its second component normalised by the sum
normalisation lemma, and then the naturality of distributivity applies. -/

/-- A normal drop with a product codomain, followed by an arbitrary term out of that product,
is a lift-drop factorisation as soon as each of the leaves `x × y` of the case tree is
one. -/
theorem liftDrop_normalProd_of_leaves {B₁ B₂ E : Ty} {k : Term (B₁ ⊗ B₂) E}
    (H : ∀ {X Y : Ty} {x : Term X B₁} {y : Term Y B₂}, IsDrop x → IsDrop y →
      IsLiftDrop (Term.prodF x y ⨟ k)) :
    ∀ {A : Ty} {g : Term A (B₁ ⊗ B₂)}, IsNormalProd g → IsLiftDrop (g ⨟ k) := by
  intro A g hg
  induction hg with
  | prodF hx hy => exact H hx hy
  | either _ _ ih₁ ih₂ =>
      exact IsLiftDrop.congr (Term.either_comp _ _ _) ((ih₁ H).either (ih₂ H))

/-- A leaf `x × u` whose second component is a normal drop with a co-product codomain,
followed by distributivity on the right. -/
theorem liftDrop_prodF_normalSumTree_distR {r : ℕ} {X A : Ty} {x : Term X A}
    (hx : IsDrop x) : ∀ {Y B C : Ty} {u : Term Y (B ⊕' C)}, IsNormalSumTree r u →
      IsLiftDrop (Term.prodF x u ⨟ Term.distR A B C) := by
  intro Y B C u hu
  induction hu with
  | @inl Y₀ B' C' g hg _ =>
      refine IsLiftDrop.congr ?_ (IsLiftDrop.of_isDrop
        (IsDrop.comp (IsDrop.prodF hx hg) (IsDrop.inl (A ⊗ B') (A ⊗ C'))))
      calc (Term.prodF x (g ⨟ Term.inl B' C') ⨟ Term.distR A B' C')
          ≡ₜ ((Term.prodF x g ⨟ Term.prodF (Term.id A) (Term.inl B' C')) ⨟
              Term.distR A B' C') :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp x g (Term.id A) (Term.inl B' C')).trans
              (PEq.congr_prodF (PEq.comp_id x) (PEq.refl _))))
        _ ≡ₜ (Term.prodF x g ⨟ (Term.prodF (Term.id A) (Term.inl B' C') ⨟
              Term.distR A B' C')) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.prodF x g ⨟ Term.inl (A ⊗ B') (A ⊗ C')) :=
            PEq.compR _ (Term.prodF_inl_distR A B' C')
  | @inr Y₀ B' C' g hg _ =>
      refine IsLiftDrop.congr ?_ (IsLiftDrop.of_isDrop
        (IsDrop.comp (IsDrop.prodF hx hg) (IsDrop.inr (A ⊗ B') (A ⊗ C'))))
      calc (Term.prodF x (g ⨟ Term.inr B' C') ⨟ Term.distR A B' C')
          ≡ₜ ((Term.prodF x g ⨟ Term.prodF (Term.id A) (Term.inr B' C')) ⨟
              Term.distR A B' C') :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp x g (Term.id A) (Term.inr B' C')).trans
              (PEq.congr_prodF (PEq.comp_id x) (PEq.refl _))))
        _ ≡ₜ (Term.prodF x g ⨟ (Term.prodF (Term.id A) (Term.inr B' C') ⨟
              Term.distR A B' C')) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.prodF x g ⨟ Term.inr (A ⊗ B') (A ⊗ C')) :=
            PEq.compR _ (Term.prodF_inr_distR A B' C')
  | @sumF Y₁ Y₂ B' C' u₁ u₂ h₁ h₂ _ _ =>
      exact IsLiftDrop.congr (PEq.nat_distR x u₁ u₂)
        (IsLiftDrop.comp_left (IsLift.distR X Y₁ Y₂)
          (IsLiftDrop.of_isDrop (IsDrop.sumF (IsDrop.prodF hx h₁) (IsDrop.prodF hx h₂))))
  | @either Y₁ Y₂ B' C' f₁ f₂ _ _ ih₁ ih₂ =>
      refine IsLiftDrop.congr ?_
        (IsLiftDrop.comp_left (IsLift.distR X Y₁ Y₂) (ih₁.either ih₂))
      calc (Term.prodF x (Term.either f₁ f₂) ⨟ Term.distR A B' C')
          ≡ₜ ((Term.distR X Y₁ Y₂ ⨟ Term.either (Term.prodF x f₁) (Term.prodF x f₂)) ⨟
              Term.distR A B' C') := PEq.compL _ (Term.prodF_either_distR f₁ f₂ x)
        _ ≡ₜ (Term.distR X Y₁ Y₂ ⨟ (Term.either (Term.prodF x f₁) (Term.prodF x f₂) ⨟
              Term.distR A B' C')) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.distR X Y₁ Y₂ ⨟ Term.either (Term.prodF x f₁ ⨟ Term.distR A B' C')
              (Term.prodF x f₂ ⨟ Term.distR A B' C')) :=
            PEq.compR _ (Term.either_comp _ _ _)

/-- A leaf `u × y` whose first component is a normal drop with a co-product codomain,
followed by distributivity on the left. -/
theorem liftDrop_prodF_normalSumTree_distL {r : ℕ} {Y C : Ty} {y : Term Y C}
    (hy : IsDrop y) : ∀ {X A B : Ty} {u : Term X (A ⊕' B)}, IsNormalSumTree r u →
      IsLiftDrop (Term.prodF u y ⨟ Term.distL A B C) := by
  intro X A B u hu
  induction hu with
  | @inl X₀ A' B' g hg _ =>
      refine IsLiftDrop.congr ?_ (IsLiftDrop.of_isDrop
        (IsDrop.comp (IsDrop.prodF hg hy) (IsDrop.inl (A' ⊗ C) (B' ⊗ C))))
      calc (Term.prodF (g ⨟ Term.inl A' B') y ⨟ Term.distL A' B' C)
          ≡ₜ ((Term.prodF g y ⨟ Term.prodF (Term.inl A' B') (Term.id C)) ⨟
              Term.distL A' B' C) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp g y (Term.inl A' B') (Term.id C)).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.comp_id y))))
        _ ≡ₜ (Term.prodF g y ⨟ (Term.prodF (Term.inl A' B') (Term.id C) ⨟
              Term.distL A' B' C)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.prodF g y ⨟ Term.inl (A' ⊗ C) (B' ⊗ C)) :=
            PEq.compR _ (Term.prodF_inl_distL A' B' C)
  | @inr X₀ A' B' g hg _ =>
      refine IsLiftDrop.congr ?_ (IsLiftDrop.of_isDrop
        (IsDrop.comp (IsDrop.prodF hg hy) (IsDrop.inr (A' ⊗ C) (B' ⊗ C))))
      calc (Term.prodF (g ⨟ Term.inr A' B') y ⨟ Term.distL A' B' C)
          ≡ₜ ((Term.prodF g y ⨟ Term.prodF (Term.inr A' B') (Term.id C)) ⨟
              Term.distL A' B' C) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp g y (Term.inr A' B') (Term.id C)).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.comp_id y))))
        _ ≡ₜ (Term.prodF g y ⨟ (Term.prodF (Term.inr A' B') (Term.id C) ⨟
              Term.distL A' B' C)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.prodF g y ⨟ Term.inr (A' ⊗ C) (B' ⊗ C)) :=
            PEq.compR _ (Term.prodF_inr_distL A' B' C)
  | @sumF X₁ X₂ A' B' u₁ u₂ h₁ h₂ _ _ =>
      exact IsLiftDrop.congr (PEq.nat_distL u₁ u₂ y)
        (IsLiftDrop.comp_left (IsLift.distL X₁ X₂ Y)
          (IsLiftDrop.of_isDrop (IsDrop.sumF (IsDrop.prodF h₁ hy) (IsDrop.prodF h₂ hy))))
  | @either X₁ X₂ A' B' f₁ f₂ _ _ ih₁ ih₂ =>
      refine IsLiftDrop.congr ?_
        (IsLiftDrop.comp_left (IsLift.distL X₁ X₂ Y) (ih₁.either ih₂))
      calc (Term.prodF (Term.either f₁ f₂) y ⨟ Term.distL A' B' C)
          ≡ₜ ((Term.distL X₁ X₂ Y ⨟ Term.either (Term.prodF f₁ y) (Term.prodF f₂ y)) ⨟
              Term.distL A' B' C) := PEq.compL _ (Term.prodF_either_distL f₁ f₂ y)
        _ ≡ₜ (Term.distL X₁ X₂ Y ⨟ (Term.either (Term.prodF f₁ y) (Term.prodF f₂ y) ⨟
              Term.distL A' B' C)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.distL X₁ X₂ Y ⨟ Term.either (Term.prodF f₁ y ⨟ Term.distL A' B' C)
              (Term.prodF f₂ y ⨟ Term.distL A' B' C)) :=
            PEq.compR _ (Term.either_comp _ _ _)

/-- Distributivity on the right admits exchange. -/
theorem admitsExchange_distR (A B C : Ty) : AdmitsExchange (Term.distR A B C) := by
  intro Z d hd
  obtain ⟨D, alpha, g, halpha, -, hnorm, he⟩ := drops_with_prod_codomain d hd
  refine IsLiftDrop.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  refine IsLiftDrop.comp_left halpha
    (liftDrop_normalProd_of_leaves ?_ hnorm.isNormalProd)
  intro X Y x y hx hy
  obtain ⟨Dy, beta, u, hbeta, -, hu, hey⟩ := drops_with_sum_codomain_tree y hy
  refine IsLiftDrop.congr ?_
    (IsLiftDrop.comp_left (IsLift.prodF (IsLift.id X) hbeta)
      (liftDrop_prodF_normalSumTree_distR hx hu))
  calc (Term.prodF x y ⨟ Term.distR A B C)
      ≡ₜ (Term.prodF x (beta ⨟ u) ⨟ Term.distR A B C) :=
        PEq.compL _ (PEq.congr_prodF (PEq.refl _) hey)
    _ ≡ₜ ((Term.prodF (Term.id X) beta ⨟ Term.prodF x u) ⨟ Term.distR A B C) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp (Term.id X) beta x u).trans
          (PEq.congr_prodF (PEq.id_comp x) (PEq.refl _))))
    _ ≡ₜ (Term.prodF (Term.id X) beta ⨟ (Term.prodF x u ⨟ Term.distR A B C)) :=
        PEq.comp_assoc _ _ _

/-- Distributivity on the left admits exchange. -/
theorem admitsExchange_distL (A B C : Ty) : AdmitsExchange (Term.distL A B C) := by
  intro Z d hd
  obtain ⟨D, alpha, g, halpha, -, hnorm, he⟩ := drops_with_prod_codomain d hd
  refine IsLiftDrop.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  refine IsLiftDrop.comp_left halpha
    (liftDrop_normalProd_of_leaves ?_ hnorm.isNormalProd)
  intro X Y x y hx hy
  obtain ⟨Dx, beta, u, hbeta, -, hu, hex⟩ := drops_with_sum_codomain_tree x hx
  refine IsLiftDrop.congr ?_
    (IsLiftDrop.comp_left (IsLift.prodF hbeta (IsLift.id Y))
      (liftDrop_prodF_normalSumTree_distL hy hu))
  calc (Term.prodF x y ⨟ Term.distL A B C)
      ≡ₜ (Term.prodF (beta ⨟ u) y ⨟ Term.distL A B C) :=
        PEq.compL _ (PEq.congr_prodF hex (PEq.refl _))
    _ ≡ₜ ((Term.prodF beta (Term.id Y) ⨟ Term.prodF u y) ⨟ Term.distL A B C) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp beta (Term.id Y) u y).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.id_comp y))))
    _ ≡ₜ (Term.prodF beta (Term.id Y) ⨟ (Term.prodF u y ⨟ Term.distL A B C)) :=
        PEq.comp_assoc _ _ _

/-! ### The combinator cases

Each of them is handled by the corresponding normalisation lemma for drops: the normal form
is a case tree whose leaves plug drops into the components of the codomain, and the induction
hypothesis applies to each of those drops. -/

/-- The case of a product: a normal drop with a product codomain followed by a product of
lifts. -/
theorem liftDrop_normalProd {B₁ B₂ C₁ C₂ : Ty} {f : Term B₁ C₁} {g : Term B₂ C₂}
    (ihf : AdmitsExchange f) (ihg : AdmitsExchange g) :
    ∀ {A : Ty} {g₀ : Term A (B₁ ⊗ B₂)}, IsNormalProd g₀ →
      IsLiftDrop (g₀ ⨟ Term.prodF f g) := by
  intro A g₀ hg₀
  induction hg₀ with
  | @prodF X Y _ _ x y hx hy =>
      exact IsLiftDrop.congr (PEq.prod_comp _ _ _ _) ((ihf hx).prodF (ihg hy))
  | @either A₁ A₂ _ _ f₁ f₂ _ _ ih₁ ih₂ =>
      exact IsLiftDrop.congr (Term.either_comp _ _ _) ((ih₁ ihf ihg).either (ih₂ ihf ihg))

/-- The case of a co-product: a normal drop with a co-product codomain followed by a
co-product of lifts. -/
theorem liftDrop_normalSumTree {r : ℕ} {B₁ B₂ C₁ C₂ : Ty} {f : Term B₁ C₁} {g : Term B₂ C₂}
    (ihf : AdmitsExchange f) (ihg : AdmitsExchange g) :
    ∀ {A : Ty} {g₀ : Term A (B₁ ⊕' B₂)}, IsNormalSumTree r g₀ →
      IsLiftDrop (g₀ ⨟ Term.sumF f g) := by
  intro A g₀ hg₀
  induction hg₀ with
  | @inl A₀ _ _ g₁ hg₁ _ =>
      refine IsLiftDrop.congr ?_ ((ihf hg₁).comp_right (IsDrop.inl C₁ C₂))
      exact (PEq.comp_assoc _ _ _).trans
        ((PEq.compR _ (PEq.nat_inl _ _)).trans (PEq.symm (PEq.comp_assoc _ _ _)))
  | @inr A₀ _ _ g₂ hg₂ _ =>
      refine IsLiftDrop.congr ?_ ((ihg hg₂).comp_right (IsDrop.inr C₁ C₂))
      exact (PEq.comp_assoc _ _ _).trans
        ((PEq.compR _ (PEq.nat_inr _ _)).trans (PEq.symm (PEq.comp_assoc _ _ _)))
  | @sumF A₁ A₂ _ _ g₁ g₂ hg₁ hg₂ _ _ =>
      exact IsLiftDrop.congr (PEq.sum_comp _ _ _ _) ((ihf hg₁).sumF (ihg hg₂))
  | @either A₁ A₂ _ _ f₁ f₂ _ _ ih₁ ih₂ =>
      exact IsLiftDrop.congr (Term.either_comp _ _ _) ((ih₁ ihf ihg).either (ih₂ ihf ihg))

/-- The case of a list: a leaf of a normal drop with a list codomain followed by the
homomorphic image of a lift.  A constant leaf is handled by `Lax149335Proofs.isLiftDrop_constant`. -/
theorem liftDrop_normalListLeaf {B C : Ty} {f : Term B C} (ihf : AdmitsExchange f)
    {A : Ty} {u : Term A B⋆} (hu : IsNormalListLeaf B u) :
    IsLiftDrop (u ⨟ Term.listF f) := by
  induction hu with
  | @const A₀ v =>
      exact IsLiftDrop.congr (PEq.comp_assoc _ _ _)
        (isLiftDrop_constant A₀ (v ⨟ Term.listF f))
  | @sing A₀ g hg =>
      refine IsLiftDrop.congr ?_ ((ihf hg).comp_right (IsDrop.pureT C))
      calc ((g ⨟ Term.pureT B) ⨟ Term.listF f)
          ≡ₜ (g ⨟ (Term.pureT B ⨟ Term.listF f)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (g ⨟ (f ⨟ Term.pureT C)) := PEq.compR _ (PEq.symm (Term.pureT_natural f))
        _ ≡ₜ ((g ⨟ f) ⨟ Term.pureT C) := PEq.symm (PEq.comp_assoc _ _ _)
  | @map A₀ g hg =>
      exact IsLiftDrop.congr (PEq.list_comp _ _) ((ihf hg).listF)

/-! ### The combinators preserve exchange

The four cases of the induction for the combinators, isolated as closure properties of
`Lax149335Proofs.AdmitsExchange`. -/

namespace AdmitsExchange

/-- A composition of two terms that admit exchange admits exchange. -/
theorem comp {B C D : Ty} {f : Term B C} {g : Term C D} (hf : AdmitsExchange f)
    (hg : AdmitsExchange g) : AdmitsExchange (f ⨟ g) := by
  intro A d hd
  obtain ⟨D₁, l₁, d₁, hl₁, hd₁, he₁⟩ := hf hd
  refine IsLiftDrop.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine IsLiftDrop.congr (PEq.compL _ he₁) ?_
  exact IsLiftDrop.congr (PEq.comp_assoc _ _ _) (IsLiftDrop.comp_left hl₁ (hg hd₁))

/-- A product of two terms that admit exchange admits exchange. -/
theorem prodF {B₁ B₂ C₁ C₂ : Ty} {f : Term B₁ C₁} {g : Term B₂ C₂} (hf : AdmitsExchange f)
    (hg : AdmitsExchange g) : AdmitsExchange (Term.prodF f g) := by
  intro A d hd
  obtain ⟨D, alpha, g₀, halpha, -, hnorm, he⟩ := drops_with_prod_codomain d hd
  refine IsLiftDrop.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact IsLiftDrop.comp_left halpha (liftDrop_normalProd hf hg hnorm.isNormalProd)

/-- A co-product of two terms that admit exchange admits exchange. -/
theorem sumF {B₁ B₂ C₁ C₂ : Ty} {f : Term B₁ C₁} {g : Term B₂ C₂} (hf : AdmitsExchange f)
    (hg : AdmitsExchange g) : AdmitsExchange (Term.sumF f g) := by
  intro A d hd
  obtain ⟨D, alpha, g₀, halpha, -, hnorm, he⟩ := drops_with_sum_codomain_tree d hd
  refine IsLiftDrop.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact IsLiftDrop.comp_left halpha (liftDrop_normalSumTree hf hg hnorm)

/-- The homomorphic image of a term that admits exchange admits exchange. -/
theorem listF {B C : Ty} {f : Term B C} (hf : AdmitsExchange f) :
    AdmitsExchange (Term.listF f) := by
  intro A d hd
  classical
  obtain ⟨F, As, alpha, fs, halpha, hleaf, he⟩ := drops_with_list_codomain d hd
  obtain ⟨fs', hfseq, hleaf'⟩ : ∃ fs' : (i : ℕ) → Term (As i) B⋆,
      (∀ i, F.usesParam i → fs i ≡ₜ fs' i) ∧ ∀ i, IsNormalListLeaf B (fs' i) := by
    refine ⟨fun i => if F.usesParam i then fs i else (Term.toUnit (As i) ⨟ Term.nilT B),
      fun i hi => ?_, fun i => ?_⟩
    · simp only [if_pos hi]
      exact PEq.refl _
    · by_cases h : F.usesParam i
      · simp only [if_pos h]
        exact (hleaf i h).isNormalListLeaf
      · simp only [if_neg h]
        exact IsNormalListLeaf.const (A := As i) (Term.nilT B)
  have hshape : normalListShape B F As fs ≡ₜ normalListShape B F As fs' :=
    PEq.compL _ (F.mapN_congr hfseq)
  have hfac : ∀ i, IsLiftDrop (fs' i ⨟ Term.listF f) :=
    fun i => liftDrop_normalListLeaf hf (hleaf' i)
  choose Ds ls ds hls hds hes using hfac
  refine IsLiftDrop.congr
    ((PEq.compL _ (he.trans (PEq.compR _ hshape))).trans (PEq.comp_assoc _ _ _)) ?_
  refine IsLiftDrop.comp_left halpha ?_
  refine IsLiftDrop.congr ?_
    (IsLiftDrop.comp_left (TyFn.isLift_mapN F hls)
      (IsLiftDrop.of_isEqDrop
        (IsEqDrop.comp (IsEqDrop.of_isDrop (TyFn.isDrop_mapN F hds))
          (TyFn.isEqDrop_listConcatMap F C))))
  calc ((F.mapN fs' ⨟ F.listConcatMap B) ⨟ Term.listF f)
      ≡ₜ (F.mapN fs' ⨟ (F.listConcatMap B ⨟ Term.listF f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (F.mapN fs' ⨟ (F.mapN (fun _ => Term.listF f) ⨟ F.listConcatMap C)) :=
        PEq.compR _ (TyFn.listConcatMap_natural F f)
    _ ≡ₜ ((F.mapN fs' ⨟ F.mapN (fun _ => Term.listF f)) ⨟ F.listConcatMap C) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (F.mapN (fun i => fs' i ⨟ Term.listF f) ⨟ F.listConcatMap C) :=
        PEq.compL _ (TyFn.mapN_comp F _ _)
    _ ≡ₜ (F.mapN (fun i => ls i ⨟ ds i) ⨟ F.listConcatMap C) :=
        PEq.compL _ (TyFn.mapN_congr F (fun i _ => hes i))
    _ ≡ₜ ((F.mapN ls ⨟ F.mapN ds) ⨟ F.listConcatMap C) :=
        PEq.compL _ (PEq.symm (TyFn.mapN_comp F _ _))
    _ ≡ₜ (F.mapN ls ⨟ (F.mapN ds ⨟ F.listConcatMap C)) := PEq.comp_assoc _ _ _

end AdmitsExchange

/-! ### The induction

Everything except the two hard prime lifts `shift` and `split`. -/

/-- **The induction underlying the exchange lemma (Lemma 7.5)**, assuming the two hard cases
of the appendix: if the prime lifts `shift` and `split` admit exchange, then every lift
admits exchange, i.e. every drop followed by a lift has a lift-drop factorisation.

The two assumptions are exactly the cases *Shift* and *Split* of the appendix proof; all the
other cases — the four combinators and the ten remaining prime lifts of Table 1 — are
proved here. -/
theorem exchange_aux
    (Hshift : ∀ S T : Ty, AdmitsExchange (Term.shift S T))
    (Hsplit : ∀ S T : Ty, AdmitsExchange (Term.split S T)) :
    ∀ {B C : Ty} {l : Term B C}, IsLift l → AdmitsExchange l := by
  intro B C l hl
  induction hl with
  | comp _ _ ihf ihg => exact ihf.comp ihg
  | prodF _ _ ihf ihg => exact ihf.prodF ihg
  | sumF _ _ ihf ihg => exact ihf.sumF ihg
  | listF _ ihf => exact ihf.listF
  | id A => exact admitsExchange_of_isDrop (IsDrop.id A)
  | unitR A => exact admitsExchange_unitR A
  | unitL A => exact admitsExchange_unitL A
  | assocL A B C => exact admitsExchange_of_isDrop (IsDrop.assocL A B C)
  | assocR A B C => exact admitsExchange_of_isDrop (IsDrop.assocR A B C)
  | sumAssocL A B C => exact admitsExchange_of_isDrop (isDrop_sumAssocL A B C)
  | sumAssocR A B C => exact admitsExchange_of_isDrop (isDrop_sumAssocR A B C)
  | comm A B => exact admitsExchange_of_isDrop (isDrop_comm A B)
  | distL A B C => exact admitsExchange_distL A B C
  | distR A B C => exact admitsExchange_distR A B C
  | split A B => exact Hsplit A B
  | shift A B => exact Hshift A B

/-- **Lemma 7.5 (Exchange)**, assuming its two hard cases: if the prime lifts `shift` and
`split` admit exchange, then every composition of the form drop-lift is provably equivalent
to a composition of the form lift-drop. -/
theorem exchange_of_shift_split
    (Hshift : ∀ S T : Ty, AdmitsExchange (Term.shift S T))
    (Hsplit : ∀ S T : Ty, AdmitsExchange (Term.split S T))
    {A B C : Ty} (d : Term A B) (l : Term B C) (hd : IsDrop d) (hl : IsLift l) :
    ∃ (D : Ty) (l' : Term A D) (d' : Term D C),
      IsLift l' ∧ IsDrop d' ∧ (d ⨟ l) ≡ₜ (l' ⨟ d') :=
  exchange_aux Hshift Hsplit hl hd

end Lax149335Proofs

bridge_export Lax149335Proofs
