import Lax149335Proofs.Appendix.Drops.InjectiveTypes
import Lax149335Proofs.Appendix.Drops.ListNormalForm
import Lax149335Proofs.Appendix.Drops.UnshiftNormalForm
import Lax149335Proofs.Appendix.ValueNormalisation

/-!
# The shapes of the shift exchange lemma (appendix, *Shift exchange lemma*)

This file records the three notions of shape that the conclusion of the shift exchange lemma
uses — `Lax149335Proofs.IsShiftInnerLeaf` (the restricted leaves of the inner normal form),
`Lax149335Proofs.IsShiftInnerForm` (the inner normal form itself) and
`Lax149335Proofs.IsShiftExchangeShape` (the co-pairing of drops that the lemma produces) — together
with their basic properties and the predicate `Lax149335Proofs.ShiftExch` that the induction of
`Lax149335Proofs.Appendix.Drops.ShiftExchange` maintains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- The codomain of `shift`: `1 + S × (T × S)* × T`. -/
abbrev shiftCod (S T : Ty) : Ty := Ty.unit ⊕' (S ⊗ ((T ⊗ S)⋆ ⊗ T))

/-! ### The shapes of the conclusion -/

/-- The three shapes allowed for the leaves of the inner normal form of the shift exchange
lemma: a constant `(1; v)`, a singleton `[(fst × id); k]` or a homomorphic image
`((fst × id); k)*`, where `k` is a drop with codomain `T × S` of rank at most `r`.

The projection `fst` erases the factor of the domain that carries no letter; in the appendix
that factor is always the unit type. -/
inductive IsShiftInnerLeaf (S T : Ty) (r : ℕ) : {A : Ty} → Term A ((T ⊗ S)⋆) → Prop
  /-- A constant value. -/
  | const {A : Ty} (v : Value ((T ⊗ S)⋆)) : IsShiftInnerLeaf S T r (toUnit A ⨟ v)
  /-- A singleton list `[(fst × id); k]`. -/
  | sing {P W Q : Ty} {k : Term (P ⊗ Q) (T ⊗ S)} : IsDrop k → rank k ≤ r →
      IsShiftInnerLeaf S T r
        ((prodF (Term.fst P W) (Term.id Q) ⨟ k) ⨟ pureT (T ⊗ S))
  /-- A homomorphic image `((fst × id); k)*`. -/
  | map {P W Q : Ty} {k : Term (P ⊗ Q) (T ⊗ S)} : IsDrop k → rank k ≤ r →
      IsShiftInnerLeaf S T r (listF (prodF (Term.fst P W) (Term.id Q) ⨟ k))

/-- The inner normal form of the shift exchange lemma: a drop in normal form
`H(h⃗); genconc` with codomain `(T × S)*` whose leaves are the restricted ones of
`Lax149335Proofs.IsShiftInnerLeaf`.  The five clauses are those of `Lax149335Proofs.IsListNormalForm`. -/
inductive IsShiftInnerForm (S T : Ty) (r : ℕ) : {A : Ty} → Term A ((T ⊗ S)⋆) → Prop
  /-- A single leaf, the case `H = Xᵢ`. -/
  | leaf {A : Ty} {h : Term A ((T ⊗ S)⋆)} : IsShiftInnerLeaf S T r h →
      IsShiftInnerForm S T r h
  /-- The empty list, the case `H = 1`. -/
  | nil : IsShiftInnerForm S T r (nilT (T ⊗ S))
  /-- A concatenation, the case `H = H₁ × H₂`. -/
  | fdot {A₁ A₂ : Ty} {h₁ : Term A₁ ((T ⊗ S)⋆)} {h₂ : Term A₂ ((T ⊗ S)⋆)} :
      IsShiftInnerForm S T r h₁ → IsShiftInnerForm S T r h₂ →
      IsShiftInnerForm S T r (h₁ ⊙ h₂)
  /-- A co-pairing, the case `H = H₁ + H₂`. -/
  | either {A₁ A₂ : Ty} {h₁ : Term A₁ ((T ⊗ S)⋆)} {h₂ : Term A₂ ((T ⊗ S)⋆)} :
      IsShiftInnerForm S T r h₁ → IsShiftInnerForm S T r h₂ →
      IsShiftInnerForm S T r (Term.either h₁ h₂)
  /-- A homomorphic image, the case `H = H₁*`. -/
  | homT {A : Ty} {h : Term A ((T ⊗ S)⋆)} : IsShiftInnerForm S T r h →
      IsShiftInnerForm S T r (Term.homT h)

/-- The shape of the drop that the shift exchange lemma produces after the lift: a co-pairing
whose components are the constant `(1;1); Left` and the terms
`((snd; x) × (m × (fst; y))); Right` with `m` an inner normal form. -/
inductive IsShiftExchangeShape (S T : Ty) (r : ℕ) : {A : Ty} → Term A (shiftCod S T) → Prop
  /-- The empty component `(1;1); Left`. -/
  | empty (A : Ty) :
      IsShiftExchangeShape S T r (toUnit A ⨟ inl Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)))
  /-- A non-empty component: a letter of `S`, an inner normal form and a letter of `T`. -/
  | inner {W X M Y V : Ty} {x : Term X S} {y : Term Y T} {m : Term M ((T ⊗ S)⋆)} :
      IsDrop x → rank x ≤ r → IsDrop y → rank y ≤ r → IsShiftInnerForm S T r m →
      IsShiftExchangeShape S T r
        (prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
          inr Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)))
  /-- One more component of the co-pairing. -/
  | either {A₁ A₂ : Ty} {g₁ : Term A₁ (shiftCod S T)} {g₂ : Term A₂ (shiftCod S T)} :
      IsShiftExchangeShape S T r g₁ → IsShiftExchangeShape S T r g₂ →
      IsShiftExchangeShape S T r (Term.either g₁ g₂)

/-! ### Basic properties of the shapes -/

namespace IsShiftInnerLeaf

variable {S T : Ty} {r r' : ℕ}

/-- The leaves are monotone in the rank bound. -/
theorem mono (h : r ≤ r') : {A : Ty} → {u : Term A ((T ⊗ S)⋆)} →
    IsShiftInnerLeaf S T r u → IsShiftInnerLeaf S T r' u
  | _, _, .const v => .const v
  | _, _, .sing hk hr => .sing hk (hr.trans h)
  | _, _, .map hk hr => .map hk (hr.trans h)

/-- A restricted leaf is a leaf of a normal form, with the rank bound raised by one: the
composition with the erasing projection is one composition longer. -/
theorem isNormalListLeafLe : {A : Ty} → {u : Term A ((T ⊗ S)⋆)} →
    IsShiftInnerLeaf S T r u → IsNormalListLeafLe (T ⊗ S) (r + 1) u
  | _, _, .const v => .const v
  | _, _, @sing _ _ _ P W Q k hk hr =>
      .sing (IsDrop.comp (IsDrop.prodF (IsDrop.fst _ _) (IsDrop.id _)) hk)
        (by
          have h := rank_comp_le (prodF (Term.fst P W) (Term.id Q)) k
          have h0 : rank (prodF (Term.fst P W) (Term.id Q)) = 0 := rfl
          omega)
  | _, _, @map _ _ _ P W Q k hk hr =>
      .map (IsDrop.comp (IsDrop.prodF (IsDrop.fst _ _) (IsDrop.id _)) hk)
        (by
          have h := rank_comp_le (prodF (Term.fst P W) (Term.id Q)) k
          have h0 : rank (prodF (Term.fst P W) (Term.id Q)) = 0 := rfl
          omega)

end IsShiftInnerLeaf

namespace IsShiftInnerForm

variable {S T : Ty} {r r' : ℕ}

/-- Inner normal forms are monotone in the rank bound. -/
theorem mono (h : r ≤ r') : {A : Ty} → {u : Term A ((T ⊗ S)⋆)} →
    IsShiftInnerForm S T r u → IsShiftInnerForm S T r' u
  | _, _, .leaf hl => .leaf (hl.mono h)
  | _, _, .nil => .nil
  | _, _, .fdot h₁ h₂ => .fdot (h₁.mono h) (h₂.mono h)
  | _, _, .either h₁ h₂ => .either (h₁.mono h) (h₂.mono h)
  | _, _, .homT h₁ => .homT (h₁.mono h)

/-- An inner normal form is a normal form, with the rank bound raised by one. -/
theorem isListNormalForm : {A : Ty} → {u : Term A ((T ⊗ S)⋆)} →
    IsShiftInnerForm S T r u → IsListNormalForm (T ⊗ S) (r + 1) u
  | _, _, .leaf hl => .leaf hl.isNormalListLeafLe
  | _, _, .nil => .nil
  | _, _, .fdot h₁ h₂ => .fdot h₁.isListNormalForm h₂.isListNormalForm
  | _, _, .either h₁ h₂ => .either h₁.isListNormalForm h₂.isListNormalForm
  | _, _, .homT h₁ => .homT h₁.isListNormalForm

end IsShiftInnerForm

namespace IsShiftExchangeShape

variable {S T : Ty} {r r' : ℕ}

/-- The shapes are monotone in the rank bound. -/
theorem mono (h : r ≤ r') : {A : Ty} → {g : Term A (shiftCod S T)} →
    IsShiftExchangeShape S T r g → IsShiftExchangeShape S T r' g
  | _, _, .empty A => .empty A
  | _, _, .inner hx hrx hy hry hm => .inner hx (hrx.trans h) hy (hry.trans h) (hm.mono h)
  | _, _, .either h₁ h₂ => .either (h₁.mono h) (h₂.mono h)

/-- Every component of the co-pairing is a drop, hence so is the co-pairing. -/
theorem isEqDrop : {A : Ty} → {g : Term A (shiftCod S T)} →
    IsShiftExchangeShape S T r g → IsEqDrop g
  | _, _, .empty A => IsEqDrop.of_isDrop (IsDrop.bangV A (Term.inl Ty.unit _))
  | _, _, .inner hx _ hy _ hm =>
      IsEqDrop.comp
        (IsEqDrop.prodF (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.snd _ _) hx))
          (IsEqDrop.prodF hm.isListNormalForm.isEqDrop
            (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.fst _ _) hy))))
        (IsEqDrop.of_isDrop (IsDrop.inr _ _))
  | _, _, .either h₁ h₂ => IsEqDrop.either h₁.isEqDrop h₂.isEqDrop

end IsShiftExchangeShape

/-! ### The predicate maintained by the induction

The conclusion of the lemma, as a predicate on the normal form, so that the induction on the
structure of the list-polynomial functor can be written as a sequence of closure lemmas. -/

/-- `ShiftExch S T r f` says that `f ⨟ shift` is provably equal to a lift followed by a drop
of the shape of `Lax149335Proofs.IsShiftExchangeShape`. -/
def ShiftExch (S T : Ty) (r : ℕ) {A : Ty} (f : Term A ((S ⊗ T)⋆)) : Prop :=
  ∃ (D : Ty) (alpha : Term A D) (g : Term D (shiftCod S T)),
    IsLift alpha ∧ IsShiftExchangeShape S T r g ∧ (f ⨟ Term.shift S T) ≡ₜ (alpha ⨟ g)

namespace ShiftExch

variable {S T : Ty} {r r' : ℕ}

theorem congr {A : Ty} {f f' : Term A ((S ⊗ T)⋆)} (h : f ≡ₜ f') (hf : ShiftExch S T r f') :
    ShiftExch S T r f :=
  let ⟨D, alpha, g, ha, hg, he⟩ := hf
  ⟨D, alpha, g, ha, hg, (PEq.compL _ h).trans he⟩

/-- One more case of the co-pairing. -/
theorem either {A₁ A₂ : Ty} {f₁ : Term A₁ ((S ⊗ T)⋆)} {f₂ : Term A₂ ((S ⊗ T)⋆)}
    (h₁ : ShiftExch S T r f₁) (h₂ : ShiftExch S T r f₂) :
    ShiftExch S T r (Term.either f₁ f₂) := by
  obtain ⟨D₁, a₁, g₁, ha₁, hg₁, he₁⟩ := h₁
  obtain ⟨D₂, a₂, g₂, ha₂, hg₂, he₂⟩ := h₂
  refine ⟨D₁ ⊕' D₂, sumF a₁ a₂, Term.either g₁ g₂, IsLift.sumF ha₁ ha₂, hg₁.either hg₂, ?_⟩
  calc (Term.either f₁ f₂ ⨟ Term.shift S T)
      ≡ₜ Term.either (f₁ ⨟ Term.shift S T) (f₂ ⨟ Term.shift S T) := Term.either_comp _ _ _
    _ ≡ₜ Term.either (a₁ ⨟ g₁) (a₂ ⨟ g₂) := Term.either_congr he₁ he₂
    _ ≡ₜ (sumF a₁ a₂ ⨟ Term.either g₁ g₂) := PEq.symm (Term.sumF_either _ _ _ _)

end ShiftExch

end Lax149335Proofs

bridge_export Lax149335Proofs
