import Lax149335Proofs.Appendix.Drops.ListNormalisation

/-!
# Drop simplification (appendix, *Proof of joint simplification*)

This file proves the appendix lemma **Drop simplification**: if `B` is a finite alphabet and
`f : A ⇒ B*` is a drop, then there is a list-polynomial functor `F`, a lift `A ⊸ F(1,…,1)`
and values `v₁,…,vₙ` of type `B*` with

`f ≡ δ; F(v₁,…,vₙ); genconc`.

In other words, after a lift, a drop into a finite alphabet becomes a simple rational term in
which all the values are produced in the leaves, and all the leaves are the unit type.

The proof follows the appendix.  The drop is first normalised with the list normalisation
lemma (`Lax149335Proofs.drop_normListable`), which produces a lift followed by a normal shape whose
leaves are constants `1; v`, singletons `[g]` and homomorphic images `g⋆` with `g : X ⇒ B`.
Each leaf is then simplified:

* a constant `1; v` on a domain `X` is pushed onto the unit type with the lift
  `unitL : X ⊸ 1 × X`, which produces the value on the `1` and the empty list on `X`
  (`Lax149335Proofs.valueShaped_const`);
* a leaf whose component is a drop `g : X ⇒ B` into the finite alphabet is decomposed with
  the sum normalisation lemma into a case tree whose leaves produce a single, fixed letter
  (`Lax149335Proofs.valueShaped_sumUnits`).

The predicate maintained by the induction is `Lax149335Proofs.ValueShaped`, which is exactly the
conclusion of the lemma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Shapes with values in the leaves -/

/-- Provably equal to a lift followed by a normal shape all of whose leaves are values on the
unit type.  This is the conclusion of the drop simplification lemma. -/
def ValueShaped (B : Ty) {A : Ty} (f : Term A B⋆) : Prop :=
  ∃ (F : TyFn) (delta : Term A (F.app (fun _ => Ty.unit))) (vs : (i : ℕ) → Value B⋆),
    IsLift delta ∧ f ≡ₜ (delta ⨟ normalListShape B F (fun _ => Ty.unit) vs)

namespace ValueShaped

variable {B : Ty}

theorem congr {A : Ty} {f g : Term A B⋆} (h : f ≡ₜ g) (hg : ValueShaped B g) :
    ValueShaped B f := by
  obtain ⟨F, delta, vs, hd, he⟩ := hg
  exact ⟨F, delta, vs, hd, h.trans he⟩

/-- Pre-composing with a lift. -/
theorem lift_comp {A A' : Ty} {beta : Term A A'} (hb : IsLift beta) {f : Term A' B⋆}
    (hf : ValueShaped B f) : ValueShaped B (beta ⨟ f) := by
  obtain ⟨F, delta, vs, hd, he⟩ := hf
  exact ⟨F, beta ⨟ delta, vs, IsLift.comp hb hd,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

/-- A value on the unit type is a one-leaf shape. -/
theorem value (v : Value B⋆) : ValueShaped B v := by
  refine ⟨.param 0, Term.id Ty.unit, fun _ => v, IsLift.id _, ?_⟩
  exact (PEq.symm (PEq.comp_id v)).trans (PEq.symm (PEq.id_comp _))

end ValueShaped

/-! ### Renumbering the leaves

Two shapes are combined by renumbering the parameters of the first one to the even indices
and those of the second one to the odd indices.  Since all the leaves have the unit type
here, the leaf environment is just a family of values. -/

/-- Merging two families of values: the first one on the even indices, the second one on the
odd indices. -/
def mergeVal {B : Ty} (vs₁ vs₂ : ℕ → Value B⋆) : ℕ → Value B⋆ :=
  fun i => if i % 2 = 0 then vs₁ (i / 2) else vs₂ (i / 2)

theorem mergeVal_even {B : Ty} (vs₁ vs₂ : ℕ → Value B⋆) (i : ℕ) :
    mergeVal vs₁ vs₂ (2 * i) = vs₁ i := by
  simp [mergeVal, Nat.mul_mod_right]

theorem mergeVal_odd {B : Ty} (vs₁ vs₂ : ℕ → Value B⋆) (i : ℕ) :
    mergeVal vs₁ vs₂ (2 * i + 1) = vs₂ i := by
  have h₁ : (2 * i + 1) % 2 = 1 := by omega
  have h₂ : (2 * i + 1) / 2 = i := by omega
  simp [mergeVal, h₁, h₂]

/-- Renumbering the parameters of a shape whose leaves are values, up to a lift. -/
theorem valueShape_reindex (B : Ty) : (F : TyFn) → (h : ℕ → ℕ) → (vs vs' : ℕ → Value B⋆) →
    (∀ i, vs' (h i) = vs i) →
    ∃ gamma : Term (F.app (fun _ => Ty.unit)) ((F.reindex h).app (fun _ => Ty.unit)),
      IsLift gamma ∧
        normalListShape B F (fun _ => Ty.unit) vs ≡ₜ
          (gamma ⨟ normalListShape B (F.reindex h) (fun _ => Ty.unit) vs')
  | .param i, h, vs, vs', hv => by
      refine ⟨Term.id Ty.unit, IsLift.id _, ?_⟩
      calc normalListShape B (.param i) (fun _ => Ty.unit) vs ≡ₜ vs i :=
            Term.normalListShape_param _ _ _ _
        _ ≡ₜ vs' (h i) := by rw [hv i]; exact PEq.refl _
        _ ≡ₜ normalListShape B (.param (h i)) (fun _ => Ty.unit) vs' :=
            PEq.symm (Term.normalListShape_param _ _ _ _)
        _ ≡ₜ (Term.id Ty.unit ⨟ normalListShape B (.param (h i)) (fun _ => Ty.unit) vs') :=
            PEq.symm (PEq.id_comp _)
  | .unit, h, vs, vs', _ => by
      refine ⟨Term.id Ty.unit, IsLift.id _, ?_⟩
      calc normalListShape B .unit (fun _ => Ty.unit) vs ≡ₜ nilT B :=
            Term.normalListShape_unit _ _ _
        _ ≡ₜ normalListShape B .unit (fun _ => Ty.unit) vs' :=
            PEq.symm (Term.normalListShape_unit _ _ _)
        _ ≡ₜ (Term.id Ty.unit ⨟ normalListShape B .unit (fun _ => Ty.unit) vs') :=
            PEq.symm (PEq.id_comp _)
  | .prod F G, h, vs, vs', hv => by
      obtain ⟨g₁, hg₁, he₁⟩ := valueShape_reindex B F h vs vs' hv
      obtain ⟨g₂, hg₂, he₂⟩ := valueShape_reindex B G h vs vs' hv
      refine ⟨prodF g₁ g₂, IsLift.prodF hg₁ hg₂, ?_⟩
      calc normalListShape B (.prod F G) (fun _ => Ty.unit) vs
          ≡ₜ ((normalListShape B F (fun _ => Ty.unit) vs) ⊙
              (normalListShape B G (fun _ => Ty.unit) vs)) :=
            Term.normalListShape_prod _ _ _ _ _
        _ ≡ₜ ((g₁ ⨟ normalListShape B (F.reindex h) (fun _ => Ty.unit) vs') ⊙
              (g₂ ⨟ normalListShape B (G.reindex h) (fun _ => Ty.unit) vs')) :=
            PEq.compL _ (PEq.congr_prodF he₁ he₂)
        _ ≡ₜ (prodF g₁ g₂ ⨟
              ((normalListShape B (F.reindex h) (fun _ => Ty.unit) vs') ⊙
               (normalListShape B (G.reindex h) (fun _ => Ty.unit) vs'))) := by
            calc _ ≡ₜ ((prodF g₁ g₂ ⨟ prodF _ _) ⨟ binconcat B) :=
                  PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
              _ ≡ₜ _ := PEq.comp_assoc _ _ _
        _ ≡ₜ (prodF g₁ g₂ ⨟
              normalListShape B ((TyFn.prod F G).reindex h) (fun _ => Ty.unit) vs') :=
            PEq.compR _ (PEq.symm (Term.normalListShape_prod _ _ _ _ _))
  | .sum F G, h, vs, vs', hv => by
      obtain ⟨g₁, hg₁, he₁⟩ := valueShape_reindex B F h vs vs' hv
      obtain ⟨g₂, hg₂, he₂⟩ := valueShape_reindex B G h vs vs' hv
      refine ⟨sumF g₁ g₂, IsLift.sumF hg₁ hg₂, ?_⟩
      calc normalListShape B (.sum F G) (fun _ => Ty.unit) vs
          ≡ₜ Term.either (normalListShape B F (fun _ => Ty.unit) vs)
              (normalListShape B G (fun _ => Ty.unit) vs) :=
            Term.normalListShape_sum _ _ _ _ _
        _ ≡ₜ Term.either (g₁ ⨟ normalListShape B (F.reindex h) (fun _ => Ty.unit) vs')
              (g₂ ⨟ normalListShape B (G.reindex h) (fun _ => Ty.unit) vs') :=
            Term.either_congr he₁ he₂
        _ ≡ₜ (sumF g₁ g₂ ⨟ Term.either
              (normalListShape B (F.reindex h) (fun _ => Ty.unit) vs')
              (normalListShape B (G.reindex h) (fun _ => Ty.unit) vs')) :=
            PEq.symm (Term.sumF_either _ _ _ _)
        _ ≡ₜ (sumF g₁ g₂ ⨟
              normalListShape B ((TyFn.sum F G).reindex h) (fun _ => Ty.unit) vs') :=
            PEq.compR _ (PEq.symm (Term.normalListShape_sum _ _ _ _ _))
  | .list F, h, vs, vs', hv => by
      obtain ⟨g₁, hg₁, he₁⟩ := valueShape_reindex B F h vs vs' hv
      refine ⟨listF g₁, IsLift.listF hg₁, ?_⟩
      calc normalListShape B (.list F) (fun _ => Ty.unit) vs
          ≡ₜ Term.homT (normalListShape B F (fun _ => Ty.unit) vs) :=
            Term.normalListShape_list _ _ _ _
        _ ≡ₜ Term.homT (g₁ ⨟ normalListShape B (F.reindex h) (fun _ => Ty.unit) vs') :=
            Term.homT_congr he₁
        _ ≡ₜ (listF g₁ ⨟
              Term.homT (normalListShape B (F.reindex h) (fun _ => Ty.unit) vs')) :=
            Term.homT_precomp _ _
        _ ≡ₜ (listF g₁ ⨟
              normalListShape B ((TyFn.list F).reindex h) (fun _ => Ty.unit) vs') :=
            PEq.compR _ (PEq.symm (Term.normalListShape_list _ _ _ _))

namespace ValueShaped

variable {B : Ty}

/-- Value shapes are closed under concatenation. -/
theorem fdot {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : ValueShaped B f₁) (h₂ : ValueShaped B f₂) : ValueShaped B (f₁ ⊙ f₂) := by
  obtain ⟨F₁, a₁, vs₁, ha₁, he₁⟩ := h₁
  obtain ⟨F₂, a₂, vs₂, ha₂, he₂⟩ := h₂
  obtain ⟨g₁, hg₁, hs₁⟩ :=
    valueShape_reindex B F₁ (fun j => 2 * j) vs₁ (mergeVal vs₁ vs₂)
      (fun i => mergeVal_even vs₁ vs₂ i)
  obtain ⟨g₂, hg₂, hs₂⟩ :=
    valueShape_reindex B F₂ (fun j => 2 * j + 1) vs₂ (mergeVal vs₁ vs₂)
      (fun i => mergeVal_odd vs₁ vs₂ i)
  refine ⟨.prod (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)),
    prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂), mergeVal vs₁ vs₂,
    IsLift.prodF (IsLift.comp ha₁ hg₁) (IsLift.comp ha₂ hg₂), ?_⟩
  calc (f₁ ⊙ f₂)
      ≡ₜ ((a₁ ⨟ normalListShape B F₁ (fun _ => Ty.unit) vs₁) ⊙
          (a₂ ⨟ normalListShape B F₂ (fun _ => Ty.unit) vs₂)) :=
        PEq.compL _ (PEq.congr_prodF he₁ he₂)
    _ ≡ₜ (((a₁ ⨟ g₁) ⨟ normalListShape B (F₁.reindex (fun j => 2 * j))
            (fun _ => Ty.unit) (mergeVal vs₁ vs₂)) ⊙
          ((a₂ ⨟ g₂) ⨟ normalListShape B (F₂.reindex (fun j => 2 * j + 1))
            (fun _ => Ty.unit) (mergeVal vs₁ vs₂))) :=
        PEq.compL _ (PEq.congr_prodF
          ((PEq.compR _ hs₁).trans (PEq.symm (PEq.comp_assoc _ _ _)))
          ((PEq.compR _ hs₂).trans (PEq.symm (PEq.comp_assoc _ _ _))))
    _ ≡ₜ (prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟
          ((normalListShape B (F₁.reindex (fun j => 2 * j)) (fun _ => Ty.unit)
              (mergeVal vs₁ vs₂)) ⊙
           (normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (fun _ => Ty.unit)
              (mergeVal vs₁ vs₂)))) := by
        calc _ ≡ₜ ((prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ prodF _ _) ⨟ binconcat B) :=
              PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
          _ ≡ₜ _ := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ normalListShape B
          (.prod (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)))
          (fun _ => Ty.unit) (mergeVal vs₁ vs₂)) :=
        PEq.compR _ (PEq.symm (Term.normalListShape_prod _ _ _ _ _))

/-- Value shapes are closed under co-pairing. -/
theorem either {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : ValueShaped B f₁) (h₂ : ValueShaped B f₂) :
    ValueShaped B (Term.either f₁ f₂) := by
  obtain ⟨F₁, a₁, vs₁, ha₁, he₁⟩ := h₁
  obtain ⟨F₂, a₂, vs₂, ha₂, he₂⟩ := h₂
  obtain ⟨g₁, hg₁, hs₁⟩ :=
    valueShape_reindex B F₁ (fun j => 2 * j) vs₁ (mergeVal vs₁ vs₂)
      (fun i => mergeVal_even vs₁ vs₂ i)
  obtain ⟨g₂, hg₂, hs₂⟩ :=
    valueShape_reindex B F₂ (fun j => 2 * j + 1) vs₂ (mergeVal vs₁ vs₂)
      (fun i => mergeVal_odd vs₁ vs₂ i)
  refine ⟨.sum (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)),
    sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂), mergeVal vs₁ vs₂,
    IsLift.sumF (IsLift.comp ha₁ hg₁) (IsLift.comp ha₂ hg₂), ?_⟩
  calc Term.either f₁ f₂
      ≡ₜ Term.either (a₁ ⨟ normalListShape B F₁ (fun _ => Ty.unit) vs₁)
          (a₂ ⨟ normalListShape B F₂ (fun _ => Ty.unit) vs₂) := Term.either_congr he₁ he₂
    _ ≡ₜ Term.either ((a₁ ⨟ g₁) ⨟ normalListShape B (F₁.reindex (fun j => 2 * j))
            (fun _ => Ty.unit) (mergeVal vs₁ vs₂))
          ((a₂ ⨟ g₂) ⨟ normalListShape B (F₂.reindex (fun j => 2 * j + 1))
            (fun _ => Ty.unit) (mergeVal vs₁ vs₂)) :=
        Term.either_congr ((PEq.compR _ hs₁).trans (PEq.symm (PEq.comp_assoc _ _ _)))
          ((PEq.compR _ hs₂).trans (PEq.symm (PEq.comp_assoc _ _ _)))
    _ ≡ₜ (sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ Term.either
          (normalListShape B (F₁.reindex (fun j => 2 * j)) (fun _ => Ty.unit)
            (mergeVal vs₁ vs₂))
          (normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (fun _ => Ty.unit)
            (mergeVal vs₁ vs₂))) := PEq.symm (Term.sumF_either _ _ _ _)
    _ ≡ₜ (sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ normalListShape B
          (.sum (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)))
          (fun _ => Ty.unit) (mergeVal vs₁ vs₂)) :=
        PEq.compR _ (PEq.symm (Term.normalListShape_sum _ _ _ _ _))

/-- Value shapes are closed under the homomorphism combinator. -/
theorem homT {A : Ty} {f : Term A B⋆} (h : ValueShaped B f) :
    ValueShaped B (Term.homT f) := by
  obtain ⟨F, a, vs, ha, he⟩ := h
  refine ⟨.list F, listF a, vs, IsLift.listF ha, ?_⟩
  calc Term.homT f ≡ₜ Term.homT (a ⨟ normalListShape B F (fun _ => Ty.unit) vs) :=
        Term.homT_congr he
    _ ≡ₜ (listF a ⨟ Term.homT (normalListShape B F (fun _ => Ty.unit) vs)) :=
        Term.homT_precomp _ _
    _ ≡ₜ (listF a ⨟ normalListShape B (.list F) (fun _ => Ty.unit) vs) :=
        PEq.compR _ (PEq.symm (Term.normalListShape_list _ _ _ _))

end ValueShaped

/-! ### Constants

A constant leaf is pushed onto the unit type: the input is lifted with `unitL`, the value is
produced on the new `1`, and the empty list on the original domain. -/

/-- The constantly empty function on any type is a value shape: its shape is the shape of the
type itself, with the empty value in every leaf. -/
theorem valueShaped_nilconst (B : Ty) : (A : Ty) → ValueShaped B (toUnit A ⨟ nilT B)
  | .unit =>
      ValueShaped.congr (PEq.compL _ (PEq.unit_unique _ (Term.id Ty.unit))
        |>.trans (PEq.id_comp _)) (ValueShaped.value (nilT B))
  | .prod X Y => by
      refine ValueShaped.congr ?_
        (ValueShaped.fdot (valueShaped_nilconst B X) (valueShaped_nilconst B Y))
      calc (toUnit (X ⊗ Y) ⨟ nilT B)
          ≡ₜ (fst X Y ⨟ (toUnit X ⨟ nilT B)) := by
            refine (PEq.compL _ ?_).trans (PEq.comp_assoc _ _ _)
            exact PEq.unit_unique _ (fst X Y ⨟ toUnit X)
        _ ≡ₜ ((toUnit X ⨟ nilT B) ⊙ (toUnit Y ⨟ nilT B)) :=
            PEq.symm (Term.prodF_nilconst_binconcat (toUnit X ⨟ nilT B))
  | .sum X Y => by
      refine ValueShaped.congr ?_
        (ValueShaped.either (valueShaped_nilconst B X) (valueShaped_nilconst B Y))
      calc (toUnit (X ⊕' Y) ⨟ nilT B)
          ≡ₜ (Term.either (toUnit X) (toUnit Y) ⨟ nilT B) :=
            PEq.compL _ (PEq.unit_unique _ (Term.either (toUnit X) (toUnit Y)))
        _ ≡ₜ Term.either (toUnit X ⨟ nilT B) (toUnit Y ⨟ nilT B) :=
            Term.either_comp _ _ _
  | .list X => by
      refine ValueShaped.congr ?_ (ValueShaped.homT (valueShaped_nilconst B X))
      exact PEq.symm (Term.homT_nilconst X B)

/-- A constant is a value shape: the value is produced on a unit type added by a lift. -/
theorem valueShaped_const (B : Ty) (A : Ty) (v : Value B⋆) :
    ValueShaped B (toUnit A ⨟ v) := by
  refine ValueShaped.congr ?_
    (ValueShaped.lift_comp (IsLift.unitL A)
      (ValueShaped.fdot (ValueShaped.value v) (valueShaped_nilconst B A)))
  exact PEq.symm ((PEq.symm (PEq.comp_assoc _ _ _)).trans (Term.dotL_nilconst A B v))

/-- The inner induction: a case tree with a co-product codomain, followed by any term, is a
value shape, provided that the statement is already known for the drops into the two
summands. -/
theorem valueShaped_sumTree (B : Ty) {r : ℕ} {C₁ C₂ : Ty}
    (P₁ : ∀ {X : Ty} (g : Term X C₁), IsDrop g → ∀ k : Term C₁ B⋆, ValueShaped B (g ⨟ k))
    (P₂ : ∀ {X : Ty} (g : Term X C₂), IsDrop g → ∀ k : Term C₂ B⋆, ValueShaped B (g ⨟ k)) :
    {D : Ty} → {N : Term D (C₁ ⊕' C₂)} → IsNormalSumTree r N →
      ∀ k : Term (C₁ ⊕' C₂) B⋆, ValueShaped B (N ⨟ k)
  | _, _, @IsNormalSumTree.inl _ _ _ _ g hg _, k =>
      ValueShaped.congr (PEq.comp_assoc _ _ _) (P₁ g hg (Term.inl C₁ C₂ ⨟ k))
  | _, _, @IsNormalSumTree.inr _ _ _ _ g hg _, k =>
      ValueShaped.congr (PEq.comp_assoc _ _ _) (P₂ g hg (Term.inr C₁ C₂ ⨟ k))
  | _, _, @IsNormalSumTree.sumF _ A₁ A₂ _ _ g₁ g₂ hg₁ hg₂ _ _, k => by
      refine ValueShaped.congr ?_
        (ValueShaped.either (P₁ g₁ hg₁ (Term.inl C₁ C₂ ⨟ k))
          (P₂ g₂ hg₂ (Term.inr C₁ C₂ ⨟ k)))
      refine Term.either_ext _ _ ?_ ?_
      · calc (Term.inl A₁ A₂ ⨟ (sumF g₁ g₂ ⨟ k))
            ≡ₜ ((Term.inl A₁ A₂ ⨟ sumF g₁ g₂) ⨟ k) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((g₁ ⨟ Term.inl C₁ C₂) ⨟ k) := PEq.compL _ (PEq.nat_inl _ _)
          _ ≡ₜ (g₁ ⨟ (Term.inl C₁ C₂ ⨟ k)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (Term.inl A₁ A₂ ⨟ Term.either (g₁ ⨟ (Term.inl C₁ C₂ ⨟ k))
                (g₂ ⨟ (Term.inr C₁ C₂ ⨟ k))) := PEq.symm (Term.inl_either _ _)
      · calc (Term.inr A₁ A₂ ⨟ (sumF g₁ g₂ ⨟ k))
            ≡ₜ ((Term.inr A₁ A₂ ⨟ sumF g₁ g₂) ⨟ k) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((g₂ ⨟ Term.inr C₁ C₂) ⨟ k) := PEq.compL _ (PEq.nat_inr _ _)
          _ ≡ₜ (g₂ ⨟ (Term.inr C₁ C₂ ⨟ k)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (Term.inr A₁ A₂ ⨟ Term.either (g₁ ⨟ (Term.inl C₁ C₂ ⨟ k))
                (g₂ ⨟ (Term.inr C₁ C₂ ⨟ k))) := PEq.symm (Term.inr_either _ _)
  | _, _, @IsNormalSumTree.either _ _ _ _ _ _ _ t₁ t₂, k =>
      ValueShaped.congr (Term.either_comp _ _ _)
        (ValueShaped.either (valueShaped_sumTree B P₁ P₂ t₁ k)
          (valueShaped_sumTree B P₁ P₂ t₂ k))

/-- A drop into the unit type, followed by any value, is a value shape. -/
theorem valueShaped_toUnit (B : Ty) {X : Ty} (g : Term X Ty.unit) (k : Value B⋆) :
    ValueShaped B (g ⨟ k) :=
  ValueShaped.congr (PEq.compL _ (PEq.unit_unique _ _)) (valueShaped_const B X k)

/-! ### Drops into a sum of unit types

A drop into a finite alphabet, followed by any term out of that alphabet, is a value shape:
the sum normalisation lemma decomposes the drop into a case tree whose leaves produce a fixed
letter, and in each case the composition is a constant.

The induction only uses that the alphabet is a co-product tree of unit types, which is
slightly more general than being a finite alphabet (`Lax149335Proofs.Ty.IsFinAlph` fixes the
bracketing of the co-products).  The extra generality is what makes the *joint*
simplification of two drops possible: two drops into `B*` are merged into a single drop into
`(B + B)*`, and `B + B` is again a co-product tree of unit types. -/

/-- Types that are built from the unit type using co-products.  These are exactly the finite
alphabets up to the bracketing of the co-products. -/
inductive Ty.IsSumUnits : Ty → Prop
  /-- The unit type. -/
  | unit : Ty.IsSumUnits Ty.unit
  /-- A co-product of two such types. -/
  | sum {A B : Ty} : Ty.IsSumUnits A → Ty.IsSumUnits B → Ty.IsSumUnits (A ⊕' B)

/-- Every finite alphabet is a co-product tree of unit types. -/
theorem Ty.isSumUnits_finAlph : (n : ℕ) → Ty.IsSumUnits (Ty.finAlph n)
  | 0 => .unit
  | (n + 1) => .sum .unit (Ty.isSumUnits_finAlph n)

/-- A drop into a co-product tree of unit types, followed by any term out of that type, is a
value shape. -/
theorem valueShaped_sumUnits (B : Ty) :
    {C : Ty} → Ty.IsSumUnits C → {X : Ty} → (g : Term X C) → IsDrop g →
      ∀ k : Term C B⋆, ValueShaped B (g ⨟ k)
  | _, .unit, _, g, _, k => valueShaped_toUnit B g k
  | _, .sum h₁ h₂, _, g, hg, k => by
      obtain ⟨D, alpha, N, halpha, -, hN, he⟩ := drops_with_sum_codomain_tree g hg
      refine ValueShaped.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
      refine ValueShaped.lift_comp halpha ?_
      exact valueShaped_sumTree B (fun g' hg' k' => valueShaped_sumUnits B h₁ g' hg' k')
        (fun g' hg' k' => valueShaped_sumUnits B h₂ g' hg' k') hN k

/-! ### The leaves and the normal shapes -/

/-- Every leaf of a normal shape whose output alphabet is a co-product tree of unit types is
a value shape. -/
theorem valueShaped_of_leaf {C : Ty} (hC : Ty.IsSumUnits C) {r : ℕ} :
    {A : Ty} → {u : Term A C⋆} → IsNormalListLeafLe C r u → ValueShaped C u
  | A, _, .const v => valueShaped_const _ A v
  | _, _, .sing hg _ => valueShaped_sumUnits _ hC _ hg (pureT C)
  | _, _, @IsNormalListLeafLe.map _ _ A g hg _ => by
      refine ValueShaped.congr ?_
        (ValueShaped.homT (valueShaped_sumUnits _ hC g hg (pureT C)))
      calc listF g
          ≡ₜ (listF g ⨟ Term.id C⋆) := PEq.symm (PEq.comp_id _)
        _ ≡ₜ (listF g ⨟ Term.homT (pureT C)) :=
            PEq.compR _ (PEq.symm (Term.homT_pureT C))
        _ ≡ₜ (listF g ⨟ (listF (pureT C) ⨟ concat C)) := PEq.refl _
        _ ≡ₜ ((listF g ⨟ listF (pureT C)) ⨟ concat C) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (listF (g ⨟ pureT C) ⨟ concat C) := PEq.compL _ (PEq.list_comp _ _)

/-- Every normal shape whose output alphabet is a co-product tree of unit types is a value
shape. -/
theorem valueShaped_of_normalForm {C : Ty} (hC : Ty.IsSumUnits C) {r : ℕ} {A : Ty}
    {u : Term A C⋆} (hu : IsListNormalForm C r u) : ValueShaped C u := by
  induction hu with
  | leaf hl => exact valueShaped_of_leaf hC hl
  | nil => exact ValueShaped.value (nilT C)
  | fdot _ _ ih₁ ih₂ => exact ValueShaped.fdot ih₁ ih₂
  | either _ _ ih₁ ih₂ => exact ValueShaped.either ih₁ ih₂
  | homT _ ih => exact ValueShaped.homT ih

/-! ### Drop simplification -/

/-- **Lemma (Drop Simplification)** (appendix, *Proof of joint simplification*), for an
output alphabet that is a co-product tree of unit types. -/
theorem drop_simplification_sumUnits {A B : Ty} (hB : Ty.IsSumUnits B) (f : Term A B⋆)
    (hf : IsDrop f) : ValueShaped B f := by
  obtain ⟨D, alpha, u, ha, hu, he⟩ := drop_normListable f hf
  exact ValueShaped.congr he
    (ValueShaped.lift_comp ha (valueShaped_of_normalForm hB hu))

/-- **Lemma (Drop Simplification)** (appendix, *Proof of joint simplification*).  If `B` is a
finite alphabet and `f : A ⇒ B*` is a drop, then there is a list-polynomial functor `F`, a
lift `A ⊸ F(1,…,1)` and values `v₁,…,vₙ` of type `B*` such that
`f ≡ δ; F(v₁,…,vₙ); genconc`.  In other words, `f` becomes a simple rational term after
lifting, with all values produced in the leaves. -/
theorem drop_simplification {A B : Ty} (hB : Ty.IsFinAlph B) (f : Term A B⋆) (hf : IsDrop f) :
    ∃ (F : TyFn) (delta : Term A (F.app (fun _ => Ty.unit))) (vs : (i : ℕ) → Value B⋆),
      IsLift delta ∧
        f ≡ₜ (delta ⨟ normalListShape B F (fun _ => Ty.unit) vs) := by
  obtain ⟨N, rfl⟩ := hB
  exact drop_simplification_sumUnits (Ty.isSumUnits_finAlph N) f hf

end Lax149335Proofs

bridge_export Lax149335Proofs
