import Lax149335Proofs.Appendix.Drops.DropRank
import Mathlib.Tactic.Set

/-!
# Normal shapes for drops with a list codomain

The list normalisation lemma of the appendix produces a drop of the shape
`F(f₁,…,fₙ); genconc` (`Lax149335Proofs.normalListShape`), whose leaves `fᵢ` are constants,
singletons or homomorphic images.  Building such a shape by induction means combining two
shapes, which forces the parameters of the two multivariate functors to be renumbered.

To keep that bookkeeping in one place, this file introduces an equivalent *inductive*
description of the normal shapes (`Lax149335Proofs.IsListNormalForm`), whose constructors are the
five clauses of the definition of `Lax149335Proofs.normalListShape` read through the definition of
the concatenation combinator `genconc`: a leaf, the empty list, a concatenation `⊙`, a
co-pairing, and a homomorphic image.  Combining two such shapes is then immediate, and the
renumbering of the parameters is performed once and for all in
`Lax149335Proofs.IsListNormalForm.shaped`, which converts an inductive shape back into the form
`F(f₁,…,fₙ); genconc` of the appendix.

The predicate that the induction of the list normalisation lemma actually maintains is
`Lax149335Proofs.NormListable`: provably equal to a lift followed by a normal shape.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Leaves -/

/-- The three shapes allowed for the leaves of a drop in normal form with list codomain, with
the paper's bound on the rank of the component drop.  As for the normal forms with a
co-product or a product codomain (`Lax149335Proofs.IsSumLeaf`, `Lax149335Proofs.IsNormalProdLe`), the
bound is imposed on the *components* of the leaf, not on the leaf itself: a singleton leaf
`[g]` is one composition longer than its component. -/
inductive IsNormalListLeafLe (B : Ty) (r : ℕ) : {A : Ty} → Term A B⋆ → Prop
  /-- A constant value. -/
  | const {A : Ty} (v : Value B⋆) : IsNormalListLeafLe B r (toUnit A ⨟ v)
  /-- A singleton list. -/
  | sing {A : Ty} {g : Term A B} : IsDrop g → rank g ≤ r →
      IsNormalListLeafLe B r (g ⨟ pureT B)
  /-- A homomorphic image. -/
  | map {A : Ty} {g : Term A B} : IsDrop g → rank g ≤ r → IsNormalListLeafLe B r (listF g)

/-- A leaf with bounded components is a leaf. -/
theorem IsNormalListLeafLe.isNormalListLeaf {B : Ty} {r : ℕ} : {A : Ty} → {f : Term A B⋆} →
    IsNormalListLeafLe B r f → IsNormalListLeaf B f
  | _, _, .const v => .const v
  | _, _, .sing hg _ => .sing hg
  | _, _, .map hg _ => .map hg

/-- Leaves are monotone in the rank bound. -/
theorem IsNormalListLeafLe.mono {B : Ty} {r r' : ℕ} (h : r ≤ r') : {A : Ty} →
    {f : Term A B⋆} → IsNormalListLeafLe B r f → IsNormalListLeafLe B r' f
  | _, _, .const v => .const v
  | _, _, .sing hg hr => .sing hg (le_trans hr h)
  | _, _, .map hg hr => .map hg (le_trans hr h)

/-! ### Normal shapes, inductively -/

/-- The normal shapes with list codomain, described inductively: a leaf, the empty list, a
concatenation, a co-pairing, or a homomorphic image.  These are exactly the terms
`F(f₁,…,fₙ); genconc` of the appendix (`Lax149335Proofs.IsListNormalForm.shaped`). -/
inductive IsListNormalForm (B : Ty) (r : ℕ) : {A : Ty} → Term A B⋆ → Prop
  /-- A single leaf, the case `F = Xᵢ`. -/
  | leaf {A : Ty} {f : Term A B⋆} : IsNormalListLeafLe B r f → IsListNormalForm B r f
  /-- The empty list, the case `F = 1`. -/
  | nil : IsListNormalForm B r (nilT B)
  /-- A concatenation, the case `F = F₁ × F₂`. -/
  | fdot {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆} :
      IsListNormalForm B r f₁ → IsListNormalForm B r f₂ → IsListNormalForm B r (f₁ ⊙ f₂)
  /-- A co-pairing, the case `F = F₁ + F₂`. -/
  | either {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆} :
      IsListNormalForm B r f₁ → IsListNormalForm B r f₂ →
      IsListNormalForm B r (Term.either f₁ f₂)
  /-- A homomorphic image, the case `F = F₁*`. -/
  | homT {A : Ty} {f : Term A B⋆} : IsListNormalForm B r f → IsListNormalForm B r (homT f)

/-- Normal shapes are monotone in the rank bound. -/
theorem IsListNormalForm.mono {B : Ty} {r r' : ℕ} (h : r ≤ r') : {A : Ty} →
    {f : Term A B⋆} → IsListNormalForm B r f → IsListNormalForm B r' f
  | _, _, .leaf hl => .leaf (hl.mono h)
  | _, _, .nil => .nil
  | _, _, .fdot h₁ h₂ => .fdot (h₁.mono h) (h₂.mono h)
  | _, _, .either h₁ h₂ => .either (h₁.mono h) (h₂.mono h)
  | _, _, .homT h₁ => .homT (h₁.mono h)

/-- Every leaf of a normal shape is provably equal to a drop. -/
theorem IsNormalListLeafLe.isEqDrop {B : Ty} {r : ℕ} : {A : Ty} → {f : Term A B⋆} →
    IsNormalListLeafLe B r f → IsEqDrop f
  | _, _, .const v => IsEqDrop.of_isDrop (IsDrop.bangV _ v)
  | _, _, .sing hg _ => IsEqDrop.of_isDrop (IsDrop.comp hg (IsDrop.pureT _))
  | _, _, .map hg _ => IsEqDrop.of_isDrop (IsDrop.listF hg)

/-- Every normal shape is provably equal to a drop. -/
theorem IsListNormalForm.isEqDrop {B : Ty} {r : ℕ} : {A : Ty} → {f : Term A B⋆} →
    IsListNormalForm B r f → IsEqDrop f
  | _, _, .leaf hl => hl.isEqDrop
  | _, _, .nil => by
      refine IsEqDrop.congr ?_ (IsEqDrop.of_isDrop (IsDrop.bangV Ty.unit (nilT B)))
      exact PEq.symm ((PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans
        (PEq.id_comp _))
  | _, _, .fdot h₁ h₂ =>
      IsEqDrop.comp (IsEqDrop.prodF h₁.isEqDrop h₂.isEqDrop)
        (IsEqDrop.of_isDrop (IsDrop.binconcat B))
  | _, _, .either h₁ h₂ => IsEqDrop.either h₁.isEqDrop h₂.isEqDrop
  | _, _, .homT h₁ =>
      IsEqDrop.comp (IsEqDrop.listF h₁.isEqDrop) (IsEqDrop.of_isDrop (IsDrop.concat B))

/-- **The predicate maintained by the list normalisation lemma**: provably equal to a lift
followed by a normal shape whose leaves have components of rank at most `r`. -/
def NormListable (B : Ty) (r : ℕ) {A : Ty} (f : Term A B⋆) : Prop :=
  ∃ (D : Ty) (alpha : Term A D) (g : Term D B⋆),
    IsLift alpha ∧ IsListNormalForm B r g ∧ f ≡ₜ (alpha ⨟ g)

namespace NormListable

theorem of_isListNormalForm {B : Ty} {r : ℕ} {A : Ty} {f : Term A B⋆}
    (h : IsListNormalForm B r f) : NormListable B r f :=
  ⟨A, Term.id A, f, IsLift.id A, h, PEq.symm (PEq.id_comp f)⟩

theorem of_leaf {B : Ty} {r : ℕ} {A : Ty} {f : Term A B⋆} (h : IsNormalListLeafLe B r f) :
    NormListable B r f :=
  of_isListNormalForm (.leaf h)

theorem congr {B : Ty} {r : ℕ} {A : Ty} {f g : Term A B⋆} (h : f ≡ₜ g)
    (hg : NormListable B r g) : NormListable B r f := by
  obtain ⟨D, alpha, u, ha, hu, he⟩ := hg
  exact ⟨D, alpha, u, ha, hu, h.trans he⟩

theorem mono {B : Ty} {r r' : ℕ} (h : r ≤ r') {A : Ty} {f : Term A B⋆}
    (hf : NormListable B r f) : NormListable B r' f := by
  obtain ⟨D, alpha, u, ha, hu, he⟩ := hf
  exact ⟨D, alpha, u, ha, hu.mono h, he⟩

/-- Pre-composing with a lift. -/
theorem lift_comp {B : Ty} {r : ℕ} {A A' : Ty} {beta : Term A A'} (hb : IsLift beta)
    {f : Term A' B⋆} (hf : NormListable B r f) : NormListable B r (beta ⨟ f) := by
  obtain ⟨D, alpha, u, ha, hu, he⟩ := hf
  exact ⟨D, beta ⨟ alpha, u, IsLift.comp hb ha, hu,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem fdot {B : Ty} {r : ℕ} {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : NormListable B r f₁) (h₂ : NormListable B r f₂) : NormListable B r (f₁ ⊙ f₂) := by
  obtain ⟨D₁, a₁, u₁, ha₁, hu₁, he₁⟩ := h₁
  obtain ⟨D₂, a₂, u₂, ha₂, hu₂, he₂⟩ := h₂
  refine ⟨D₁ ⊗ D₂, prodF a₁ a₂, u₁ ⊙ u₂, IsLift.prodF ha₁ ha₂, .fdot hu₁ hu₂, ?_⟩
  calc (prodF f₁ f₂ ⨟ binconcat B)
      ≡ₜ (prodF (a₁ ⨟ u₁) (a₂ ⨟ u₂) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF he₁ he₂)
    _ ≡ₜ ((prodF a₁ a₂ ⨟ prodF u₁ u₂) ⨟ binconcat B) :=
        PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
    _ ≡ₜ (prodF a₁ a₂ ⨟ (prodF u₁ u₂ ⨟ binconcat B)) := PEq.comp_assoc _ _ _

theorem either {B : Ty} {r : ℕ} {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : NormListable B r f₁) (h₂ : NormListable B r f₂) :
    NormListable B r (Term.either f₁ f₂) := by
  obtain ⟨D₁, a₁, u₁, ha₁, hu₁, he₁⟩ := h₁
  obtain ⟨D₂, a₂, u₂, ha₂, hu₂, he₂⟩ := h₂
  refine ⟨D₁ ⊕' D₂, sumF a₁ a₂, Term.either u₁ u₂, IsLift.sumF ha₁ ha₂, .either hu₁ hu₂, ?_⟩
  calc Term.either f₁ f₂ ≡ₜ Term.either (a₁ ⨟ u₁) (a₂ ⨟ u₂) := Term.either_congr he₁ he₂
    _ ≡ₜ (sumF a₁ a₂ ⨟ Term.either u₁ u₂) := PEq.symm (Term.sumF_either _ _ _ _)

theorem homT {B : Ty} {r : ℕ} {A : Ty} {f : Term A B⋆} (h : NormListable B r f) :
    NormListable B r (Term.homT f) := by
  obtain ⟨D, a, u, ha, hu, he⟩ := h
  exact ⟨D⋆, listF a, Term.homT u, IsLift.listF ha, .homT hu,
    (Term.homT_congr he).trans (Term.homT_precomp a u)⟩

end NormListable

/-! ### Unfolding the shape `F(f₁,…,fₙ); genconc` -/

namespace Term

theorem normalListShape_param (B : Ty) (i : ℕ) (As : ℕ → Ty)
    (fs : (j : ℕ) → Term (As j) B⋆) :
    normalListShape B (.param i) As fs ≡ₜ fs i :=
  PEq.comp_id _

theorem normalListShape_unit (B : Ty) (As : ℕ → Ty) (fs : (j : ℕ) → Term (As j) B⋆) :
    normalListShape B .unit As fs ≡ₜ nilT B :=
  PEq.id_comp _

theorem normalListShape_prod (B : Ty) (F G : TyFn) (As : ℕ → Ty)
    (fs : (j : ℕ) → Term (As j) B⋆) :
    normalListShape B (.prod F G) As fs ≡ₜ
      ((normalListShape B F As fs) ⊙ (normalListShape B G As fs)) := by
  calc (prodF (F.mapN fs) (G.mapN fs) ⨟ (prodF (F.listConcatMap B) (G.listConcatMap B) ⨟
        binconcat B))
      ≡ₜ ((prodF (F.mapN fs) (G.mapN fs) ⨟ prodF (F.listConcatMap B) (G.listConcatMap B)) ⨟
        binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (F.mapN fs ⨟ F.listConcatMap B) (G.mapN fs ⨟ G.listConcatMap B) ⨟
        binconcat B) := PEq.compL _ (PEq.prod_comp _ _ _ _)

theorem normalListShape_sum (B : Ty) (F G : TyFn) (As : ℕ → Ty)
    (fs : (j : ℕ) → Term (As j) B⋆) :
    normalListShape B (.sum F G) As fs ≡ₜ
      Term.either (normalListShape B F As fs) (normalListShape B G As fs) :=
  Term.sumF_either _ _ _ _

theorem normalListShape_list (B : Ty) (F : TyFn) (As : ℕ → Ty)
    (fs : (j : ℕ) → Term (As j) B⋆) :
    normalListShape B (.list F) As fs ≡ₜ Term.homT (normalListShape B F As fs) := by
  calc (listF (F.mapN fs) ⨟ (listF (F.listConcatMap B) ⨟ concat B))
      ≡ₜ ((listF (F.mapN fs) ⨟ listF (F.listConcatMap B)) ⨟ concat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (listF (F.mapN fs ⨟ F.listConcatMap B) ⨟ concat B) :=
        PEq.compL _ (PEq.list_comp _ _)

/-! ### Renumbering the parameters -/

/-- Renumbering the parameters of a multivariate list-polynomial functor. -/
def TyFn.reindex : TyFn → (ℕ → ℕ) → TyFn
  | .param i, h => .param (h i)
  | .unit, _ => .unit
  | .prod F G, h => .prod (F.reindex h) (G.reindex h)
  | .sum F G, h => .sum (F.reindex h) (G.reindex h)
  | .list F, h => .list (F.reindex h)

/-- The parameters used by a renumbered functor are the renumbered parameters. -/
theorem TyFn.usesParam_reindex : (F : TyFn) → (h : ℕ → ℕ) → (i : ℕ) →
    (F.reindex h).usesParam i → ∃ j, F.usesParam j ∧ h j = i
  | .param k, _, _, hk => ⟨k, rfl, hk⟩
  | .unit, _, _, hk => absurd hk (by simp [TyFn.reindex, TyFn.usesParam])
  | .prod F G, h, i, hk => by
      rcases hk with hk | hk
      · obtain ⟨j, hj, hji⟩ := F.usesParam_reindex h i hk
        exact ⟨j, Or.inl hj, hji⟩
      · obtain ⟨j, hj, hji⟩ := G.usesParam_reindex h i hk
        exact ⟨j, Or.inr hj, hji⟩
  | .sum F G, h, i, hk => by
      rcases hk with hk | hk
      · obtain ⟨j, hj, hji⟩ := F.usesParam_reindex h i hk
        exact ⟨j, Or.inl hj, hji⟩
      · obtain ⟨j, hj, hji⟩ := G.usesParam_reindex h i hk
        exact ⟨j, Or.inr hj, hji⟩
  | .list F, h, i, hk => F.usesParam_reindex h i hk

end Term

/-! ### Leaf environments

A leaf environment packages the domain of a leaf together with the leaf itself, so that two
environments can be merged without transporting terms along equalities of types. -/

/-- A leaf of a normal shape: its domain together with the term. -/
def Leaf (B : Ty) : Type := Σ A : Ty, Term A B⋆

/-- The domains of a leaf environment. -/
def leafTy {B : Ty} (L : ℕ → Leaf B) : ℕ → Ty := fun i => (L i).1

/-- The terms of a leaf environment. -/
def leafTm {B : Ty} (L : ℕ → Leaf B) : (i : ℕ) → Term (leafTy L i) B⋆ := fun i => (L i).2

/-- The leaf environment that is used for the parameters that do not occur. -/
def dummyLeaf (B : Ty) : Leaf B := ⟨Ty.unit, nilT B⟩

/-- Two equal leaves are connected by a lift. -/
theorem lift_of_leaf_eq {B : Ty} {l l' : Leaf B} (h : l' = l) :
    ∃ gamma : Term l.1 l'.1, IsLift gamma ∧ l.2 ≡ₜ (gamma ⨟ l'.2) := by
  cases h
  exact ⟨Term.id _, IsLift.id _, PEq.symm (PEq.id_comp _)⟩

/-- Transporting the leaf condition along an equality of leaves. -/
theorem leaf_transfer {B : Ty} {r : ℕ} {l l' : Leaf B} (h : l = l')
    (hl : IsNormalListLeafLe B r l'.2) : IsNormalListLeafLe B r l.2 := by
  cases h; exact hl

/-- Renumbering the parameters of a normal shape, up to a lift. -/
theorem shape_reindex (B : Ty) : (F : Term.TyFn) → (h : ℕ → ℕ) → (L L' : ℕ → Leaf B) →
    (hL : ∀ i, L' (h i) = L i) →
    ∃ gamma : Term (F.app (leafTy L)) ((F.reindex h).app (leafTy L')),
      IsLift gamma ∧
        normalListShape B F (leafTy L) (leafTm L) ≡ₜ
          (gamma ⨟ normalListShape B (F.reindex h) (leafTy L') (leafTm L'))
  | .param i, h, L, L', hL => by
      obtain ⟨gamma, hg, he⟩ := lift_of_leaf_eq (hL i)
      refine ⟨gamma, hg, ?_⟩
      calc normalListShape B (.param i) (leafTy L) (leafTm L) ≡ₜ leafTm L i :=
            Term.normalListShape_param _ _ _ _
        _ ≡ₜ (gamma ⨟ leafTm L' (h i)) := he
        _ ≡ₜ (gamma ⨟ normalListShape B (.param (h i)) (leafTy L') (leafTm L')) :=
            PEq.compR _ (PEq.symm (Term.normalListShape_param _ _ _ _))
  | .unit, h, L, L', _ => by
      refine ⟨Term.id Ty.unit, IsLift.id _, ?_⟩
      calc normalListShape B .unit (leafTy L) (leafTm L) ≡ₜ nilT B :=
            Term.normalListShape_unit _ _ _
        _ ≡ₜ normalListShape B .unit (leafTy L') (leafTm L') :=
            PEq.symm (Term.normalListShape_unit _ _ _)
        _ ≡ₜ (Term.id Ty.unit ⨟ normalListShape B .unit (leafTy L') (leafTm L')) :=
            PEq.symm (PEq.id_comp _)
  | .prod F G, h, L, L', hL => by
      obtain ⟨g₁, hg₁, he₁⟩ := shape_reindex B F h L L' hL
      obtain ⟨g₂, hg₂, he₂⟩ := shape_reindex B G h L L' hL
      refine ⟨prodF g₁ g₂, IsLift.prodF hg₁ hg₂, ?_⟩
      calc normalListShape B (.prod F G) (leafTy L) (leafTm L)
          ≡ₜ ((normalListShape B F (leafTy L) (leafTm L)) ⊙
              (normalListShape B G (leafTy L) (leafTm L))) :=
            Term.normalListShape_prod _ _ _ _ _
        _ ≡ₜ ((g₁ ⨟ normalListShape B (F.reindex h) (leafTy L') (leafTm L')) ⊙
              (g₂ ⨟ normalListShape B (G.reindex h) (leafTy L') (leafTm L'))) :=
            PEq.compL _ (PEq.congr_prodF he₁ he₂)
        _ ≡ₜ (prodF g₁ g₂ ⨟ ((normalListShape B (F.reindex h) (leafTy L') (leafTm L')) ⊙
              (normalListShape B (G.reindex h) (leafTy L') (leafTm L')))) := by
            calc ((g₁ ⨟ _) ⊙ (g₂ ⨟ _))
                ≡ₜ ((prodF g₁ g₂ ⨟ prodF _ _) ⨟ binconcat B) :=
                  PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
              _ ≡ₜ (prodF g₁ g₂ ⨟ (prodF _ _ ⨟ binconcat B)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (prodF g₁ g₂ ⨟ normalListShape B ((TyFn.prod F G).reindex h) (leafTy L')
              (leafTm L')) :=
            PEq.compR _ (PEq.symm (Term.normalListShape_prod _ _ _ _ _))
  | .sum F G, h, L, L', hL => by
      obtain ⟨g₁, hg₁, he₁⟩ := shape_reindex B F h L L' hL
      obtain ⟨g₂, hg₂, he₂⟩ := shape_reindex B G h L L' hL
      refine ⟨sumF g₁ g₂, IsLift.sumF hg₁ hg₂, ?_⟩
      calc normalListShape B (.sum F G) (leafTy L) (leafTm L)
          ≡ₜ Term.either (normalListShape B F (leafTy L) (leafTm L))
              (normalListShape B G (leafTy L) (leafTm L)) :=
            Term.normalListShape_sum _ _ _ _ _
        _ ≡ₜ Term.either (g₁ ⨟ normalListShape B (F.reindex h) (leafTy L') (leafTm L'))
              (g₂ ⨟ normalListShape B (G.reindex h) (leafTy L') (leafTm L')) :=
            Term.either_congr he₁ he₂
        _ ≡ₜ (sumF g₁ g₂ ⨟ Term.either
              (normalListShape B (F.reindex h) (leafTy L') (leafTm L'))
              (normalListShape B (G.reindex h) (leafTy L') (leafTm L'))) :=
            PEq.symm (Term.sumF_either _ _ _ _)
        _ ≡ₜ (sumF g₁ g₂ ⨟ normalListShape B ((TyFn.sum F G).reindex h) (leafTy L')
              (leafTm L')) :=
            PEq.compR _ (PEq.symm (Term.normalListShape_sum _ _ _ _ _))
  | .list F, h, L, L', hL => by
      obtain ⟨g₁, hg₁, he₁⟩ := shape_reindex B F h L L' hL
      refine ⟨listF g₁, IsLift.listF hg₁, ?_⟩
      calc normalListShape B (.list F) (leafTy L) (leafTm L)
          ≡ₜ Term.homT (normalListShape B F (leafTy L) (leafTm L)) :=
            Term.normalListShape_list _ _ _ _
        _ ≡ₜ Term.homT (g₁ ⨟ normalListShape B (F.reindex h) (leafTy L') (leafTm L')) :=
            Term.homT_congr he₁
        _ ≡ₜ (listF g₁ ⨟ Term.homT
              (normalListShape B (F.reindex h) (leafTy L') (leafTm L'))) :=
            Term.homT_precomp _ _
        _ ≡ₜ (listF g₁ ⨟ normalListShape B ((TyFn.list F).reindex h) (leafTy L')
              (leafTm L')) :=
            PEq.compR _ (PEq.symm (Term.normalListShape_list _ _ _ _))

/-! ### From an inductive shape to the shape of the appendix -/

/-- Provably equal to a lift followed by a drop in the normal form `F(f₁,…,fₙ); genconc` of
the appendix. -/
def Shaped (B : Ty) (r : ℕ) {A : Ty} (f : Term A B⋆) : Prop :=
  ∃ (F : Term.TyFn) (L : ℕ → Leaf B) (alpha : Term A (F.app (leafTy L))),
    IsLift alpha ∧ (∀ i, F.usesParam i → IsNormalListLeafLe B r (leafTm L i)) ∧
      f ≡ₜ (alpha ⨟ normalListShape B F (leafTy L) (leafTm L))

/-- The merge of two leaf environments: the first one on the even indices, the second one on
the odd indices. -/
def mergeLeaf {B : Ty} (L₁ L₂ : ℕ → Leaf B) : ℕ → Leaf B :=
  fun i => if i % 2 = 0 then L₁ (i / 2) else L₂ (i / 2)

theorem mergeLeaf_even {B : Ty} (L₁ L₂ : ℕ → Leaf B) (i : ℕ) :
    mergeLeaf L₁ L₂ (2 * i) = L₁ i := by
  simp [mergeLeaf, Nat.mul_mod_right]

theorem mergeLeaf_odd {B : Ty} (L₁ L₂ : ℕ → Leaf B) (i : ℕ) :
    mergeLeaf L₁ L₂ (2 * i + 1) = L₂ i := by
  have h₁ : (2 * i + 1) % 2 = 1 := by omega
  have h₂ : (2 * i + 1) / 2 = i := by omega
  simp [mergeLeaf, h₁, h₂]

/-- Every inductive normal shape is a drop in the normal form of the appendix. -/
theorem IsListNormalForm.shaped {B : Ty} {r : ℕ} : {A : Ty} → {f : Term A B⋆} →
    IsListNormalForm B r f → Shaped B r f := by
  intro A f hf
  induction hf with
  | @leaf A f hl =>
      refine ⟨.param 0, fun _ => ⟨A, f⟩, Term.id A, IsLift.id A, ?_, ?_⟩
      · intro i _; exact hl
      · exact (PEq.symm (PEq.comp_id f)).trans (PEq.symm (PEq.id_comp _))
  | nil =>
      refine ⟨.unit, fun _ => dummyLeaf B, Term.id Ty.unit, IsLift.id _, ?_, ?_⟩
      · intro i hi; exact absurd hi (by simp [Term.TyFn.usesParam])
      · exact PEq.symm ((PEq.id_comp _).trans (PEq.id_comp _))
  | @fdot A₁ A₂ f₁ f₂ _ _ ih₁ ih₂ =>
      obtain ⟨F₁, L₁, a₁, ha₁, hl₁, he₁⟩ := ih₁
      obtain ⟨F₂, L₂, a₂, ha₂, hl₂, he₂⟩ := ih₂
      set L := mergeLeaf L₁ L₂ with hLdef
      obtain ⟨g₁, hg₁, hs₁⟩ :=
        shape_reindex B F₁ (fun j => 2 * j) L₁ L (fun i => mergeLeaf_even L₁ L₂ i)
      obtain ⟨g₂, hg₂, hs₂⟩ :=
        shape_reindex B F₂ (fun j => 2 * j + 1) L₂ L (fun i => mergeLeaf_odd L₁ L₂ i)
      refine ⟨.prod (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)), L,
        prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂), IsLift.prodF (IsLift.comp ha₁ hg₁) (IsLift.comp ha₂ hg₂),
        ?_, ?_⟩
      · rintro i (hi | hi)
        · obtain ⟨j, hj, hji⟩ := Term.TyFn.usesParam_reindex F₁ _ i hi
          subst hji
          exact leaf_transfer (mergeLeaf_even L₁ L₂ j) (hl₁ j hj)
        · obtain ⟨j, hj, hji⟩ := Term.TyFn.usesParam_reindex F₂ _ i hi
          subst hji
          exact leaf_transfer (mergeLeaf_odd L₁ L₂ j) (hl₂ j hj)
      · calc (f₁ ⊙ f₂)
            ≡ₜ ((a₁ ⨟ normalListShape B F₁ (leafTy L₁) (leafTm L₁)) ⊙
                (a₂ ⨟ normalListShape B F₂ (leafTy L₂) (leafTm L₂))) :=
              PEq.compL _ (PEq.congr_prodF he₁ he₂)
          _ ≡ₜ ((a₁ ⨟ (g₁ ⨟ normalListShape B (F₁.reindex (fun j => 2 * j)) (leafTy L)
                (leafTm L))) ⊙
                (a₂ ⨟ (g₂ ⨟ normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (leafTy L)
                (leafTm L)))) :=
              PEq.compL _ (PEq.congr_prodF (PEq.compR _ hs₁) (PEq.compR _ hs₂))
          _ ≡ₜ (((a₁ ⨟ g₁) ⨟ normalListShape B (F₁.reindex (fun j => 2 * j)) (leafTy L)
                (leafTm L)) ⊙
                ((a₂ ⨟ g₂) ⨟ normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (leafTy L)
                (leafTm L))) :=
              PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.comp_assoc _ _ _))
                (PEq.symm (PEq.comp_assoc _ _ _)))
          _ ≡ₜ (prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟
                ((normalListShape B (F₁.reindex (fun j => 2 * j)) (leafTy L) (leafTm L)) ⊙
                 (normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (leafTy L)
                   (leafTm L)))) := by
              calc _ ≡ₜ ((prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ prodF _ _) ⨟ binconcat B) :=
                    PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
                _ ≡ₜ _ := PEq.comp_assoc _ _ _
          _ ≡ₜ (prodF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ normalListShape B
                (.prod (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)))
                (leafTy L) (leafTm L)) :=
              PEq.compR _ (PEq.symm (Term.normalListShape_prod _ _ _ _ _))
  | @either A₁ A₂ f₁ f₂ _ _ ih₁ ih₂ =>
      obtain ⟨F₁, L₁, a₁, ha₁, hl₁, he₁⟩ := ih₁
      obtain ⟨F₂, L₂, a₂, ha₂, hl₂, he₂⟩ := ih₂
      set L := mergeLeaf L₁ L₂ with hLdef
      obtain ⟨g₁, hg₁, hs₁⟩ :=
        shape_reindex B F₁ (fun j => 2 * j) L₁ L (fun i => mergeLeaf_even L₁ L₂ i)
      obtain ⟨g₂, hg₂, hs₂⟩ :=
        shape_reindex B F₂ (fun j => 2 * j + 1) L₂ L (fun i => mergeLeaf_odd L₁ L₂ i)
      refine ⟨.sum (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)), L,
        sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂), IsLift.sumF (IsLift.comp ha₁ hg₁) (IsLift.comp ha₂ hg₂),
        ?_, ?_⟩
      · rintro i (hi | hi)
        · obtain ⟨j, hj, hji⟩ := Term.TyFn.usesParam_reindex F₁ _ i hi
          subst hji
          exact leaf_transfer (mergeLeaf_even L₁ L₂ j) (hl₁ j hj)
        · obtain ⟨j, hj, hji⟩ := Term.TyFn.usesParam_reindex F₂ _ i hi
          subst hji
          exact leaf_transfer (mergeLeaf_odd L₁ L₂ j) (hl₂ j hj)
      · calc Term.either f₁ f₂
            ≡ₜ Term.either (a₁ ⨟ normalListShape B F₁ (leafTy L₁) (leafTm L₁))
                (a₂ ⨟ normalListShape B F₂ (leafTy L₂) (leafTm L₂)) :=
              Term.either_congr he₁ he₂
          _ ≡ₜ Term.either ((a₁ ⨟ g₁) ⨟ normalListShape B (F₁.reindex (fun j => 2 * j))
                (leafTy L) (leafTm L))
                ((a₂ ⨟ g₂) ⨟ normalListShape B (F₂.reindex (fun j => 2 * j + 1))
                (leafTy L) (leafTm L)) :=
              Term.either_congr ((PEq.compR _ hs₁).trans (PEq.symm (PEq.comp_assoc _ _ _)))
                ((PEq.compR _ hs₂).trans (PEq.symm (PEq.comp_assoc _ _ _)))
          _ ≡ₜ (sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ Term.either
                (normalListShape B (F₁.reindex (fun j => 2 * j)) (leafTy L) (leafTm L))
                (normalListShape B (F₂.reindex (fun j => 2 * j + 1)) (leafTy L)
                  (leafTm L))) :=
              PEq.symm (Term.sumF_either _ _ _ _)
          _ ≡ₜ (sumF (a₁ ⨟ g₁) (a₂ ⨟ g₂) ⨟ normalListShape B
                (.sum (F₁.reindex (fun j => 2 * j)) (F₂.reindex (fun j => 2 * j + 1)))
                (leafTy L) (leafTm L)) :=
              PEq.compR _ (PEq.symm (Term.normalListShape_sum _ _ _ _ _))
  | @homT A f _ ih =>
      obtain ⟨F, L, a, ha, hl, he⟩ := ih
      refine ⟨.list F, L, listF a, IsLift.listF ha, hl, ?_⟩
      calc Term.homT f ≡ₜ Term.homT (a ⨟ normalListShape B F (leafTy L) (leafTm L)) :=
            Term.homT_congr he
        _ ≡ₜ (listF a ⨟ Term.homT (normalListShape B F (leafTy L) (leafTm L))) :=
            Term.homT_precomp _ _
        _ ≡ₜ (listF a ⨟ normalListShape B (.list F) (leafTy L) (leafTm L)) :=
            PEq.compR _ (PEq.symm (Term.normalListShape_list _ _ _ _))

/-- Every term that is provably a lift followed by a normal shape is a drop in the normal
form `F(f₁,…,fₙ); genconc` of the appendix. -/
theorem NormListable.shaped {B : Ty} {r : ℕ} {A : Ty} {f : Term A B⋆}
    (hf : NormListable B r f) : Shaped B r f := by
  obtain ⟨D, alpha, u, ha, hu, he⟩ := hf
  obtain ⟨F, L, beta, hb, hl, hs⟩ := hu.shaped
  exact ⟨F, L, alpha ⨟ beta, IsLift.comp ha hb, hl,
    (he.trans (PEq.compR _ hs)).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
