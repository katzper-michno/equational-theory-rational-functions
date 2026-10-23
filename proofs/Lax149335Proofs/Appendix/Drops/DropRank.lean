import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Lax149335Proofs.Appendix.ConcatenationMaps
import Lax149335Proofs.GeneralCompleteness.LiftsAndDrops

/-!
# Composition rank and normalised drop functions (appendix)

The definitions used by the appendix section whose goal is to prove the exchange lemma
(Lemma 7.5) and the joint simplification of drops (Lemma 7.3):

* the composition rank of a term;
* normalised drop functions, according to the shape of the codomain (sum, product, list),
  both without and with a bound on the rank of their components.

The normalisation lemmas themselves are proved in
`Lax149335Proofs.Appendix.Drops.SumProdNormalisation` (sum and product codomain) and stated in
`Lax149335Proofs.Appendix.Drops.DropNormalisation` (list codomain).

Multivariate list-polynomial functors are the ones of `Lax149335Proofs.Appendix.ConcatenationMaps`
(`Lax149335Proofs.Term.TyFn`), and the two-parameter functors used for the collectors are
`Lax149335Proofs.Term.TyF2`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Composition rank -/

/-- **Definition (Composition rank).**  The rank of a term is the length of the longest chain
of compositions along a single sequential thread; the prime functions have rank `0`.

The prime drop `1 ; v` is a composition whose intermediate type is the unit type, and every
term of that shape is provably equal to such a prime drop (the unit type is terminal); this
is why the first clause below gives rank `0` to all of them.  See `Lax149335Proofs.rank_const`. -/
def rank : {A B : Ty} → Term A B → ℕ
  | _, _, @Term.comp _ M _ f g => if M = Ty.unit then 0 else rank f + rank g + 1
  | _, _, .prodF f g => max (rank f) (rank g)
  | _, _, .sumF f g => max (rank f) (rank g)
  | _, _, .listF f => rank f
  | _, _, _ => 0

/-- The rank of a composition. -/
theorem rank_comp {A M B : Ty} (f : Term A M) (g : Term M B) :
    rank (f ⨟ g) = if M = Ty.unit then 0 else rank f + rank g + 1 := by
  simp [rank]

/-- The rank of a composition, when the intermediate type is not the unit type. -/
theorem rank_comp_of_ne {A M B : Ty} (f : Term A M) (g : Term M B) (h : M ≠ Ty.unit) :
    rank (f ⨟ g) = rank f + rank g + 1 := by
  rw [rank_comp]; simp [h]

/-- A composition never has rank larger than the rank of its two factors plus one. -/
theorem rank_comp_le {A M B : Ty} (f : Term A M) (g : Term M B) :
    rank (f ⨟ g) ≤ rank f + rank g + 1 := by
  rw [rank_comp]; split <;> omega

/-- The prime drop `1 ; v` has rank `0`, whatever the value `v`. -/
theorem rank_const {A B : Ty} (f : Term A Ty.unit) (v : Value B) : rank (f ⨟ v) = 0 := by
  simp [rank]

namespace Term

/-- The parameters that occur in a multivariate list-polynomial functor. -/
def TyFn.usesParam : TyFn → ℕ → Prop
  | .param j, i => j = i
  | .unit, _ => False
  | .prod F G, i => F.usesParam i ∨ G.usesParam i
  | .sum F G, i => F.usesParam i ∨ G.usesParam i
  | .list F, i => F.usesParam i

/-- The concatenation combinator of a multivariate list-polynomial functor whose parameters
are all instantiated by a list type: the term `F(B*,…,B*) → B*` that concatenates all the
lists occurring in the input.  This is the map written `genconc` in the appendix. -/
def TyFn.listConcatMap : (F : TyFn) → (B : Ty) → Term (F.app (fun _ => B⋆)) B⋆
  | .param _, B => Term.id B⋆
  | .unit, B => nilT B
  | .prod F G, B => (F.listConcatMap B) ⊙ (G.listConcatMap B)
  | .sum F G, B => either (F.listConcatMap B) (G.listConcatMap B)
  | .list F, B => homT (F.listConcatMap B)

end Term

/-! ### Normalised drop functions -/

/-- **Definition (Normalised drop functions), sum codomain: one component.**  A component of
a drop in normal form with codomain `B₁ + B₂` is a drop `g` of rank at most `r` followed by
one of the two co-projections. -/
inductive IsSumLeaf (r : ℕ) : {A B₁ B₂ : Ty} → Term A (B₁ ⊕' B₂) → Prop
  /-- `g; Left`. -/
  | inl {A B₁ B₂ : Ty} {g : Term A B₁} : IsDrop g → rank g ≤ r →
      IsSumLeaf r (g ⨟ Term.inl B₁ B₂)
  /-- `g; Right`. -/
  | inr {A B₁ B₂ : Ty} {g : Term A B₂} : IsDrop g → rank g ≤ r →
      IsSumLeaf r (g ⨟ Term.inr B₁ B₂)

/-- **Definition (Normalised drop functions), sum codomain.**  A drop with codomain
`B₁ + B₂` is in normal form if it is an `n`-ary co-pairing, associated to the right, of
components of the form `gᵢ ; Left` or `gᵢ ; Right`, where every `gᵢ` is a drop of rank at
most `r`. -/
inductive IsNormalSumVec (r : ℕ) : {A B₁ B₂ : Ty} → Term A (B₁ ⊕' B₂) → Prop
  /-- A co-pairing with a single component. -/
  | single {A B₁ B₂ : Ty} {f : Term A (B₁ ⊕' B₂)} : IsSumLeaf r f → IsNormalSumVec r f
  /-- One more component, added on the left. -/
  | cons {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊕' B₂)} {f₂ : Term A₂ (B₁ ⊕' B₂)} :
      IsSumLeaf r f₁ → IsNormalSumVec r f₂ → IsNormalSumVec r (Term.either f₁ f₂)

/-- A component of a normal form is a drop. -/
theorem IsSumLeaf.isDrop {r : ℕ} : {A B₁ B₂ : Ty} → {g : Term A (B₁ ⊕' B₂)} →
    IsSumLeaf r g → IsDrop g
  | _, _, _, _, .inl hg _ => IsDrop.comp hg (IsDrop.inl _ _)
  | _, _, _, _, .inr hg _ => IsDrop.comp hg (IsDrop.inr _ _)

/-- A normal form with sum codomain is a drop. -/
theorem IsNormalSumVec.isDrop {r : ℕ} : {A B₁ B₂ : Ty} → {g : Term A (B₁ ⊕' B₂)} →
    IsNormalSumVec r g → IsDrop g
  | _, _, _, _, .single hl => hl.isDrop
  | _, _, _, _, .cons hl ht =>
      IsDrop.comp (IsDrop.sumF hl.isDrop ht.isDrop) (IsDrop.codiag _)

/-- **Definition (Normalised drop functions), product codomain.**  A drop with codomain
`B₁ × B₂` is in normal form if it is an `n`-ary co-pairing of products `xᵢ × yᵢ`. -/
inductive IsNormalProd : {A B₁ B₂ : Ty} → Term A (B₁ ⊗ B₂) → Prop
  /-- A single case `x × y`. -/
  | prodF {X Y B₁ B₂ : Ty} {x : Term X B₁} {y : Term Y B₂} :
      IsDrop x → IsDrop y → IsNormalProd (Term.prodF x y)
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊗ B₂)} {f₂ : Term A₂ (B₁ ⊗ B₂)} :
      IsNormalProd f₁ → IsNormalProd f₂ → IsNormalProd (Term.either f₁ f₂)

/-- The three shapes allowed for the components of a drop in normal form with list codomain:
a constant `1; v`, a singleton `[g]`, or a homomorphic image `g*`. -/
inductive IsNormalListLeaf (B : Ty) : {A : Ty} → Term A B⋆ → Prop
  /-- A constant value. -/
  | const {A : Ty} (v : Value B⋆) : IsNormalListLeaf B (toUnit A ⨟ v)
  /-- A singleton list. -/
  | sing {A : Ty} {g : Term A B} : IsDrop g → IsNormalListLeaf B (g ⨟ pureT B)
  /-- A homomorphic image. -/
  | map {A : Ty} {g : Term A B} : IsDrop g → IsNormalListLeaf B (listF g)

/-- **Definition (Normalised drop functions), list codomain.**  The shape `F(f₁,…,fₙ); genconc`
of a drop in normal form with list codomain. -/
def normalListShape (B : Ty) (F : TyFn) (As : ℕ → Ty)
    (fs : (i : ℕ) → Term (As i) B⋆) : Term (F.app As) B⋆ :=
  F.mapN fs ⨟ F.listConcatMap B

/-! ### The normalisation lemmas

The paper requires that the *components* `gᵢ` (respectively `xᵢ, yᵢ`) of the normal form have
at most the rank of the original drop (`⃗g ⪯ f`); this is what the rank bound of
`Lax149335Proofs.IsSumLeaf` above, and of `Lax149335Proofs.IsNormalProdLe` below, expresses.  Read as a
condition on the whole normal form it would be too strong: already the shapes `g ; Left` and
`g ; Right`, and every case of an `n`-ary co-pairing, raise the rank by one. -/

/-- **Definition (Normalised drop functions), product codomain**, with a bound on the rank of
the components. -/
inductive IsNormalProdLe (r : ℕ) : {A B₁ B₂ : Ty} → Term A (B₁ ⊗ B₂) → Prop
  /-- A single case `x × y`. -/
  | prodF {X Y B₁ B₂ : Ty} {x : Term X B₁} {y : Term Y B₂} :
      IsDrop x → IsDrop y → rank x ≤ r → rank y ≤ r → IsNormalProdLe r (Term.prodF x y)
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊗ B₂)} {f₂ : Term A₂ (B₁ ⊗ B₂)} :
      IsNormalProdLe r f₁ → IsNormalProdLe r f₂ → IsNormalProdLe r (Term.either f₁ f₂)

/-- A normal form with bounded components is in normal form. -/
theorem IsNormalProdLe.isNormalProd {r : ℕ} : {A B₁ B₂ : Ty} → {g : Term A (B₁ ⊗ B₂)} →
    IsNormalProdLe r g → IsNormalProd g
  | _, _, _, _, .prodF hx hy _ _ => .prodF hx hy
  | _, _, _, _, .either h₁ h₂ => .either h₁.isNormalProd h₂.isNormalProd

end Lax149335Proofs

bridge_export Lax149335Proofs
