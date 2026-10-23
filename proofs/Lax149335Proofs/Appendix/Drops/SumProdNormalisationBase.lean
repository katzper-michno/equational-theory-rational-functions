import Lax149335Proofs.Preliminaries.Overview
import Lax149335Proofs.Appendix.Drops.DropRank
import Lax149335Proofs.Preliminaries.StringRepresentation
import Mathlib.Tactic.SplitIfs

/-!
# Normalisation of drops with sum or product codomain: the normal forms

This file contains the first half of the appendix section *Normalisation with sum or product
codomain*: the shapes that the two normalisation lemmas produce, and the tools that the
induction of `Lax149335Proofs.Appendix.Drops.SumProdNormalisation` uses.

* the normal form with co-product codomain as a *case tree* (`Lax149335Proofs.IsNormalSumTree`) and
  the normal form with product codomain (`Lax149335Proofs.IsNormalProd`);
* the *spine* of a drop (`Lax149335Proofs.IsDrop.spine`), i.e. the case analysis on its last prime
  function, which the induction is driven by;
* two more coherence laws for the associators;
* normalisation up to a lift (`Lax149335Proofs.NormSum`, `Lax149335Proofs.NormProd`), the form in which
  the two lemmas are stated during the induction;
* co-pairing trees (`Lax149335Proofs.CopairTree`), which carry the normalisation of a drop whose
  codomain is a co-product of the two codomains of interest.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Normal forms with sum codomain, as case trees -/

/-- **Normalised drop functions with sum codomain, tree version.**  An `n`-ary co-pairing of
terms of the three shapes `g ; Left`, `g ; Right` and `g₁ + g₂` allowed by the appendix, all
of whose components are drops of rank at most `r`. -/
inductive IsNormalSumTree (r : ℕ) : {A B₁ B₂ : Ty} → Term A (B₁ ⊕' B₂) → Prop
  /-- `g; Left`. -/
  | inl {A B₁ B₂ : Ty} {g : Term A B₁} : IsDrop g → rank g ≤ r →
      IsNormalSumTree r (g ⨟ Term.inl B₁ B₂)
  /-- `g; Right`. -/
  | inr {A B₁ B₂ : Ty} {g : Term A B₂} : IsDrop g → rank g ≤ r →
      IsNormalSumTree r (g ⨟ Term.inr B₁ B₂)
  /-- `g₁ + g₂`. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} {g₁ : Term A₁ B₁} {g₂ : Term A₂ B₂} :
      IsDrop g₁ → IsDrop g₂ → rank g₁ ≤ r → rank g₂ ≤ r →
      IsNormalSumTree r (Term.sumF g₁ g₂)
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊕' B₂)} {f₂ : Term A₂ (B₁ ⊕' B₂)} :
      IsNormalSumTree r f₁ → IsNormalSumTree r f₂ → IsNormalSumTree r (Term.either f₁ f₂)

/-- Case trees are monotone in the rank bound. -/
theorem IsNormalSumTree.mono {r r' : ℕ} (h : r ≤ r') : {A B₁ B₂ : Ty} →
    {g : Term A (B₁ ⊕' B₂)} → IsNormalSumTree r g → IsNormalSumTree r' g
  | _, _, _, _, .inl hg hr => .inl hg (hr.trans h)
  | _, _, _, _, .inr hg hr => .inr hg (hr.trans h)
  | _, _, _, _, .sumF h₁ h₂ r₁ r₂ => .sumF h₁ h₂ (r₁.trans h) (r₂.trans h)
  | _, _, _, _, .either t₁ t₂ => .either (t₁.mono h) (t₂.mono h)

/-- Normal forms with product codomain are monotone in the rank bound. -/
theorem IsNormalProdLe.mono {r r' : ℕ} (h : r ≤ r') : {A B₁ B₂ : Ty} →
    {g : Term A (B₁ ⊗ B₂)} → IsNormalProdLe r g → IsNormalProdLe r' g
  | _, _, _, _, .prodF hx hy rx ry => .prodF hx hy (rx.trans h) (ry.trans h)
  | _, _, _, _, .either t₁ t₂ => .either (t₁.mono h) (t₂.mono h)

/-- A normal form with sum codomain is a drop. -/
theorem IsNormalSumTree.isDrop {r : ℕ} : {A B₁ B₂ : Ty} → {g : Term A (B₁ ⊕' B₂)} →
    IsNormalSumTree r g → IsDrop g
  | _, _, _, _, .inl hg _ => IsDrop.comp hg (IsDrop.inl _ _)
  | _, _, _, _, .inr hg _ => IsDrop.comp hg (IsDrop.inr _ _)
  | _, _, _, _, .sumF h₁ h₂ _ _ => IsDrop.sumF h₁ h₂
  | _, _, _, _, .either t₁ t₂ =>
      IsDrop.comp (IsDrop.sumF t₁.isDrop t₂.isDrop) (IsDrop.codiag _)

/-- A normal form with product codomain is a drop. -/
theorem IsNormalProdLe.isDrop {r : ℕ} : {A B₁ B₂ : Ty} → {g : Term A (B₁ ⊗ B₂)} →
    IsNormalProdLe r g → IsDrop g
  | _, _, _, _, .prodF hx hy _ _ => IsDrop.prodF hx hy
  | _, _, _, _, .either t₁ t₂ =>
      IsDrop.comp (IsDrop.sumF t₁.isDrop t₂.isDrop) (IsDrop.codiag _)

/-! ### The spine of a drop -/

/-- The drops that are not built by the composition combinator: the prime drops of Table 1
and the three functoriality combinators applied to drops. -/
inductive IsDropAtom : {A B : Ty} → Term A B → Prop
  | prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsDrop f → IsDrop g → IsDropAtom (Term.prodF f g)
  | sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsDrop f → IsDrop g → IsDropAtom (Term.sumF f g)
  | listF {A B : Ty} {f : Term A B} : IsDrop f → IsDropAtom (Term.listF f)
  | id (A : Ty) : IsDropAtom (Term.id A)
  | bangV (A : Ty) {B : Ty} (v : Value B) : IsDropAtom (Term.toUnit A ⨟ v)
  | assocL (A B C : Ty) : IsDropAtom (Term.assocL A B C)
  | assocR (A B C : Ty) : IsDropAtom (Term.assocR A B C)
  | fst (A B : Ty) : IsDropAtom (Term.fst A B)
  | snd (A B : Ty) : IsDropAtom (Term.snd A B)
  | inl (A B : Ty) : IsDropAtom (Term.inl A B)
  | inr (A B : Ty) : IsDropAtom (Term.inr A B)
  | codiag (A : Ty) : IsDropAtom (Term.codiag A)
  | pureT (A : Ty) : IsDropAtom (Term.pureT A)
  | binconcat (A : Ty) : IsDropAtom (Term.binconcat A)
  | concat (A : Ty) : IsDropAtom (Term.concat A)
  | unshift (A B : Ty) : IsDropAtom (Term.unshift A B)

/-- **The spine of a drop.**  Every drop is either provably equal to an atom of at most its
rank, or provably equal to a drop followed by an atom, the two factors together having at
most its rank; in particular the first factor has strictly smaller rank.

(A drop whose domain is the unit type is a value, hence the prime drop `1 ; v`, which is why
the first case is stated up to provable equality.) -/
theorem IsDrop.spine : {A B : Ty} → {f : Term A B} → IsDrop f →
    (∃ f' : Term A B, IsDropAtom f' ∧ rank f' ≤ rank f ∧ f ≡ₜ f') ∨
    ∃ (C : Ty) (f₁ : Term A C) (f₂ : Term C B),
      IsDrop f₁ ∧ IsDropAtom f₂ ∧ rank f₁ + rank f₂ + 1 ≤ rank f ∧ f ≡ₜ (f₁ ⨟ f₂) := by
  intro A B f hf
  induction hf with
  | @comp A B C f g hf hg ihf ihg =>
      by_cases hB : B = Ty.unit
      · subst hB
        refine Or.inl ⟨Term.toUnit A ⨟ g, IsDropAtom.bangV A g, by simp [rank_const], ?_⟩
        exact PEq.compL _ (PEq.unit_unique f (Term.toUnit A))
      · have hrc : rank (f ⨟ g) = rank f + rank g + 1 := rank_comp_of_ne f g hB
        rcases ihg with ⟨g', hatom, hle, heg⟩ | ⟨D, g₁, g₂, hg₁, hg₂, hrank, heq⟩
        · exact Or.inr ⟨B, f, g', hf, hatom, by omega, PEq.compR _ heg⟩
        · refine Or.inr ⟨D, f ⨟ g₁, g₂, IsDrop.comp hf hg₁, hg₂, ?_, ?_⟩
          · have := rank_comp_le f g₁
            omega
          · calc (f ⨟ g) ≡ₜ (f ⨟ (g₁ ⨟ g₂)) := PEq.compR _ heq
              _ ≡ₜ ((f ⨟ g₁) ⨟ g₂) := PEq.symm (PEq.comp_assoc _ _ _)
  | prodF hf hg _ _ => exact Or.inl ⟨_, IsDropAtom.prodF hf hg, le_rfl, PEq.refl _⟩
  | sumF hf hg _ _ => exact Or.inl ⟨_, IsDropAtom.sumF hf hg, le_rfl, PEq.refl _⟩
  | listF hf _ => exact Or.inl ⟨_, IsDropAtom.listF hf, le_rfl, PEq.refl _⟩
  | id A => exact Or.inl ⟨_, IsDropAtom.id A, le_rfl, PEq.refl _⟩
  | bangV A v => exact Or.inl ⟨_, IsDropAtom.bangV A v, le_rfl, PEq.refl _⟩
  | assocL A B C => exact Or.inl ⟨_, IsDropAtom.assocL A B C, le_rfl, PEq.refl _⟩
  | assocR A B C => exact Or.inl ⟨_, IsDropAtom.assocR A B C, le_rfl, PEq.refl _⟩
  | fst A B => exact Or.inl ⟨_, IsDropAtom.fst A B, le_rfl, PEq.refl _⟩
  | snd A B => exact Or.inl ⟨_, IsDropAtom.snd A B, le_rfl, PEq.refl _⟩
  | inl A B => exact Or.inl ⟨_, IsDropAtom.inl A B, le_rfl, PEq.refl _⟩
  | inr A B => exact Or.inl ⟨_, IsDropAtom.inr A B, le_rfl, PEq.refl _⟩
  | codiag A => exact Or.inl ⟨_, IsDropAtom.codiag A, le_rfl, PEq.refl _⟩
  | pureT A => exact Or.inl ⟨_, IsDropAtom.pureT A, le_rfl, PEq.refl _⟩
  | binconcat A => exact Or.inl ⟨_, IsDropAtom.binconcat A, le_rfl, PEq.refl _⟩
  | concat A => exact Or.inl ⟨_, IsDropAtom.concat A, le_rfl, PEq.refl _⟩
  | unshift A B => exact Or.inl ⟨_, IsDropAtom.unshift A B, le_rfl, PEq.refl _⟩

/-! ### Two more coherence laws

The mirror images of `Lax149335Proofs.Term.distL_fst` and `Lax149335Proofs.Term.fst_prodF_assocR`, which
are needed for the cases of the induction that involve the second projection. -/

namespace Term

/-- The `distR`-`snd` coherence law, mirroring `Lax149335Proofs.Term.distL_fst`. -/
theorem distR_snd (A B C : Ty) :
    (distR A B C ⨟ sumF (snd A B) (snd A C)) ≡ₜ snd A (B ⊕' C) := by
  have key : (undistR A B C ⨟ snd A (B ⊕' C)) ≡ₜ sumF (snd A B) (snd A C) := by
    calc (either (prodF (Term.id A) (inl B C)) (prodF (Term.id A) (inr B C)) ⨟
            snd A (B ⊕' C))
        ≡ₜ either (prodF (Term.id A) (inl B C) ⨟ snd A (B ⊕' C))
            (prodF (Term.id A) (inr B C) ⨟ snd A (B ⊕' C)) := either_comp _ _ _
      _ ≡ₜ either (snd A B ⨟ inl B C) (snd A C ⨟ inr B C) :=
          either_congr (PEq.nat_snd _ _) (PEq.nat_snd _ _)
      _ ≡ₜ (sumF (snd A B) (snd A C) ⨟ either (inl B C) (inr B C)) :=
          PEq.symm (sumF_either _ _ _ _)
      _ ≡ₜ (sumF (snd A B) (snd A C) ⨟ Term.id (B ⊕' C)) :=
          PEq.compR _ (either_inl_inr B C)
      _ ≡ₜ sumF (snd A B) (snd A C) := PEq.comp_id _
  calc (distR A B C ⨟ sumF (snd A B) (snd A C))
      ≡ₜ (distR A B C ⨟ (undistR A B C ⨟ snd A (B ⊕' C))) := PEq.compR _ (PEq.symm key)
    _ ≡ₜ ((distR A B C ⨟ undistR A B C) ⨟ snd A (B ⊕' C)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (A ⊗ (B ⊕' C)) ⨟ snd A (B ⊕' C)) := PEq.compL _ (PEq.distR_undistR A B C)
    _ ≡ₜ snd A (B ⊕' C) := PEq.id_comp _

/-- Coherence between the second projection, the associator and the product combinator,
mirroring `Lax149335Proofs.Term.fst_prodF_assocR`. -/
theorem snd_prodF_assocL {A B B' C C' : Ty} (f : Term B B') (g : Term C C') :
    (snd A (B ⊗ C) ⨟ prodF f g) ≡ₜ (assocL A B C ⨟ prodF (snd A B ⨟ f) g) := by
  have key : (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ prodF f g)) ≡ₜ prodF (snd A B ⨟ f) g := by
    calc (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ prodF f g))
        ≡ₜ ((assocR A B C ⨟ snd A (B ⊗ C)) ⨟ prodF f g) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (snd A B) (Term.id C) ⨟ prodF f g) := PEq.compL _ (Term.assocR_snd A B C)
      _ ≡ₜ prodF (snd A B ⨟ f) (Term.id C ⨟ g) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (snd A B ⨟ f) g := PEq.congr_prodF (PEq.refl _) (PEq.id_comp _)
  calc (snd A (B ⊗ C) ⨟ prodF f g)
      ≡ₜ (Term.id (A ⊗ (B ⊗ C)) ⨟ (snd A (B ⊗ C) ⨟ prodF f g)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocL A B C ⨟ assocR A B C) ⨟ (snd A (B ⊗ C) ⨟ prodF f g)) :=
        PEq.compL _ (PEq.symm (PEq.assocL_assocR A B C))
    _ ≡ₜ (assocL A B C ⨟ (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ prodF f g))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL A B C ⨟ prodF (snd A B ⨟ f) g) := PEq.compR _ key

end Term

/-! ### Normalisation up to a lift -/

/-- A drop with co-product codomain is *sum-normalisable with bound `r`* if it is provably
equal to a lift followed by a case tree in normal form all of whose components are drops of
rank at most `r`. -/
def NormSum (r : ℕ) {A B₁ B₂ : Ty} (f : Term A (B₁ ⊕' B₂)) : Prop :=
  ∃ (D : Ty) (alpha : Term A D) (N : Term D (B₁ ⊕' B₂)),
    IsLift alpha ∧ IsNormalSumTree r N ∧ f ≡ₜ (alpha ⨟ N)

/-- A drop with product codomain is *product-normalisable with bound `r`* if it is provably
equal to a lift followed by an `n`-ary co-pairing of products of drops of rank at most
`r`. -/
def NormProd (r : ℕ) {A B₁ B₂ : Ty} (f : Term A (B₁ ⊗ B₂)) : Prop :=
  ∃ (D : Ty) (alpha : Term A D) (N : Term D (B₁ ⊗ B₂)),
    IsLift alpha ∧ IsNormalProdLe r N ∧ f ≡ₜ (alpha ⨟ N)

theorem NormSum.mono {r r' : ℕ} (h : r ≤ r') {A B₁ B₂ : Ty} {f : Term A (B₁ ⊕' B₂)} :
    NormSum r f → NormSum r' f := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, a, N, ha, hN.mono h, he⟩

theorem NormProd.mono {r r' : ℕ} (h : r ≤ r') {A B₁ B₂ : Ty} {f : Term A (B₁ ⊗ B₂)} :
    NormProd r f → NormProd r' f := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, a, N, ha, hN.mono h, he⟩

theorem NormSum.of_eq {r : ℕ} {A B₁ B₂ : Ty} {f g : Term A (B₁ ⊕' B₂)} (h : f ≡ₜ g) :
    NormSum r g → NormSum r f := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, a, N, ha, hN, h.trans he⟩

theorem NormProd.of_eq {r : ℕ} {A B₁ B₂ : Ty} {f g : Term A (B₁ ⊗ B₂)} (h : f ≡ₜ g) :
    NormProd r g → NormProd r f := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, a, N, ha, hN, h.trans he⟩

theorem NormSum.tree {r : ℕ} {A B₁ B₂ : Ty} {N : Term A (B₁ ⊕' B₂)}
    (hN : IsNormalSumTree r N) : NormSum r N :=
  ⟨A, Term.id A, N, IsLift.id A, hN, PEq.symm (PEq.id_comp _)⟩

theorem NormProd.tree {r : ℕ} {A B₁ B₂ : Ty} {N : Term A (B₁ ⊗ B₂)}
    (hN : IsNormalProdLe r N) : NormProd r N :=
  ⟨A, Term.id A, N, IsLift.id A, hN, PEq.symm (PEq.id_comp _)⟩

theorem NormSum.lift_comp {r : ℕ} {A E B₁ B₂ : Ty} {beta : Term A E} (hb : IsLift beta)
    {g : Term E (B₁ ⊕' B₂)} : NormSum r g → NormSum r (beta ⨟ g) := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, beta ⨟ a, N, IsLift.comp hb ha, hN,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem NormProd.lift_comp {r : ℕ} {A E B₁ B₂ : Ty} {beta : Term A E} (hb : IsLift beta)
    {g : Term E (B₁ ⊗ B₂)} : NormProd r g → NormProd r (beta ⨟ g) := by
  rintro ⟨D, a, N, ha, hN, he⟩
  exact ⟨D, beta ⨟ a, N, IsLift.comp hb ha, hN,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem NormSum.either {r : ℕ} {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊕' B₂)}
    {f₂ : Term A₂ (B₁ ⊕' B₂)} : NormSum r f₁ → NormSum r f₂ →
    NormSum r (Term.either f₁ f₂) := by
  rintro ⟨D₁, a₁, N₁, ha₁, hN₁, he₁⟩ ⟨D₂, a₂, N₂, ha₂, hN₂, he₂⟩
  refine ⟨D₁ ⊕' D₂, Term.sumF a₁ a₂, Term.either N₁ N₂, IsLift.sumF ha₁ ha₂,
    IsNormalSumTree.either hN₁ hN₂, ?_⟩
  calc Term.either f₁ f₂ ≡ₜ Term.either (a₁ ⨟ N₁) (a₂ ⨟ N₂) := either_congr he₁ he₂
    _ ≡ₜ (Term.sumF a₁ a₂ ⨟ Term.either N₁ N₂) := PEq.symm (sumF_either _ _ _ _)

theorem NormProd.either {r : ℕ} {A₁ A₂ B₁ B₂ : Ty} {f₁ : Term A₁ (B₁ ⊗ B₂)}
    {f₂ : Term A₂ (B₁ ⊗ B₂)} : NormProd r f₁ → NormProd r f₂ →
    NormProd r (Term.either f₁ f₂) := by
  rintro ⟨D₁, a₁, N₁, ha₁, hN₁, he₁⟩ ⟨D₂, a₂, N₂, ha₂, hN₂, he₂⟩
  refine ⟨D₁ ⊕' D₂, Term.sumF a₁ a₂, Term.either N₁ N₂, IsLift.sumF ha₁ ha₂,
    IsNormalProdLe.either hN₁ hN₂, ?_⟩
  calc Term.either f₁ f₂ ≡ₜ Term.either (a₁ ⨟ N₁) (a₂ ⨟ N₂) := either_congr he₁ he₂
    _ ≡ₜ (Term.sumF a₁ a₂ ⨟ Term.either N₁ N₂) := PEq.symm (sumF_either _ _ _ _)

/-! ### Co-pairing trees -/

/-- An `n`-ary co-pairing whose leaves are drops of rank at most `r` (up to provable
equality).  This is the shape that a case tree in normal form takes after it is composed with
the co-diagonal. -/
inductive CopairTree (r : ℕ) : {A B : Ty} → Term A B → Prop
  /-- A leaf: a term provably equal to a drop of rank at most `r`. -/
  | leaf {A B : Ty} {f g : Term A B} : IsDrop f → rank f ≤ r → g ≡ₜ f → CopairTree r g
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ B : Ty} {f₁ : Term A₁ B} {f₂ : Term A₂ B} {g : Term (A₁ ⊕' A₂) B} :
      CopairTree r f₁ → CopairTree r f₂ → g ≡ₜ Term.either f₁ f₂ → CopairTree r g

/-- The hypothesis of the sum normalisation lemma, up to rank `m`. -/
def SumNormalisable (m : ℕ) : Prop :=
  ∀ {A B₁ B₂ : Ty} (f : Term A (B₁ ⊕' B₂)), IsDrop f → rank f ≤ m → NormSum (rank f) f

/-- The hypothesis of the product normalisation lemma, up to rank `m`. -/
def ProdNormalisable (m : ℕ) : Prop :=
  ∀ {A B₁ B₂ : Ty} (f : Term A (B₁ ⊗ B₂)), IsDrop f → rank f ≤ m → NormProd (rank f) f

/-- A co-pairing tree with co-product codomain is sum-normalisable, provided its leaves
are. -/
theorem CopairTree.normSum {r m : ℕ} (hS : SumNormalisable m) (hm : r ≤ m) :
    {A B₁ B₂ : Ty} → {f : Term A (B₁ ⊕' B₂)} → CopairTree r f → NormSum r f
  | _, _, _, _, .leaf hd hr he => NormSum.of_eq he ((hS _ hd (hr.trans hm)).mono hr)
  | _, _, _, _, .either t₁ t₂ he =>
      NormSum.of_eq he (NormSum.either (t₁.normSum hS hm) (t₂.normSum hS hm))

/-- A co-pairing tree with product codomain is product-normalisable, provided its leaves
are. -/
theorem CopairTree.normProd {r m : ℕ} (hP : ProdNormalisable m) (hm : r ≤ m) :
    {A B₁ B₂ : Ty} → {f : Term A (B₁ ⊗ B₂)} → CopairTree r f → NormProd r f
  | _, _, _, _, .leaf hd hr he => NormProd.of_eq he ((hP _ hd (hr.trans hm)).mono hr)
  | _, _, _, _, .either t₁ t₂ he =>
      NormProd.of_eq he (NormProd.either (t₁.normProd hP hm) (t₂.normProd hP hm))
end Lax149335Proofs

bridge_export Lax149335Proofs
