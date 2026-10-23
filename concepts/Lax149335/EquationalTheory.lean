import Lax149335.DerivedTerms

/-!
---
title: The equational theory
type: definition
---
Section 4 introduces an equivalence relation $f \equiv g$ on rational terms of the same type,
called *provable equivalence*. It is the least equivalence relation on rational terms that
contains the following sixteen axioms and is preserved by the four combinators of
Definition 3.1 (composition and functoriality of products, co-products and lists).

1. *Category axioms:* composition is associative and the identity is neutral.
2. *Functoriality:* the combinators $\times$, $+$ and $(-)^*$ preserve identities and
   composition.
3. *Naturality:* every atomic function except prefix multiplication is a natural
   transformation.
4. *Isomorphisms:* ten pairs of mutually inverse terms — the units and $\mathsf{fst}$,
   $\mathsf{snd}$; $\mathsf{assocL}$ and $\mathsf{assocR}$; $\mathsf{distL}$ and
   $\mathsf{undistL}$; $\mathsf{distR}$ and $\mathsf{undistR}$; $\mathsf{cons}$ and
   $\mathsf{uncons}$; $\mathsf{snoc}$ and $\mathsf{unsnoc}$; $\mathsf{split}$ and
   $\mathsf{unsplit}$; $\mathsf{pref}$ and $\mathsf{unpref}$; $\mathsf{shiftL}$ and
   $\mathsf{shiftR}$.
5. The unit type is terminal: any two terms $A \to 1$ are equivalent.
6. *The co-diagonal:* $\mathsf{Left} \mathbin{;} \mathsf{codiag} \equiv \mathrm{id}$,
   $\mathsf{Right} \mathbin{;} \mathsf{codiag} \equiv \mathrm{id}$ and
   $(\mathsf{Left} + \mathsf{Right}) \mathbin{;} \mathsf{codiag} \equiv \mathrm{id}$.
7. Mac Lane's pentagon for $\mathsf{assocL}$.
8. Mac Lane's triangle for $\mathsf{assocL}$ and the unit.
9. The notation based on $\mathsf{snoc}$ agrees with the notation based on
   $\mathsf{cons}$: for the empty list, for singleton lists, and for concatenation.
10. $A^*$ is a monoid under $\mathsf{binconcat}$ with unit $[\,]$.
11. $\mathsf{concat}$ is a monoid homomorphism.
12. $A^*$ is a monad with unit $\mathsf{pure}$ and multiplication $\mathsf{concat}$.
13. $\mathsf{prepend}$ and $\mathsf{append}$ are expressed by $\mathsf{binconcat}$.
14. Concatenating a list of empty lists gives the empty list.
15. $\mathsf{shiftR}$ does not change the content of a list: it commutes with the
    concatenation maps into $(A + B)^*$.
16. *The window axiom:* the bundle term
    $\mathsf{bundle} : (2^*)^* \to (2^* \times 2^*)^* \times (1 + 2^*)$, which splits a
    list into consecutive pairs followed by a remainder of at most one element, is undone by
    the concatenation map: $\mathsf{bundle} \mathbin{;} \mathsf{concat} \equiv
    \mathrm{id}$. Here $2 = 1 + 1$.

The bundle term (Definition H.5) is, for a type $A$ and a value $w : 1 \to A$, the
composition
$$
((\mathrm{id}, 1) \mathbin{;} (\mathrm{id} \times \mathsf{Right}))^* \mathbin{;}
\mathsf{pref}_{\mathbb{Z}_2} \mathbin{;}
(\mathsf{distR} \mathbin{;} \langle \mathsf{fst} \mathbin{;} \mathsf{Right},
\mathsf{fst} \mathbin{;} \mathsf{Left} \rangle)^* \mathbin{;} \mathsf{split}
\mathbin{;} \mathsf{shiftL} \mathbin{;} ((\mathsf{head}_w \times \mathrm{id})^*
\times (\mathsf{uncons} \mathbin{;} (\mathrm{id} + \mathsf{fst}))),
$$
where $\mathbb{Z}_2$ is the cyclic group of order two on $2 = 1 + 1$, with identity
$\mathsf{Left}$. The window axiom uses it for $A = 2^*$ and $w = [\,]$.

# Formalization notes

Naturality of prefix multiplication is not an axiom: as observed in footnote 5 of the paper,
it is derivable. The axioms are listed in full in the constructors of `PEq` below.
-/

namespace Lax149335.EquationalTheory

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms

namespace Term

open Lax149335.Terms.Term Lax149335.DerivedTerms.Term

/-- The cyclic group `ℤ₂` of order two, with the two letter alphabet `2 = 1 + 1` as its
underlying set: the group identity is the first letter `Left`, and the second letter `Right`
is the generator. -/
def cyclicTwo : Group ⟦Ty.finAlph 1⟧ where
  mul x y := match x, y with
    | .inl _, y => y
    | x, .inl _ => x
    | .inr _, .inr _ => .inl ()
  one := .inl ()
  inv x := x
  mul_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  one_mul := by intro x; cases x <;> rfl
  mul_one := by intro x; cases x <;> rfl
  inv_mul_cancel := by intro x; cases x <;> rfl

/-- The generator `Right` of the cyclic group of order two. -/
def cyclicTwoGen : ⟦Ty.finAlph 1⟧ := Sum.inr ()

/-- **Step 3 of the bundle term**, for a single element: `distR ; either (fst ; Right)
(fst ; Left) : A × 2 → A + A`.  An element annotated with the generator `Right` goes to the
left copy of `A`, and an element annotated with the identity `Left` goes to the right
copy. -/
def bundleTag (A : Ty) : Term (A ⊗ Ty.finAlph 1) (A ⊕' A) :=
  distR A Ty.unit (Ty.finAlph 0) ⨟ either (fst A Ty.unit ⨟ inr A A) (fst A Ty.unit ⨟ inl A A)

/-- **Definition H.5 (the bundle term)** `A* → (A × A)* × (1 + A)`, for a type `A` and a value
`w : 1 → A`:

`((id,1) ; (id × Right))* ; pref_{ℤ₂} ; (distR ; either (fst ; Right) (fst ; Left))* ;
split ; shiftL ; ((head_w × id)* × (uncons ; (id + fst)))`.

The window axiom (Axiom 16) says that, for `A = 2*` and `w = []`, it is a one-sided inverse
of the concatenation map `(A × A)* × (1 + A) ↣ A*`. -/
def bundle (A : Ty) (w : Value A) : Term A⋆ ((A ⊗ A)⋆ ⊗ (Ty.unit ⊕' A)) :=
  listF (unitR A ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph 0))) ⨟
    pref A cyclicTwo ⨟
    listF (bundleTag A) ⨟
    split A A ⨟
    shiftL A⋆ A ⨟
    prodF (listF (prodF (headT w) (Term.id A))) (uncons A ⨟ sumF (Term.id Ty.unit) (fst A A⋆))

/-- The type constructor `A ↦ (A × A)* × (1 + A)` of the window axiom. -/
def TyF.window : TyF := .prod (.list (.prod .param .param)) (.sum .unit .param)

end Term

open Lax149335.Terms.Term Lax149335.DerivedTerms.Term

/-- Provable equality of rational terms: the least equivalence relation containing
Axioms 1-16 of Section 4 and stable under the combinators of the system. -/
inductive PEq : {A B : Ty} → Term A B → Term A B → Prop
  -- rules of equational reasoning: `≡` is an equivalence relation, stable under the
  -- four combinators of the system
  | refl {A B : Ty} (f : Term A B) : PEq f f
  | symm {A B : Ty} {f g : Term A B} : PEq f g → PEq g f
  | trans {A B : Ty} {f g h : Term A B} : PEq f g → PEq g h → PEq f h
  | congr_comp {A B C : Ty} {f f' : Term A B} {g g' : Term B C} :
      PEq f f' → PEq g g' → PEq (f ⨟ g) (f' ⨟ g')
  | congr_prodF {A₁ A₂ B₁ B₂ : Ty} {f f' : Term A₁ B₁} {g g' : Term A₂ B₂} :
      PEq f f' → PEq g g' → PEq (prodF f g) (prodF f' g')
  | congr_sumF {A₁ A₂ B₁ B₂ : Ty} {f f' : Term A₁ B₁} {g g' : Term A₂ B₂} :
      PEq f f' → PEq g g' → PEq (sumF f g) (sumF f' g')
  | congr_listF {A B : Ty} {f f' : Term A B} : PEq f f' → PEq (listF f) (listF f')
  -- ## Axiom 1 (category axioms)
  | comp_assoc {A B C D : Ty} (f : Term A B) (g : Term B C) (h : Term C D) :
      PEq ((f ⨟ g) ⨟ h) (f ⨟ (g ⨟ h))
  | id_comp {A B : Ty} (f : Term A B) : PEq (Term.id A ⨟ f) f
  | comp_id {A B : Ty} (f : Term A B) : PEq (f ⨟ Term.id B) f
  -- ## Axiom 2 (functoriality), first part: the functors preserve the identity
  | prod_id (A B : Ty) : PEq (prodF (Term.id A) (Term.id B)) (Term.id (A ⊗ B))
  | sum_id (A B : Ty) : PEq (sumF (Term.id A) (Term.id B)) (Term.id (A ⊕' B))
  | list_id (A : Ty) : PEq (listF (Term.id A)) (Term.id A⋆)
  -- ## Axiom 2 (functoriality), second part: the functors preserve composition
  | prod_comp {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} (f₁ : Term A₁ B₁) (f₂ : Term A₂ B₂)
      (g₁ : Term B₁ C₁) (g₂ : Term B₂ C₂) :
      PEq (prodF f₁ f₂ ⨟ prodF g₁ g₂) (prodF (f₁ ⨟ g₁) (f₂ ⨟ g₂))
  | sum_comp {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} (f₁ : Term A₁ B₁) (f₂ : Term A₂ B₂)
      (g₁ : Term B₁ C₁) (g₂ : Term B₂ C₂) :
      PEq (sumF f₁ f₂ ⨟ sumF g₁ g₂) (sumF (f₁ ⨟ g₁) (f₂ ⨟ g₂))
  | list_comp {A B C : Ty} (f : Term A B) (g : Term B C) :
      PEq (listF f ⨟ listF g) (listF (f ⨟ g))
  -- ## Axiom 3 (each atomic function is a natural transformation)
  | nat_inl {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (inl A B ⨟ sumF f g) (f ⨟ inl A' B')
  | nat_inr {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (inr A B ⨟ sumF f g) (g ⨟ inr A' B')
  | nat_codiag {A A' : Ty} (f : Term A A') :
      PEq (sumF f f ⨟ codiag A') (codiag A ⨟ f)
  | nat_fst {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f g ⨟ fst A' B') (fst A B ⨟ f)
  | nat_snd {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f g ⨟ snd A' B') (snd A B ⨟ g)
  | nat_unitR {A A' : Ty} (f : Term A A') :
      PEq (f ⨟ unitR A') (unitR A ⨟ prodF f (Term.id Ty.unit))
  | nat_unitL {A A' : Ty} (f : Term A A') :
      PEq (f ⨟ unitL A') (unitL A ⨟ prodF (Term.id Ty.unit) f)
  | nat_assocL {A A' B B' C C' : Ty} (f₁ : Term A A') (f₂ : Term B B') (f₃ : Term C C') :
      PEq (prodF f₁ (prodF f₂ f₃) ⨟ assocL A' B' C') (assocL A B C ⨟ prodF (prodF f₁ f₂) f₃)
  | nat_assocR {A A' B B' C C' : Ty} (f₁ : Term A A') (f₂ : Term B B') (f₃ : Term C C') :
      PEq (prodF (prodF f₁ f₂) f₃ ⨟ assocR A' B' C') (assocR A B C ⨟ prodF f₁ (prodF f₂ f₃))
  | nat_distR {A A' B B' C C' : Ty} (f : Term A A') (g : Term B B') (h : Term C C') :
      PEq (prodF f (sumF g h) ⨟ distR A' B' C') (distR A B C ⨟ sumF (prodF f g) (prodF f h))
  | nat_distL {A A' B B' C C' : Ty} (f : Term A A') (g : Term B B') (h : Term C C') :
      PEq (prodF (sumF f g) h ⨟ distL A' B' C') (distL A B C ⨟ sumF (prodF f h) (prodF g h))
  | nat_cons {A B : Ty} (f : Term A B) :
      PEq (sumF (Term.id Ty.unit) (prodF f (listF f)) ⨟ cons B) (cons A ⨟ listF f)
  | nat_uncons {A B : Ty} (f : Term A B) :
      PEq (listF f ⨟ uncons B) (uncons A ⨟ sumF (Term.id Ty.unit) (prodF f (listF f)))
  | nat_snoc {A B : Ty} (f : Term A B) :
      PEq (sumF (Term.id Ty.unit) (prodF (listF f) f) ⨟ snoc B) (snoc A ⨟ listF f)
  | nat_unsnoc {A B : Ty} (f : Term A B) :
      PEq (listF f ⨟ unsnoc B) (unsnoc A ⨟ sumF (Term.id Ty.unit) (prodF (listF f) f))
  | nat_concat {A B : Ty} (f : Term A B) :
      PEq (listF (listF f) ⨟ concat B) (concat A ⨟ listF f)
  | nat_split {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (listF (sumF f g) ⨟ split A' B')
        (split A B ⨟ prodF (listF f) (listF (prodF g (listF f))))
  | nat_shiftR {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF (listF (prodF f g)) f ⨟ shiftR A' B')
        (shiftR A B ⨟ prodF f (listF (prodF g f)))
  | nat_shiftL {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f (listF (prodF g f)) ⨟ shiftL A' B')
        (shiftL A B ⨟ prodF (listF (prodF f g)) f)
  -- (Naturality of the group prefix multiplication need not be postulated: it is derivable,
  -- see footnote 5 of the paper.)
  -- ## Axiom 4 (ten pairs of mutually inverse functions)
  | unitR_fst (A : Ty) : PEq (unitR A ⨟ fst A Ty.unit) (Term.id A)
  | fst_unitR (A : Ty) : PEq (fst A Ty.unit ⨟ unitR A) (Term.id (A ⊗ Ty.unit))
  | unitL_snd (A : Ty) : PEq (unitL A ⨟ snd Ty.unit A) (Term.id A)
  | snd_unitL (A : Ty) : PEq (snd Ty.unit A ⨟ unitL A) (Term.id (Ty.unit ⊗ A))
  | assocL_assocR (A B C : Ty) :
      PEq (assocL A B C ⨟ assocR A B C) (Term.id (A ⊗ (B ⊗ C)))
  | assocR_assocL (A B C : Ty) :
      PEq (assocR A B C ⨟ assocL A B C) (Term.id ((A ⊗ B) ⊗ C))
  | distL_undistL (A B C : Ty) :
      PEq (distL A B C ⨟ undistL A B C) (Term.id ((A ⊕' B) ⊗ C))
  | undistL_distL (A B C : Ty) :
      PEq (undistL A B C ⨟ distL A B C) (Term.id ((A ⊗ C) ⊕' (B ⊗ C)))
  | distR_undistR (A B C : Ty) :
      PEq (distR A B C ⨟ undistR A B C) (Term.id (A ⊗ (B ⊕' C)))
  | undistR_distR (A B C : Ty) :
      PEq (undistR A B C ⨟ distR A B C) (Term.id ((A ⊗ B) ⊕' (A ⊗ C)))
  | cons_uncons (A : Ty) : PEq (cons A ⨟ uncons A) (Term.id (Ty.unit ⊕' (A ⊗ A⋆)))
  | uncons_cons (A : Ty) : PEq (uncons A ⨟ cons A) (Term.id A⋆)
  | snoc_unsnoc (A : Ty) : PEq (snoc A ⨟ unsnoc A) (Term.id (Ty.unit ⊕' (A⋆ ⊗ A)))
  | unsnoc_snoc (A : Ty) : PEq (unsnoc A ⨟ snoc A) (Term.id A⋆)
  | split_unsplit (A B : Ty) : PEq (split A B ⨟ unsplit A B) (Term.id (A ⊕' B)⋆)
  | unsplit_split (A B : Ty) : PEq (unsplit A B ⨟ split A B) (Term.id (A⋆ ⊗ (B ⊗ A⋆)⋆))
  | pref_unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      PEq (pref A G ⨟ unpref A G) (Term.id ((A ⊗ Ty.finAlph n)⋆))
  | unpref_pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      PEq (unpref A G ⨟ pref A G) (Term.id ((A ⊗ Ty.finAlph n)⋆))
  | shiftL_shiftR (A B : Ty) : PEq (shiftL A B ⨟ shiftR A B) (Term.id (A ⊗ (B ⊗ A)⋆))
  | shiftR_shiftL (A B : Ty) : PEq (shiftR A B ⨟ shiftL A B) (Term.id ((A ⊗ B)⋆ ⊗ A))
  -- ## Axiom 5 (the unit type is terminal)
  | unit_unique {A : Ty} (f g : Term A Ty.unit) : PEq f g
  -- ## Axiom 6 (the co-diagonal)
  | inl_codiag (A : Ty) : PEq (inl A A ⨟ codiag A) (Term.id A)
  | inr_codiag (A : Ty) : PEq (inr A A ⨟ codiag A) (Term.id A)
  | sum_inl_inr_codiag (A B : Ty) :
      PEq (sumF (inl A B) (inr A B) ⨟ codiag (A ⊕' B)) (Term.id (A ⊕' B))
  -- ## Axiom 7 (Mac Lane's pentagon)
  | pentagon (A B C D : Ty) :
      PEq (prodF (Term.id A) (assocL B C D) ⨟ assocL A (B ⊗ C) D ⨟
              prodF (assocL A B C) (Term.id D))
        (assocL A B (C ⊗ D) ⨟ assocL (A ⊗ B) C D)
  -- ## Axiom 8 (Mac Lane's triangle)
  | triangle (A C : Ty) :
      PEq (assocL A Ty.unit C ⨟ prodF (fst A Ty.unit) (Term.id C))
        (prodF (Term.id A) (snd Ty.unit C))
  -- ## Axiom 9 (`snoc`-based notation agrees with `cons`-based notation)
  | inl_snoc_cons (A : Ty) :
      PEq (inl Ty.unit (A⋆ ⊗ A) ⨟ snoc A) (inl Ty.unit (A ⊗ A⋆) ⨟ cons A)
  | append_nil_prepend_nil (A : Ty) :
      PEq (unitL A ⨟ prodF (nilT A) (Term.id A) ⨟ append A)
        (unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A)
  | append_concat_prepend_concat (A : Ty) :
      PEq (prodF (pureT A⋆) (Term.id A⋆) ⨟ append A⋆ ⨟ concat A)
        (prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆ ⨟ concat A)
  -- ## Axiom 10 (`A*` is a monoid)
  | binconcat_assoc (A : Ty) :
      PEq (prodF (binconcat A) (Term.id A⋆) ⨟ binconcat A)
        (assocR A⋆ A⋆ A⋆ ⨟ prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A)
  | binconcat_unitR (A : Ty) :
      PEq (unitR A⋆ ⨟ prodF (Term.id A⋆) (nilT A) ⨟ binconcat A) (Term.id A⋆)
  | binconcat_unitL (A : Ty) :
      PEq (unitL A⋆ ⨟ prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) (Term.id A⋆)
  -- ## Axiom 11 (`concat` is a monoid homomorphism)
  | nil_concat (A : Ty) : PEq (nilT A⋆ ⨟ concat A) (nilT A)
  | binconcat_concat (A : Ty) :
      PEq (binconcat A⋆ ⨟ concat A) (prodF (concat A) (concat A) ⨟ binconcat A)
  -- ## Axiom 12 (`A*` is a monad)
  | concat_concat (A : Ty) : PEq (listF (concat A) ⨟ concat A) (concat A⋆ ⨟ concat A)
  | pure_concat (A : Ty) : PEq (pureT A⋆ ⨟ concat A) (Term.id A⋆)
  | listF_pure_concat (A : Ty) : PEq (listF (pureT A) ⨟ concat A) (Term.id A⋆)
  -- ## Axiom 13 (the inductive structure in terms of the monoid structure)
  | prepend_def (A : Ty) :
      PEq (prepend A) (prodF (pureT A) (Term.id A⋆) ⨟ binconcat A)
  | append_def (A : Ty) :
      PEq (append A) (prodF (Term.id A⋆) (pureT A) ⨟ binconcat A)
  -- ## Axiom 14 (concatenating a list of empty lists)
  | nil_map_concat (A : Ty) :
      PEq (listF (nilT A) ⨟ concat A) (toUnit Ty.unit⋆ ⨟ nilT A)
  -- ## Axiom 15 (`shiftR` does not change the content of the list)
  | shiftR_content (A B : Ty) :
      PEq (shiftR A B ⨟ TyF2.concatMap (.prod .p1 (.list (.prod .p2 .p1))) A B)
        (TyF2.concatMap (.prod (.list (.prod .p1 .p2)) .p1) A B)
  -- ## Axiom 16 (the window axiom: the bundle term undoes the concatenation map of bundles
  -- of size two over binary strings)
  --
  -- The bundle term `bundle_{2*} : (2*)* → (2* × 2*)* × (1 + 2*)` of Definition H.5,
  -- formalised as `Term.bundle` with the value `w = []`, splits a list into bundles
  -- of two consecutive entries followed by a remainder of at most one entry.  The axiom says
  -- that this splitting is undone by the concatenation map
  --
  --   `(2* × 2*)* × (1 + 2*) ↣ (2*)*`,
  --
  -- i.e. that `bundle ; concat ≡ id`.
  | window :
      PEq (Term.bundle ((Ty.finAlph 1)⋆) (nilT (Ty.finAlph 1)) ⨟
            TyF.concatMap Term.TyF.window ((Ty.finAlph 1)⋆))
        (Term.id (((Ty.finAlph 1)⋆)⋆))

/-- Notation `f ≡ₜ g` for provable equivalence of rational terms. -/
infix:50 " ≡ₜ " => PEq

end Lax149335.EquationalTheory
