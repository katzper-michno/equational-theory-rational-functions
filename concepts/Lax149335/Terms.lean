import Lax149335.Types
import Mathlib.Algebra.Group.Defs

/-!
---
title: Rational terms
type: definition
---
**Definition 3.1 (Rational terms).** A *rational term* $f : A \to B$ between types is an
expression built from the following atomic functions (Figure 1) using composition
$f \mathbin{;} g$ and the functoriality combinators $f \times g$, $f + g$ and $f^*$ of
products, co-products and lists:

1. the identity $A \to A$;
2. the co-projections $\mathsf{Left} : A \to A + B$ and $\mathsf{Right} : B \to A + B$;
3. the co-diagonal $A + A \to A$;
4. the projections $\mathsf{fst} : A \times B \to A$ and $\mathsf{snd} : A \times B \to B$;
5. the units $A \to A \times 1$ and $A \to 1 \times A$, and associativity of products in
   both directions;
6. distributivity $A \times (B + C) \to A \times B + A \times C$ and
   $(A + B) \times C \to A \times C + B \times C$;
7. the list constructors and destructors $\mathsf{cons} : 1 + A \times A^* \to A^*$,
   $\mathsf{uncons}$, $\mathsf{snoc} : 1 + A^* \times A \to A^*$ and $\mathsf{unsnoc}$;
8. list concatenation $\mathsf{concat} : A^{**} \to A^*$;
9. $\mathsf{block} : (A + B)^* \to A^* \times (B \times A^*)^*$, which cuts a list before
   every element of $B$;
10. bracket shifting $\mathsf{shiftR} : (A \times B)^* \times A \to A \times (B \times A)^*$
    and its inverse $\mathsf{shiftL}$;
11. prefix multiplication $\mathsf{pref} : (A \times G)^* \to (A \times G)^*$ for a finite
    group $G$, which replaces the $i$-th group element by the product of the first $i$ ones.

The *denotation* $[\![ f ]\!]$ of a rational term is the function it defines. A rational
term is *aperiodic* if it does not use prefix multiplication.

# Formalization notes

A finite group is given by a group structure on a finite alphabet $\overline{n+1}$, which is
no loss of generality since every finite group is isomorphic to one of these.
-/

namespace Lax149335.Terms

open Lax149335.Types

/-- Auxiliary function used for the denotation of the group prefix multiplication: the `i`-th
group element of the output is the product of the first `i` group elements of the input. -/
def prefixMul {α G : Type} [Mul G] : G → List (α × G) → List (α × G)
  | _, [] => []
  | acc, (a, g) :: t => (a, acc * g) :: prefixMul (acc * g) t

/-- Auxiliary function used for the denotation of `block`: a list over `A + B` is split into a
maximal prefix of elements of `A`, followed by a list of blocks, each consisting of one
element of `B` and the following maximal run of elements of `A`. -/
def blockDen {α β : Type} : List (α ⊕ β) → List α × List (β × List α)
  | [] => ([], [])
  | .inl a :: t => let p := blockDen t; (a :: p.1, p.2)
  | .inr b :: t => let p := blockDen t; ([], (b, p.1) :: p.2)

/-- Auxiliary function used for the denotation of `snoc`. -/
def snocDen {α : Type} : Unit ⊕ (List α × α) → List α
  | .inl _ => []
  | .inr (l, a) => l ++ [a]

/-- Auxiliary function used for the denotation of `unsnoc`. -/
def unsnocDen {α : Type} (l : List α) : Unit ⊕ (List α × α) :=
  match l.reverse with
  | [] => .inl ()
  | a :: t => .inr (t.reverse, a)

/-- Auxiliary function used for the denotation of `shiftR`. -/
def shiftRDen {α β : Type} : List (α × β) → α → α × List (β × α)
  | [], a => (a, [])
  | (a₁, b₁) :: t, a => let p := shiftRDen t a; (a₁, (b₁, p.1) :: p.2)

/-- Auxiliary function used for the denotation of `shiftL`. -/
def shiftLDen {α β : Type} (a : α) : List (β × α) → List (α × β) × α
  | [] => ([], a)
  | (b₁, a₂) :: t => let p := shiftLDen a₂ t; ((a, b₁) :: p.1, p.2)

/-- **Definition 3.1 (Rational terms).** The expressions built from the atomic functions of
Figure 1 by composition and the functoriality combinators of products, co-products and
lists. -/
inductive Term : Ty → Ty → Type
  /-- Composition of functions. -/
  | comp {A B C : Ty} : Term A B → Term B C → Term A C
  /-- Functoriality of the product type constructor. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} : Term A₁ B₁ → Term A₂ B₂ → Term (A₁ ⊗ A₂) (B₁ ⊗ B₂)
  /-- Functoriality of the co-product type constructor. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} : Term A₁ B₁ → Term A₂ B₂ → Term (A₁ ⊕' A₂) (B₁ ⊕' B₂)
  /-- Functoriality of the list type constructor. -/
  | listF {A B : Ty} : Term A B → Term A⋆ B⋆
  /-- Atomic function 1: the identity. -/
  | id (A : Ty) : Term A A
  /-- Atomic function 2: the left co-projection. -/
  | inl (A B : Ty) : Term A (A ⊕' B)
  /-- Atomic function 2: the right co-projection. -/
  | inr (A B : Ty) : Term B (A ⊕' B)
  /-- Atomic function 3: the co-diagonal. -/
  | codiag (A : Ty) : Term (A ⊕' A) A
  /-- Atomic function 4: the first projection. -/
  | fst (A B : Ty) : Term (A ⊗ B) A
  /-- Atomic function 4: the second projection. -/
  | snd (A B : Ty) : Term (A ⊗ B) B
  /-- Atomic function 5: the right unit `(id, 1)`. -/
  | unitR (A : Ty) : Term A (A ⊗ Ty.unit)
  /-- Atomic function 5: the left unit `(1, id)`. -/
  | unitL (A : Ty) : Term A (Ty.unit ⊗ A)
  /-- Atomic function 5: left associativity of products. -/
  | assocL (A B C : Ty) : Term (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
  /-- Atomic function 5: right associativity of products. -/
  | assocR (A B C : Ty) : Term ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  /-- Atomic function 6: distributivity on the right. -/
  | distR (A B C : Ty) : Term (A ⊗ (B ⊕' C)) ((A ⊗ B) ⊕' (A ⊗ C))
  /-- Atomic function 6: distributivity on the left. -/
  | distL (A B C : Ty) : Term ((A ⊕' B) ⊗ C) ((A ⊗ C) ⊕' (B ⊗ C))
  /-- Atomic function 7: the list constructor `cons`. -/
  | cons (A : Ty) : Term (Ty.unit ⊕' (A ⊗ A⋆)) A⋆
  /-- Atomic function 7: the list destructor `uncons`. -/
  | uncons (A : Ty) : Term A⋆ (Ty.unit ⊕' (A ⊗ A⋆))
  /-- Atomic function 7: the list constructor `snoc`. -/
  | snoc (A : Ty) : Term (Ty.unit ⊕' (A⋆ ⊗ A)) A⋆
  /-- Atomic function 7: the list destructor `unsnoc`. -/
  | unsnoc (A : Ty) : Term A⋆ (Ty.unit ⊕' (A⋆ ⊗ A))
  /-- Atomic function 8: concatenation of a list of lists. -/
  | concat (A : Ty) : Term A⋆⋆ A⋆
  /-- Atomic function 9: cutting a list over a co-product into blocks. -/
  | block (A B : Ty) : Term (A ⊕' B)⋆ (A⋆ ⊗ (B ⊗ A⋆)⋆)
  /-- Atomic function 10: shifting brackets to the right. -/
  | shiftR (A B : Ty) : Term ((A ⊗ B)⋆ ⊗ A) (A ⊗ (B ⊗ A)⋆)
  /-- Atomic function 10: shifting brackets to the left. -/
  | shiftL (A B : Ty) : Term (A ⊗ (B ⊗ A)⋆) ((A ⊗ B)⋆ ⊗ A)
  /-- Atomic function 11: prefix multiplication in a finite group whose underlying set is the
  finite alphabet `1 + ⋯ + 1`. -/
  | pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      Term ((A ⊗ Ty.finAlph n)⋆) ((A ⊗ Ty.finAlph n)⋆)

namespace Term

/-- Notation `f ⨟ g` for the composition of rational terms: first `f`, then `g`. -/
infixl:60 " ⨟ " => Term.comp

/-- The denotation `⟦f⟧` of a rational term: the function that it defines. -/
def den : {A B : Ty} → Term A B → ⟦A⟧ → ⟦B⟧
  | _, _, .comp f g, x => den g (den f x)
  | _, _, .prodF f g, x => (den f x.1, den g x.2)
  | _, _, .sumF f g, x =>
      match x with
      | .inl a => .inl (den f a)
      | .inr b => .inr (den g b)
  | _, _, .listF f, l => l.map (den f)
  | _, _, .id _, x => x
  | _, _, .inl _ _, x => .inl x
  | _, _, .inr _ _, x => .inr x
  | _, _, .codiag _, x => match x with | .inl a => a | .inr a => a
  | _, _, .fst _ _, x => x.1
  | _, _, .snd _ _, x => x.2
  | _, _, .unitR _, x => (x, ())
  | _, _, .unitL _, x => ((), x)
  | _, _, .assocL _ _ _, x => ((x.1, x.2.1), x.2.2)
  | _, _, .assocR _ _ _, x => (x.1.1, (x.1.2, x.2))
  | _, _, .distR _ _ _, x =>
      match x with
      | (a, .inl b) => .inl (a, b)
      | (a, .inr c) => .inr (a, c)
  | _, _, .distL _ _ _, x =>
      match x with
      | (.inl a, c) => .inl (a, c)
      | (.inr b, c) => .inr (b, c)
  | _, _, .cons _, x => match x with | .inl _ => [] | .inr (a, l) => a :: l
  | _, _, .uncons _, l => match l with | [] => .inl () | a :: t => .inr (a, t)
  | _, _, .snoc _, x => snocDen x
  | _, _, .unsnoc _, l => unsnocDen l
  | _, _, .concat _, l => l.flatten
  | _, _, .block _ _, l => blockDen l
  | _, _, .shiftR _ _, x => match x with | (l, a) => shiftRDen l a
  | _, _, .shiftL _ _, x => match x with | (a, l) => shiftLDen a l
  | _, _, .pref _ G, l => letI := G; prefixMul (1 : ⟦Ty.finAlph _⟧) l

/-- Whether a rational term uses the atomic function `pref` for prefix multiplication in
groups. -/
def usesPref : {A B : Ty} → Term A B → Bool
  | _, _, .comp f g => usesPref f || usesPref g
  | _, _, .prodF f g => usesPref f || usesPref g
  | _, _, .sumF f g => usesPref f || usesPref g
  | _, _, .listF f => usesPref f
  | _, _, .pref _ _ => true
  | _, _, _ => false

end Term

/-- A rational term is aperiodic if it does not use the group prefix multiplication `pref`. -/
def IsAperiodic {A B : Ty} (f : Term A B) : Prop := Term.usesPref f = false

end Lax149335.Terms
