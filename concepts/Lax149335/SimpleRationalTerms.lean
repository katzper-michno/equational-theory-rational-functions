import Lax149335.EquationalTheory

/-!
---
title: Simple rational terms and conjugacy
type: definition
---
The definition of simple rational terms (Definition 2.5) is meaningful in the compositional
syntax of Section 3: the *simple rational terms* with outputs in $B^*$ are the rational terms
built from the empty list $[\,] : 1 \to B^*$ using co-pairing $\langle f_1, f_2 \rangle$,
concatenation $f_1 \odot f_2$, the homomorphism combinator $\mathrm{hom}\, f$, and
prepending and appending a value, $w \cdot f$ and $f \cdot w$, where $w : 1 \to B^*$.

For two rational terms $f, g : A \to B^*$ and a value $w : 1 \to B^*$, Section 6 considers
three conjugacy relations, in increasing order of strength:

1. $f$ and $g$ are *denotationally $w$-conjugate* if
   $[\![ f \cdot w ]\!] = [\![ w \cdot g ]\!]$;
2. $f$ and $g$ are *provably $w$-conjugate* if $f \cdot w \equiv w \cdot g$;
3. $f$ and $g$ are *syntactically $w$-conjugate* if $f = w \cdot h$ and $g = h \cdot w$ for
   some term $h$.

The *length* of a list value $w$ is the length of the list it produces.
-/

namespace Lax149335.SimpleRationalTerms

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory

/-- Simple rational terms with outputs in `B*`, in the syntax of rational terms. -/
inductive IsSimple (B : Ty) : {A : Ty} → Term A B⋆ → Prop
  /-- The empty function `[] : 1 → B*`. -/
  | nil : IsSimple B (nilT B)
  /-- Co-pairing. -/
  | either {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆} :
      IsSimple B f₁ → IsSimple B f₂ → IsSimple B (Term.either f₁ f₂)
  /-- Concatenation of two functions. -/
  | fdot {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆} :
      IsSimple B f₁ → IsSimple B f₂ → IsSimple B (f₁ ⊙ f₂)
  /-- The homomorphism combinator. -/
  | hom {A : Ty} {f : Term A B⋆} : IsSimple B f → IsSimple B (homT f)
  /-- Prepending a value. -/
  | dotL {A : Ty} {f : Term A B⋆} (w : Value B⋆) : IsSimple B f → IsSimple B (Term.dotL w f)
  /-- Appending a value. -/
  | dotR {A : Ty} {f : Term A B⋆} (w : Value B⋆) : IsSimple B f → IsSimple B (Term.dotR f w)

/-- The length of a list value. -/
def valLength {B : Ty} (w : Value B⋆) : ℕ := List.length (w.den ())

/-- `f` and `g` are denotationally `w`-conjugate: `⟦f · w⟧ = ⟦w · g⟧`. -/
def DenConjugate {A B : Ty} (w : Value B⋆) (f g : Term A B⋆) : Prop :=
  (dotR f w).den = (dotL w g).den

/-- `f` and `g` are provably `w`-conjugate: `f · w ≡ w · g`. -/
def ProvConjugate {A B : Ty} (w : Value B⋆) (f g : Term A B⋆) : Prop :=
  dotR f w ≡ₜ dotL w g

/-- `f` and `g` are syntactically `w`-conjugate: `f = w · h` and `g = h · w` for some `h`. -/
def SynConjugate {A B : Ty} (w : Value B⋆) (f g : Term A B⋆) : Prop :=
  ∃ h : Term A B⋆, f = dotL w h ∧ g = dotR h w

end Lax149335.SimpleRationalTerms
