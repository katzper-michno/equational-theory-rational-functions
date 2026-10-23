import Lax149335.Terms

/-!
---
title: Derived terms
type: definition
---
The following terms are derived from the atomic functions and combinators of
Definition 3.1. They are used to state the axioms of Section 4 and the results of the
completeness proof.

- The unique term $A \to 1$, co-pairing $\langle f_1, f_2 \rangle = (f_1 + f_2) \mathbin{;}
  \mathsf{codiag}$, commutativity and associativity of co-products.
- The list notation of Section 4.6: the empty list $[\,] : 1 \to A^*$, $\mathsf{prepend} :
  A \times A^* \to A^*$, $\mathsf{append} : A^* \times A \to A^*$, $\mathsf{pure} : A \to
  A^*$, $\mathsf{binconcat} : A^* \times A^* \to A^*$, the homomorphism combinator
  $\mathrm{hom}\, f = f^* \mathbin{;} \mathsf{concat}$, and the concatenation
  $f \odot g = (f \times g) \mathbin{;} \mathsf{binconcat}$ of two terms with list outputs.
- The inverses of distributivity, $\mathsf{undistL}$ and $\mathsf{undistR}$ (Section 4.4).
- **Definition 5.1 (Value).** A *value* is a term of type $1 \to A$. For a list value $w$,
  the terms $w \cdot f$ and $f \cdot w$ prepend or append the output of $w$ to the output
  of $f$ (Section 5.2), and $\mathsf{head}_w : A^* \to A$ returns the first element of a
  list, or the output of $w$ for the empty list.
- *Concatenation maps* (Section 5.1). For a type constructor $F$ with one parameter, built
  from the parameter, $1$, $\times$, $+$ and $(-)^*$, the concatenation map
  $F(A) \rightarrowtail A^*$ lists all the elements of $A$ occurring in the input, from left
  to right. Similarly for type constructors with two parameters, with outputs in
  $(A + B)^*$. In particular, $\mathsf{unsplit} : A^* \times (B \times A^*)^* \to
  (A + B)^*$ is a concatenation map.
- The terms $\mathsf{shift} : (A \times B)^* \to 1 + A \times (B \times A)^* \times B$ and
  $\mathsf{unshift}$ of Table 1.
- The inverse $\mathsf{unpref}$ of group prefix multiplication (Section 4.4), which maps
  $[(a_1, g_1), \ldots, (a_n, g_n)]$ to $[(a_1, g_0^{-1} g_1), \ldots, (a_n, g_{n-1}^{-1} g_n)]$,
  where $g_0$ is the group identity.

# Formalization notes

The paper only asserts that a term for $\mathsf{unpref}$ exists. Here it is defined
explicitly, following the appendix, by case analysis on the letters of the finite alphabet
that carries the group (`caseL`, `caseR`, `constFin`).
-/

namespace Lax149335.DerivedTerms

open Lax149335.Types Lax149335.Terms

namespace Term

open Lax149335.Terms.Term

/-- The unique function into the unit type, `A → 1`. -/
def toUnit (A : Ty) : Term A Ty.unit := unitL A ⨟ fst Ty.unit A

/-- Co-pairing, a derived combinator: `either f₁ f₂ = (f₁ + f₂); codiag`. -/
def either {A₁ A₂ B : Ty} (f₁ : Term A₁ B) (f₂ : Term A₂ B) : Term (A₁ ⊕' A₂) B :=
  sumF f₁ f₂ ⨟ codiag B

/-- Commutativity of the co-product, a derived term. -/
def comm (A B : Ty) : Term (A ⊕' B) (B ⊕' A) := either (inr B A) (inl B A)

/-- Associativity of the co-product, from left to right. -/
def sumAssocR (A B C : Ty) : Term ((A ⊕' B) ⊕' C) (A ⊕' (B ⊕' C)) :=
  either (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C))) (inr B C ⨟ inr A (B ⊕' C))

/-- Associativity of the co-product, from right to left. -/
def sumAssocL (A B C : Ty) : Term (A ⊕' (B ⊕' C)) ((A ⊕' B) ⊕' C) :=
  either (inl A B ⨟ inl (A ⊕' B) C)
    (either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C))

/-- The empty list `[] : 1 → A*`, defined as `Left; cons`. -/
def nilT (A : Ty) : Term Ty.unit A⋆ := inl Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `prepend : A × A* → A*`, defined as `Right; cons`. -/
def prepend (A : Ty) : Term (A ⊗ A⋆) A⋆ := inr Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `append : A* × A → A*`, defined as `Right; snoc`. -/
def append (A : Ty) : Term (A⋆ ⊗ A) A⋆ := inr Ty.unit (A⋆ ⊗ A) ⨟ snoc A

/-- `pure : A → A*`, defined as `(id,1); id × []; prepend`. -/
def pureT (A : Ty) : Term A A⋆ :=
  unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A

/-- `binconcat : A* × A* → A*`, defined as `(id × pure); prepend; concat`. -/
def binconcat (A : Ty) : Term (A⋆ ⊗ A⋆) A⋆ :=
  prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆ ⨟ concat A

/-- The homomorphism combinator `hom f = f*; concat`. -/
def homT {A B : Ty} (f : Term A B⋆) : Term A⋆ B⋆ := listF f ⨟ concat B

/-- Concatenation of two functions with list outputs, `f ⊙ g = (f × g); binconcat`. -/
def fdot {A₁ A₂ B : Ty} (f : Term A₁ B⋆) (g : Term A₂ B⋆) : Term (A₁ ⊗ A₂) B⋆ :=
  prodF f g ⨟ binconcat B

/-- Notation `f ⊙ g` for the concatenation of two terms with list outputs. -/
infixl:65 " ⊙ " => Term.fdot

/-- The inverse of distributivity on the right,
`undistR = either (id × Left) (id × Right)`. -/
def undistR (A B C : Ty) : Term ((A ⊗ B) ⊕' (A ⊗ C)) (A ⊗ (B ⊕' C)) :=
  either (prodF (Term.id A) (inl B C)) (prodF (Term.id A) (inr B C))

/-- The inverse of distributivity on the left. -/
def undistL (A B C : Ty) : Term ((A ⊗ C) ⊕' (B ⊗ C)) ((A ⊕' B) ⊗ C) :=
  either (prodF (inl A B) (Term.id C)) (prodF (inr A B) (Term.id C))

-- Values and concatenation with values (Section 5.2)

/-- **Definition 5.1 (Value).** A value is a term of type `1 → A`. -/
abbrev Value (A : Ty) : Type := Term Ty.unit A

/-- Pairing a value on the left with an arbitrary term: `(v,f) = (1,id); (v × f)`. -/
def pairL {A B C : Ty} (v : Value C) (f : Term A B) : Term A (C ⊗ B) :=
  unitL A ⨟ prodF v f

/-- Pairing a value on the right with an arbitrary term: `(f,v) = (id,1); (f × v)`. -/
def pairR {A B C : Ty} (f : Term A B) (v : Value C) : Term A (B ⊗ C) :=
  unitR A ⨟ prodF f v

/-- Concatenation of a list value on the left with a term with list outputs, `w · f`. -/
def dotL {A B : Ty} (w : Value B⋆) (f : Term A B⋆) : Term A B⋆ :=
  pairL w f ⨟ binconcat B

/-- Concatenation of a term with list outputs with a list value on the right, `f · w`. -/
def dotR {A B : Ty} (f : Term A B⋆) (w : Value B⋆) : Term A B⋆ :=
  pairR f w ⨟ binconcat B

/-- The singleton list value `[v] = v; pure`. -/
def sing {A : Ty} (v : Value A) : Value A⋆ := v ⨟ pureT A

/-- The *head term for `w`*: the first element of a list, or the value `w` if the list is
empty. -/
def headT {A : Ty} (w : Value A) : Term A⋆ A :=
  uncons A ⨟ either w (fst A A⋆)

-- Concatenation maps (Section 5.1)

/-- Type constructors with one parameter, used to define concatenation maps. -/
inductive TyF : Type
  /-- The parameter itself. -/
  | param : TyF
  /-- The unit type. -/
  | unit : TyF
  /-- Product of two type constructors. -/
  | prod : TyF → TyF → TyF
  /-- Co-product of two type constructors. -/
  | sum : TyF → TyF → TyF
  /-- List of a type constructor. -/
  | list : TyF → TyF

/-- The type `F(A)` obtained by substituting the type `A` for the parameter of `F`. -/
def TyF.app : TyF → Ty → Ty
  | .param, A => A
  | .unit, _ => Ty.unit
  | .prod F G, A => (F.app A) ⊗ (G.app A)
  | .sum F G, A => (F.app A) ⊕' (G.app A)
  | .list F, A => (F.app A)⋆

/-- **Concatenation maps** (Section 5.1): the term `F(A) ↣ A*` that concatenates all the
elements of the input into a single list, defined by induction on `F`. -/
def TyF.concatMap : (F : TyF) → (A : Ty) → Term (F.app A) A⋆
  | .param, A => pureT A
  | .unit, A => nilT A
  | .prod F G, A => (F.concatMap A) ⊙ (G.concatMap A)
  | .sum F G, A => either (F.concatMap A) (G.concatMap A)
  | .list F, A => homT (F.concatMap A)

/-- The type constructor `A ↦ Aᵏ`, the `k`-fold product of the parameter with itself. -/
def TyF.pow : ℕ → TyF
  | 0 => .unit
  | (k + 1) => .prod .param (TyF.pow k)

/-- The type constructor `A ↦ A⁰ + A¹ + ⋯ + Aᵏ`, i.e. `A^{<k+1}` in the notation of the
paper. -/
def TyF.lt : ℕ → TyF
  | 0 => TyF.pow 0
  | (k + 1) => .sum (TyF.lt k) (TyF.pow (k + 1))

/-- Type constructors with two parameters, used for the concatenation maps with values in
`(A + B)*` that occur in Axiom 15 and in the definition of `unsplit`. -/
inductive TyF2 : Type
  /-- The first parameter. -/
  | p1 : TyF2
  /-- The second parameter. -/
  | p2 : TyF2
  /-- The unit type. -/
  | unit : TyF2
  /-- Product of two type constructors. -/
  | prod : TyF2 → TyF2 → TyF2
  /-- Co-product of two type constructors. -/
  | sum : TyF2 → TyF2 → TyF2
  /-- List of a type constructor. -/
  | list : TyF2 → TyF2

/-- The type `F(A,B)`. -/
def TyF2.app : TyF2 → Ty → Ty → Ty
  | .p1, A, _ => A
  | .p2, _, B => B
  | .unit, _, _ => Ty.unit
  | .prod F G, A, B => (F.app A B) ⊗ (G.app A B)
  | .sum F G, A, B => (F.app A B) ⊕' (G.app A B)
  | .list F, A, B => (F.app A B)⋆

/-- The concatenation map `F(A,B) ↣ (A+B)*`, which injects the elements of `A` and of `B`
into the co-product `A + B` and concatenates all of them. -/
def TyF2.concatMap : (F : TyF2) → (A B : Ty) → Term (F.app A B) (A ⊕' B)⋆
  | .p1, A, B => inl A B ⨟ pureT (A ⊕' B)
  | .p2, A, B => inr A B ⨟ pureT (A ⊕' B)
  | .unit, A, B => nilT (A ⊕' B)
  | .prod F G, A, B => (F.concatMap A B) ⊙ (G.concatMap A B)
  | .sum F G, A, B => either (F.concatMap A B) (G.concatMap A B)
  | .list F, A, B => homT (F.concatMap A B)

/-- The inverse of `split`: it injects `A` and `B` into the co-product `A + B` and then
concatenates all resulting lists. -/
def unsplit (A B : Ty) : Term (A⋆ ⊗ (B ⊗ A⋆)⋆) (A ⊕' B)⋆ :=
  TyF2.concatMap (.prod (.list .p1) (.list (.prod .p2 (.list .p1)))) A B

-- The terms `shift` and `unshift` of Table 1

/-- The lift `shift : (A × B)* ⊸ 1 + A × (B × A)* × B`, obtained by composing `uncons`,
`assocR` and `shiftL`. -/
def shift (A B : Ty) : Term ((A ⊗ B)⋆) (Ty.unit ⊕' (A ⊗ ((B ⊗ A)⋆ ⊗ B))) :=
  uncons (A ⊗ B) ⨟
    sumF (Term.id Ty.unit) (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A))

/-- The drop `unshift : 1 + A × (B × A)* × B ⇒ (A × B)*`, the inverse of `shift`. -/
def unshift (A B : Ty) : Term (Ty.unit ⊕' (A ⊗ ((B ⊗ A)⋆ ⊗ B))) ((A ⊗ B)⋆) :=
  sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟ cons (A ⊗ B)

-- Terms for finite alphabets and the inverse of the group prefix operation

/-- The value `1 → 1 + ⋯ + 1` that picks out a given letter of a finite alphabet. -/
def constFin : {n : ℕ} → ⟦Ty.finAlph n⟧ → Value (Ty.finAlph n)
  | 0, _ => Term.id Ty.unit
  | (_ + 1), .inl _ => inl Ty.unit _
  | (_ + 1), .inr g => constFin g ⨟ inr Ty.unit _

/-- Case analysis on a letter of a finite alphabet that appears as the right component of a
product; it is derived using distributivity and co-pairing. -/
def caseR : {n : ℕ} → {A B : Ty} → (⟦Ty.finAlph n⟧ → Term A B) → Term (A ⊗ Ty.finAlph n) B
  | 0, A, _, t => fst A Ty.unit ⨟ t ()
  | (n + 1), A, _, t =>
      distR A Ty.unit (Ty.finAlph n) ⨟
        either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g)))

/-- Case analysis on a letter of a finite alphabet that appears as the left component of a
product. -/
def caseL : {n : ℕ} → {A B : Ty} → (⟦Ty.finAlph n⟧ → Term A B) → Term (Ty.finAlph n ⊗ A) B
  | 0, A, _, t => snd Ty.unit A ⨟ t ()
  | (n + 1), A, _, t =>
      distL Ty.unit (Ty.finAlph n) A ⨟
        either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g)))

/-- The term `(a,g) ↦ (g,(a,g))`, admissible because the group is a finite alphabet. -/
def grepeat (A : Ty) (n : ℕ) : Term (A ⊗ Ty.finAlph n) (Ty.finAlph n ⊗ (A ⊗ Ty.finAlph n)) :=
  caseR (fun g => pairL (constFin g) (pairR (Term.id A) (constFin g)))

/-- The term `(h,(g,a)) ↦ (a, h⁻¹ · g)`, admissible because the group is a finite
alphabet. -/
def gdiv (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A)) (A ⊗ Ty.finAlph n) :=
  caseL (fun h => caseL (fun g => pairR (Term.id A) (constFin (letI := G; h⁻¹ * g))))

/-- The unprefixing operation, the inverse of the group prefix multiplication:
`[(a₁,g₁),…,(aₙ,gₙ)] ↦ [(a₁,g₀⁻¹g₁),(a₂,g₁⁻¹g₂),…,(aₙ,gₙ₋₁⁻¹gₙ)]`, where `g₀` is the group
identity. -/
def unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((A ⊗ Ty.finAlph n)⋆) ((A ⊗ Ty.finAlph n)⋆) :=
  listF (grepeat A n) ⨟
    listF (assocL (Ty.finAlph n) A (Ty.finAlph n)) ⨟
      pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (Term.id _) ⨟
        shiftL (Ty.finAlph n) (Ty.finAlph n ⊗ A) ⨟
          fst _ _ ⨟ listF (gdiv A G)

end Term

end Lax149335.DerivedTerms
