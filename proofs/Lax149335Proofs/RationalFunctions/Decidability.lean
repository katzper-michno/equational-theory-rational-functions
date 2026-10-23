import Lax149335Proofs.RationalFunctions.SimpleRational

/-!
# Deciding equivalence of simple rational functions (Corollary 2.8)

This file contains the proof of Corollary 2.8: equivalence of simple rational terms is
decidable.  As explained in `Lax149335Proofs.RationalFunctions.SimpleRational`, the corollary is recorded as a
`Decidable` instance, so that an actual algorithm has to be supplied; the polynomial time
bound of the paper is not expressible here.

The algorithm is a recursion on the input type, and it is the computational content of the
normalisation used in the proof of Theorem 2.6:

* over the unit type, the two terms are compared on the unique input;
* over a co-product, the two terms are restricted to the two summands (`restrictL`,
  `restrictR`) and compared there;
* over a product `A₁ × A₂`, the terms are brought into the shape `w₀ · (x ⊙ y) · w₁`
  (`prodParts`), and it is enough to compare them on the inputs whose second component is a
  fixed element and on those whose first component is a fixed element: the two comparisons
  are again comparisons of simple rational terms, over `A₁` and over `A₂`.  That this
  suffices is `Lax149335Proofs.SimpleTerm.prod_criterion`, an application of Levi's lemma;
* over a list type, the terms are brought into the shape `w₀ · hom h · w₁` (`listParts`),
  and it is enough to compare them on the empty list and on the singleton lists; the latter
  comparison is again a comparison of simple rational terms, over the element type.  That
  this suffices is `Lax149335Proofs.SimpleTerm.list_criterion`, again an application of Levi's
  lemma: the two terms agree on singletons exactly when the conjugacy `h(a)·p = p·h'(a)`
  holds for the overhang `p` of the two constants, and this propagates to all lists.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace SimpleTerm

variable {Bs : Type}

/-! ### Restricting and decomposing a simple rational term according to its input type -/

/-- The restriction of a term with a co-product input type to the left summand. -/
def restrictL : {A₁ A₂ : Ty} → SimpleTerm Bs (A₁ ⊕' A₂) → SimpleTerm Bs A₁
  | _, _, .either f₁ _ => f₁
  | _, _, .pre w f => .pre w (restrictL f)
  | _, _, .post f w => .post (restrictL f) w

/-- The restriction of a term with a co-product input type to the right summand. -/
def restrictR : {A₁ A₂ : Ty} → SimpleTerm Bs (A₁ ⊕' A₂) → SimpleTerm Bs A₂
  | _, _, .either _ f₂ => f₂
  | _, _, .pre w f => .pre w (restrictR f)
  | _, _, .post f w => .post (restrictR f) w

theorem den_restrictL : {A₁ A₂ : Ty} → (f : SimpleTerm Bs (A₁ ⊕' A₂)) → (a : ⟦A₁⟧) →
    (restrictL f).den a = f.den (Sum.inl a)
  | _, _, .either _ _, _ => by simp [restrictL, den]
  | _, _, .pre w f, a => by simp [restrictL, den, den_restrictL f a]
  | _, _, .post f w, a => by simp [restrictL, den, den_restrictL f a]

theorem den_restrictR : {A₁ A₂ : Ty} → (f : SimpleTerm Bs (A₁ ⊕' A₂)) → (b : ⟦A₂⟧) →
    (restrictR f).den b = f.den (Sum.inr b)
  | _, _, .either _ _, _ => by simp [restrictR, den]
  | _, _, .pre w f, b => by simp [restrictR, den, den_restrictR f b]
  | _, _, .post f w, b => by simp [restrictR, den, den_restrictR f b]

/-- A term with a product input type, decomposed as `w₀ · (x ⊙ y) · w₁`. -/
def prodParts : {A₁ A₂ : Ty} → SimpleTerm Bs (A₁ ⊗ A₂) →
    List Bs × SimpleTerm Bs A₁ × SimpleTerm Bs A₂ × List Bs
  | _, _, .conc f₁ f₂ => ([], f₁, f₂, [])
  | _, _, .pre w f => let p := prodParts f; (w ++ p.1, p.2.1, p.2.2.1, p.2.2.2)
  | _, _, .post f w => let p := prodParts f; (p.1, p.2.1, p.2.2.1, p.2.2.2 ++ w)

theorem den_prodParts : {A₁ A₂ : Ty} → (f : SimpleTerm Bs (A₁ ⊗ A₂)) → (a : ⟦A₁⟧) →
    (b : ⟦A₂⟧) →
    f.den (a, b) = (prodParts f).1 ++ (prodParts f).2.1.den a ++ (prodParts f).2.2.1.den b ++
      (prodParts f).2.2.2
  | _, _, .conc _ _, _, _ => by simp [prodParts, den]
  | _, _, .pre w f, a, b => by simp [prodParts, den, den_prodParts f a b]
  | _, _, .post f w, a, b => by simp [prodParts, den, den_prodParts f a b]

/-- A term with a list input type, decomposed as `w₀ · hom h · w₁`. -/
def listParts : {A : Ty} → SimpleTerm Bs A⋆ → List Bs × SimpleTerm Bs A × List Bs
  | _, .hom f => ([], f, [])
  | _, .pre w f => let p := listParts f; (w ++ p.1, p.2.1, p.2.2)
  | _, .post f w => let p := listParts f; (p.1, p.2.1, p.2.2 ++ w)

theorem den_listParts : {A : Ty} → (f : SimpleTerm Bs A⋆) → (l : List ⟦A⟧) →
    f.den l = (listParts f).1 ++ (l.map (listParts f).2.1.den).flatten ++ (listParts f).2.2
  | _, .hom _, _ => by simp [listParts, den]
  | _, .pre w f, l => by simp [listParts, den, den_listParts f l]
  | _, .post f w, l => by simp [listParts, den, den_listParts f l]

/-! ### The two criteria -/

/-- **The criterion for a product input type.**  Two functions of the shape
`(a,b) ↦ w₀ · X(a) · Y(b) · w₁` are equal as soon as they are equal when the second argument
is fixed and when the first argument is fixed.  (An application of Levi's lemma: the two
"overhangs" agree.) -/
theorem prod_criterion {α β : Type} (X X' : α → List Bs) (Y Y' : β → List Bs)
    (w₀ w₁ v₀ v₁ : List Bs) (a₀ : α) (b₀ : β)
    (hA : ∀ a, w₀ ++ X a ++ Y b₀ ++ w₁ = v₀ ++ X' a ++ Y' b₀ ++ v₁)
    (hB : ∀ b, w₀ ++ X a₀ ++ Y b ++ w₁ = v₀ ++ X' a₀ ++ Y' b ++ v₁) :
    ∀ a b, w₀ ++ X a ++ Y b ++ w₁ = v₀ ++ X' a ++ Y' b ++ v₁ := by
  simp only [List.append_assoc] at hA hB ⊢
  have key : (w₀ ++ X a₀) ++ (Y b₀ ++ w₁) = (v₀ ++ X' a₀) ++ (Y' b₀ ++ v₁) := by
    simp only [List.append_assoc]; exact hA a₀
  rcases List.append_eq_append_iff.mp key with ⟨q, hq1, hq2⟩ | ⟨q, hq1, hq2⟩
  · have star : ∀ a, (w₀ ++ X a) ++ q = v₀ ++ X' a := by
      intro a
      refine List.append_cancel_right (bs := Y' b₀ ++ v₁) ?_
      calc ((w₀ ++ X a) ++ q) ++ (Y' b₀ ++ v₁)
          = (w₀ ++ X a) ++ (q ++ (Y' b₀ ++ v₁)) := by simp [List.append_assoc]
        _ = (w₀ ++ X a) ++ (Y b₀ ++ w₁) := by rw [hq2]
        _ = w₀ ++ (X a ++ (Y b₀ ++ w₁)) := by simp [List.append_assoc]
        _ = v₀ ++ (X' a ++ (Y' b₀ ++ v₁)) := hA a
        _ = (v₀ ++ X' a) ++ (Y' b₀ ++ v₁) := by simp [List.append_assoc]
    have starstar : ∀ b, Y b ++ w₁ = q ++ (Y' b ++ v₁) := by
      intro b
      refine List.append_cancel_left (as := w₀ ++ X a₀) ?_
      calc (w₀ ++ X a₀) ++ (Y b ++ w₁)
          = w₀ ++ (X a₀ ++ (Y b ++ w₁)) := by simp [List.append_assoc]
        _ = v₀ ++ (X' a₀ ++ (Y' b ++ v₁)) := hB b
        _ = (v₀ ++ X' a₀) ++ (Y' b ++ v₁) := by simp [List.append_assoc]
        _ = ((w₀ ++ X a₀) ++ q) ++ (Y' b ++ v₁) := by rw [hq1]
        _ = (w₀ ++ X a₀) ++ (q ++ (Y' b ++ v₁)) := by simp [List.append_assoc]
    intro a b
    calc w₀ ++ (X a ++ (Y b ++ w₁))
        = (w₀ ++ X a) ++ (Y b ++ w₁) := by simp [List.append_assoc]
      _ = (w₀ ++ X a) ++ (q ++ (Y' b ++ v₁)) := by rw [starstar b]
      _ = ((w₀ ++ X a) ++ q) ++ (Y' b ++ v₁) := by simp [List.append_assoc]
      _ = (v₀ ++ X' a) ++ (Y' b ++ v₁) := by rw [star a]
      _ = v₀ ++ (X' a ++ (Y' b ++ v₁)) := by simp [List.append_assoc]
  · have star : ∀ a, (v₀ ++ X' a) ++ q = w₀ ++ X a := by
      intro a
      refine List.append_cancel_right (bs := Y b₀ ++ w₁) ?_
      calc ((v₀ ++ X' a) ++ q) ++ (Y b₀ ++ w₁)
          = (v₀ ++ X' a) ++ (q ++ (Y b₀ ++ w₁)) := by simp [List.append_assoc]
        _ = (v₀ ++ X' a) ++ (Y' b₀ ++ v₁) := by rw [hq2]
        _ = v₀ ++ (X' a ++ (Y' b₀ ++ v₁)) := by simp [List.append_assoc]
        _ = w₀ ++ (X a ++ (Y b₀ ++ w₁)) := (hA a).symm
        _ = (w₀ ++ X a) ++ (Y b₀ ++ w₁) := by simp [List.append_assoc]
    have starstar : ∀ b, Y' b ++ v₁ = q ++ (Y b ++ w₁) := by
      intro b
      refine List.append_cancel_left (as := v₀ ++ X' a₀) ?_
      calc (v₀ ++ X' a₀) ++ (Y' b ++ v₁)
          = v₀ ++ (X' a₀ ++ (Y' b ++ v₁)) := by simp [List.append_assoc]
        _ = w₀ ++ (X a₀ ++ (Y b ++ w₁)) := (hB b).symm
        _ = (w₀ ++ X a₀) ++ (Y b ++ w₁) := by simp [List.append_assoc]
        _ = ((v₀ ++ X' a₀) ++ q) ++ (Y b ++ w₁) := by rw [hq1]
        _ = (v₀ ++ X' a₀) ++ (q ++ (Y b ++ w₁)) := by simp [List.append_assoc]
    intro a b
    refine Eq.symm ?_
    calc v₀ ++ (X' a ++ (Y' b ++ v₁))
        = (v₀ ++ X' a) ++ (Y' b ++ v₁) := by simp [List.append_assoc]
      _ = (v₀ ++ X' a) ++ (q ++ (Y b ++ w₁)) := by rw [starstar b]
      _ = ((v₀ ++ X' a) ++ q) ++ (Y b ++ w₁) := by simp [List.append_assoc]
      _ = (w₀ ++ X a) ++ (Y b ++ w₁) := by rw [star a]
      _ = w₀ ++ (X a ++ (Y b ++ w₁)) := by simp [List.append_assoc]

/-- A conjugacy `h(a)·p = p·h'(a)` propagates from letters to words. -/
theorem flatten_conj {α : Type} (h h' : α → List Bs) (p : List Bs)
    (hc : ∀ a, h a ++ p = p ++ h' a) :
    ∀ l : List α, (l.map h).flatten ++ p = p ++ (l.map h').flatten := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      calc (h a ++ (List.map h t).flatten) ++ p
          = h a ++ ((List.map h t).flatten ++ p) := by rw [List.append_assoc]
        _ = h a ++ (p ++ (List.map h' t).flatten) := by rw [ih]
        _ = (h a ++ p) ++ (List.map h' t).flatten := by rw [List.append_assoc]
        _ = (p ++ h' a) ++ (List.map h' t).flatten := by rw [hc a]
        _ = p ++ (h' a ++ (List.map h' t).flatten) := by rw [List.append_assoc]

/-- **The criterion for a list input type.**  Two functions of the shape
`l ↦ w₀ · h(l₁) ⋯ h(lₙ) · w₁` are equal as soon as they are equal on the empty list and on
the singleton lists.  (Again an application of Levi's lemma: agreement on the singletons
means that the letters are conjugated by the overhang of the two constants.) -/
theorem list_criterion {α : Type} (h h' : α → List Bs) (w₀ w₁ v₀ v₁ : List Bs)
    (h0 : w₀ ++ w₁ = v₀ ++ v₁)
    (h1 : ∀ a, w₀ ++ h a ++ w₁ = v₀ ++ h' a ++ v₁) :
    ∀ l : List α, w₀ ++ (l.map h).flatten ++ w₁ = v₀ ++ (l.map h').flatten ++ v₁ := by
  simp only [List.append_assoc] at h1 ⊢
  rcases List.append_eq_append_iff.mp h0 with ⟨p, hp1, hp2⟩ | ⟨p, hp1, hp2⟩
  · -- `v₀ = w₀ ++ p` and `w₁ = p ++ v₁`
    have hc : ∀ a, h a ++ p = p ++ h' a := by
      intro a
      refine List.append_cancel_right (bs := v₁) (List.append_cancel_left (as := w₀) ?_)
      calc w₀ ++ ((h a ++ p) ++ v₁)
          = w₀ ++ (h a ++ (p ++ v₁)) := by simp [List.append_assoc]
        _ = w₀ ++ (h a ++ w₁) := by rw [hp2]
        _ = v₀ ++ (h' a ++ v₁) := h1 a
        _ = (w₀ ++ p) ++ (h' a ++ v₁) := by rw [hp1]
        _ = w₀ ++ ((p ++ h' a) ++ v₁) := by simp [List.append_assoc]
    intro l
    calc w₀ ++ ((l.map h).flatten ++ w₁)
        = w₀ ++ ((l.map h).flatten ++ (p ++ v₁)) := by rw [hp2]
      _ = w₀ ++ (((l.map h).flatten ++ p) ++ v₁) := by simp [List.append_assoc]
      _ = w₀ ++ ((p ++ (l.map h').flatten) ++ v₁) := by rw [flatten_conj h h' p hc l]
      _ = (w₀ ++ p) ++ ((l.map h').flatten ++ v₁) := by simp [List.append_assoc]
      _ = v₀ ++ ((l.map h').flatten ++ v₁) := by rw [← hp1]
  · -- `w₀ = v₀ ++ p` and `v₁ = p ++ w₁`
    have hc : ∀ a, h' a ++ p = p ++ h a := by
      intro a
      refine List.append_cancel_right (bs := w₁) (List.append_cancel_left (as := v₀) ?_)
      calc v₀ ++ ((h' a ++ p) ++ w₁)
          = v₀ ++ (h' a ++ (p ++ w₁)) := by simp [List.append_assoc]
        _ = v₀ ++ (h' a ++ v₁) := by rw [hp2]
        _ = w₀ ++ (h a ++ w₁) := (h1 a).symm
        _ = (v₀ ++ p) ++ (h a ++ w₁) := by rw [hp1]
        _ = v₀ ++ ((p ++ h a) ++ w₁) := by simp [List.append_assoc]
    intro l
    refine Eq.symm ?_
    calc v₀ ++ ((l.map h').flatten ++ v₁)
        = v₀ ++ ((l.map h').flatten ++ (p ++ w₁)) := by rw [hp2]
      _ = v₀ ++ (((l.map h').flatten ++ p) ++ w₁) := by simp [List.append_assoc]
      _ = v₀ ++ ((p ++ (l.map h).flatten) ++ w₁) := by rw [flatten_conj h' h p hc l]
      _ = (v₀ ++ p) ++ ((l.map h).flatten ++ w₁) := by simp [List.append_assoc]
      _ = w₀ ++ ((l.map h).flatten ++ w₁) := by rw [← hp1]

/-! ### The decision procedure -/

/-- The comparison of two terms with a product input type, with the second argument fixed. -/
def prodFixR {A₁ A₂ : Ty} (f : SimpleTerm Bs (A₁ ⊗ A₂)) : SimpleTerm Bs A₁ :=
  .pre (prodParts f).1
    (.post (prodParts f).2.1
      ((prodParts f).2.2.1.den (Ty.someElem A₂) ++ (prodParts f).2.2.2))

/-- The comparison of two terms with a product input type, with the first argument fixed. -/
def prodFixL {A₁ A₂ : Ty} (f : SimpleTerm Bs (A₁ ⊗ A₂)) : SimpleTerm Bs A₂ :=
  .pre ((prodParts f).1 ++ (prodParts f).2.1.den (Ty.someElem A₁))
    (.post (prodParts f).2.2.1 (prodParts f).2.2.2)

/-- The comparison of two terms with a list input type, on the singleton lists. -/
def listSingle {A : Ty} (f : SimpleTerm Bs A⋆) : SimpleTerm Bs A :=
  .pre (listParts f).1 (.post (listParts f).2.1 (listParts f).2.2)

theorem den_prodFixR {A₁ A₂ : Ty} (f : SimpleTerm Bs (A₁ ⊗ A₂)) (a : ⟦A₁⟧) :
    (prodFixR f).den a = f.den (a, Ty.someElem A₂) := by
  simp [prodFixR, den, den_prodParts f a (Ty.someElem A₂), List.append_assoc]

theorem den_prodFixL {A₁ A₂ : Ty} (f : SimpleTerm Bs (A₁ ⊗ A₂)) (b : ⟦A₂⟧) :
    (prodFixL f).den b = f.den (Ty.someElem A₁, b) := by
  simp [prodFixL, den, den_prodParts f (Ty.someElem A₁) b, List.append_assoc]

theorem den_listSingle {A : Ty} (f : SimpleTerm Bs A⋆) (a : ⟦A⟧) :
    (listSingle f).den a = f.den [a] := by
  simp [listSingle, den, den_listParts f [a], List.append_assoc]

/-- Over a co-product input type, two terms are equal exactly when their restrictions to the
two summands are. -/
theorem den_eq_sum_iff {A₁ A₂ : Ty} (f g : SimpleTerm Bs (A₁ ⊕' A₂)) :
    f.den = g.den ↔
      ((restrictL f).den = (restrictL g).den ∧ (restrictR f).den = (restrictR g).den) := by
  constructor
  · intro h
    exact ⟨funext fun a => by rw [den_restrictL, den_restrictL, h],
      funext fun b => by rw [den_restrictR, den_restrictR, h]⟩
  · rintro ⟨h₁, h₂⟩
    funext x
    cases x with
    | inl a => rw [← den_restrictL, ← den_restrictL, h₁]
    | inr b => rw [← den_restrictR, ← den_restrictR, h₂]

/-- Over a product input type, two terms are equal exactly when they agree on the inputs
whose second component is fixed and on those whose first component is fixed. -/
theorem den_eq_prod_iff {A₁ A₂ : Ty} (f g : SimpleTerm Bs (A₁ ⊗ A₂)) :
    f.den = g.den ↔
      ((prodFixR f).den = (prodFixR g).den ∧ (prodFixL f).den = (prodFixL g).den) := by
  constructor
  · intro h
    exact ⟨funext fun a => by rw [den_prodFixR, den_prodFixR, h],
      funext fun b => by rw [den_prodFixL, den_prodFixL, h]⟩
  · rintro ⟨h₁, h₂⟩
    have hA : ∀ a : ⟦A₁⟧, f.den (a, Ty.someElem A₂) = g.den (a, Ty.someElem A₂) := by
      intro a
      rw [← den_prodFixR, ← den_prodFixR, h₁]
    have hB : ∀ b : ⟦A₂⟧, f.den (Ty.someElem A₁, b) = g.den (Ty.someElem A₁, b) := by
      intro b
      rw [← den_prodFixL, ← den_prodFixL, h₂]
    funext x
    obtain ⟨a, b⟩ := x
    have := prod_criterion (prodParts f).2.1.den (prodParts g).2.1.den
      (prodParts f).2.2.1.den (prodParts g).2.2.1.den
      (prodParts f).1 (prodParts f).2.2.2 (prodParts g).1 (prodParts g).2.2.2
      (Ty.someElem A₁) (Ty.someElem A₂)
      (fun a => by
        rw [← den_prodParts f a (Ty.someElem A₂), ← den_prodParts g a (Ty.someElem A₂)]
        exact hA a)
      (fun b => by
        rw [← den_prodParts f (Ty.someElem A₁) b, ← den_prodParts g (Ty.someElem A₁) b]
        exact hB b) a b
    rw [den_prodParts f a b, den_prodParts g a b]
    exact this

/-- Over a list input type, two terms are equal exactly when they agree on the empty list and
on the singleton lists. -/
theorem den_eq_list_iff {A : Ty} (f g : SimpleTerm Bs A⋆) :
    f.den = g.den ↔
      ((listParts f).1 ++ (listParts f).2.2 = (listParts g).1 ++ (listParts g).2.2 ∧
        (listSingle f).den = (listSingle g).den) := by
  constructor
  · intro h
    refine ⟨?_, funext fun a => by rw [den_listSingle, den_listSingle, h]⟩
    have := congrFun h ([] : List ⟦A⟧)
    rw [den_listParts f [], den_listParts g []] at this
    simpa using this
  · rintro ⟨h₀, h₁⟩
    funext l
    have hs : ∀ a : ⟦A⟧, f.den [a] = g.den [a] := by
      intro a
      rw [← den_listSingle, ← den_listSingle, h₁]
    have := list_criterion (listParts f).2.1.den (listParts g).2.1.den
      (listParts f).1 (listParts f).2.2 (listParts g).1 (listParts g).2.2
      (by simpa using h₀)
      (fun a => by
        have h2 := hs a
        rw [den_listParts f [a], den_listParts g [a]] at h2
        simpa using h2) l
    rw [den_listParts f l, den_listParts g l]
    exact this

/-- **Corollary 2.8.**  Equivalence for simple rational functions is decidable.

The paper states the corollary with a **polynomial time** bound: by the proof of Theorem 2.6
the only conjugacies that have to be tried are those by an infix of the string of constants
of the two terms, and there is a quadratic number of those.  The complexity claim is not
formalised — the statement below is the decidability of equivalence, given by an explicit
algorithm, since the cost model needed to speak about running time is not available here. -/
def decidableDenEq [DecidableEq Bs] : {A : Ty} → (f g : SimpleTerm Bs A) → Decidable (f.den = g.den)
  | .unit, f, g =>
      decidable_of_iff (f.den () = g.den ())
        ⟨fun h => funext fun x => by cases x; exact h, fun h => congrFun h ()⟩
  | .sum A₁ A₂, f, g =>
      letI := decidableDenEq (restrictL f) (restrictL g)
      letI := decidableDenEq (restrictR f) (restrictR g)
      decidable_of_iff _ (den_eq_sum_iff f g).symm
  | .prod A₁ A₂, f, g =>
      letI := decidableDenEq (prodFixR f) (prodFixR g)
      letI := decidableDenEq (prodFixL f) (prodFixL g)
      decidable_of_iff _ (den_eq_prod_iff f g).symm
  | .list A, f, g =>
      letI := decidableDenEq (listSingle f) (listSingle g)
      decidable_of_iff _ (den_eq_list_iff f g).symm

/-- **Corollary 2.8, as a finite test.**  Two simple rational terms define the same function
exactly when they agree on the test inputs of their input type.  This is the content of the
decision procedure `decidableDenEq`: over a co-product the two summands are compared, over a
product the two components are compared with the other one fixed, and over a list type the
empty list and the singleton lists are compared. -/
theorem den_eq_iff_testInputs : {A : Ty} → (f g : SimpleTerm Bs A) →
    (f.den = g.den ↔ ∀ x ∈ testInputs A, f.den x = g.den x)
  | .unit, f, g => by
      constructor
      · intro h x _
        rw [h]
      · intro h
        funext x
        cases x
        exact h () (by simp [testInputs])
  | .sum A₁ A₂, f, g => by
      rw [den_eq_sum_iff, den_eq_iff_testInputs (restrictL f) (restrictL g),
        den_eq_iff_testInputs (restrictR f) (restrictR g)]
      simp only [testInputs, List.mem_append, List.mem_map]
      constructor
      · rintro ⟨h₁, h₂⟩ x (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · rw [← den_restrictL, ← den_restrictL]
          exact h₁ a ha
        · rw [← den_restrictR, ← den_restrictR]
          exact h₂ b hb
      · intro h
        refine ⟨fun a ha => ?_, fun b hb => ?_⟩
        · rw [den_restrictL, den_restrictL]
          exact h _ (Or.inl ⟨a, ha, rfl⟩)
        · rw [den_restrictR, den_restrictR]
          exact h _ (Or.inr ⟨b, hb, rfl⟩)
  | .prod A₁ A₂, f, g => by
      rw [den_eq_prod_iff, den_eq_iff_testInputs (prodFixR f) (prodFixR g),
        den_eq_iff_testInputs (prodFixL f) (prodFixL g)]
      simp only [testInputs, List.mem_append, List.mem_map]
      constructor
      · rintro ⟨h₁, h₂⟩ x (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · rw [← den_prodFixR, ← den_prodFixR]
          exact h₁ a ha
        · rw [← den_prodFixL, ← den_prodFixL]
          exact h₂ b hb
      · intro h
        refine ⟨fun a ha => ?_, fun b hb => ?_⟩
        · rw [den_prodFixR, den_prodFixR]
          exact h _ (Or.inl ⟨a, ha, rfl⟩)
        · rw [den_prodFixL, den_prodFixL]
          exact h _ (Or.inr ⟨b, hb, rfl⟩)
  | .list A, f, g => by
      have e : ∀ h : SimpleTerm Bs A⋆, h.den [] = (listParts h).1 ++ (listParts h).2.2 := by
        intro h
        rw [den_listParts]
        simp
      rw [den_eq_list_iff, den_eq_iff_testInputs (listSingle f) (listSingle g)]
      simp only [testInputs, List.mem_cons, List.mem_map]
      constructor
      · rintro ⟨h₀, h₁⟩ x (rfl | ⟨a, ha, rfl⟩)
        · rw [e, e]
          exact h₀
        · rw [← den_listSingle, ← den_listSingle]
          exact h₁ a ha
      · intro h
        refine ⟨?_, fun a ha => ?_⟩
        · rw [← e, ← e]
          exact h [] (Or.inl rfl)
        · rw [den_listSingle, den_listSingle]
          exact h _ (Or.inr ⟨a, ha, rfl⟩)

end SimpleTerm

/-! ### The algorithm at work

Four illustrations of the decision procedure, checked when this file is compiled.  The third
one is a pair of conjugate terms: `hom(a ↦ ab)·a` and `a·hom(a ↦ ba)` define the same
function, and the procedure recognises this. -/

section Examples

open Lax149335Proofs.SimpleTerm

private def exf₁ : SimpleTerm Bool (Ty.unit ⊗ Ty.unit) := .pre [true] (.conc .empty .empty)
private def exg₁ : SimpleTerm Bool (Ty.unit ⊗ Ty.unit) := .post (.conc .empty .empty) [true]

/-- info: true -/
#guard_msgs in
#eval @Decidable.decide _ (decidableDenEq exf₁ exg₁)

private def exf₂ : SimpleTerm Bool Ty.unit⋆ := .hom (.pre [true] .empty)
private def exg₂ : SimpleTerm Bool Ty.unit⋆ := .hom (.pre [false] .empty)

/-- info: false -/
#guard_msgs in
#eval @Decidable.decide _ (decidableDenEq exf₂ exg₂)

private def exf₃ : SimpleTerm Bool Ty.unit⋆ := .post (.hom (.pre [true, false] .empty)) [true]
private def exg₃ : SimpleTerm Bool Ty.unit⋆ := .pre [true] (.hom (.pre [false, true] .empty))

/-- info: true -/
#guard_msgs in
#eval @Decidable.decide _ (decidableDenEq exf₃ exg₃)

private def exg₄ : SimpleTerm Bool Ty.unit⋆ := .pre [true] (.hom (.pre [true, false] .empty))

/-- info: false -/
#guard_msgs in
#eval @Decidable.decide _ (decidableDenEq exf₃ exg₄)

end Examples

end Lax149335Proofs

bridge_export Lax149335Proofs
