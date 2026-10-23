import Lax149335Proofs.Terms.Derived

/-!
# Denotations of the derived terms

This file computes the denotation of each derived term of `Lax149335Proofs.Terms.Derived` and
establishes the semantic facts (about `splitDen`, `shiftRDen`, `shiftLDen`, `prefixMul`, ...)
that are needed for the soundness of the axioms of Section 4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

variable {A B C : Ty}

/-! ### Denotations of the atomic terms -/

@[simp] theorem den_comp {A B C : Ty} (f : Term A B) (g : Term B C) (x : ⟦A⟧) :
    (f ⨟ g).den x = g.den (f.den x) := rfl

@[simp] theorem den_prodF {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂)
    (x : ⟦A₁⟧ × ⟦A₂⟧) : (prodF f g).den x = (f.den x.1, g.den x.2) := rfl

@[simp] theorem den_sumF_inl {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) (a : ⟦A₁⟧) :
    (sumF f g).den (Sum.inl a) = Sum.inl (f.den a) := rfl

@[simp] theorem den_sumF_inr {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) (b : ⟦A₂⟧) :
    (sumF f g).den (Sum.inr b) = Sum.inr (g.den b) := rfl

@[simp] theorem den_listF {A B : Ty} (f : Term A B) (l : List ⟦A⟧) :
    (listF f).den l = l.map f.den := rfl

@[simp] theorem den_id (A : Ty) (x : ⟦A⟧) : (Term.id A).den x = x := rfl

@[simp] theorem den_inl (A B : Ty) (x : ⟦A⟧) : (inl A B).den x = Sum.inl x := rfl

@[simp] theorem den_inr (A B : Ty) (x : ⟦B⟧) : (inr A B).den x = Sum.inr x := rfl

@[simp] theorem den_codiag_inl (A : Ty) (x : ⟦A⟧) :
    (codiag A).den (Sum.inl x) = x := rfl

@[simp] theorem den_codiag_inr (A : Ty) (x : ⟦A⟧) :
    (codiag A).den (Sum.inr x) = x := rfl

@[simp] theorem den_fst (A B : Ty) (x : ⟦A⟧ × ⟦B⟧) : (fst A B).den x = x.1 := rfl

@[simp] theorem den_snd (A B : Ty) (x : ⟦A⟧ × ⟦B⟧) : (snd A B).den x = x.2 := rfl

@[simp] theorem den_unitR (A : Ty) (x : ⟦A⟧) : (unitR A).den x = (x, ()) := rfl

@[simp] theorem den_unitL (A : Ty) (x : ⟦A⟧) : (unitL A).den x = ((), x) := rfl

@[simp] theorem den_assocL (A B C : Ty) (x : ⟦A⟧ × (⟦B⟧ × ⟦C⟧)) :
    (assocL A B C).den x = ((x.1, x.2.1), x.2.2) := rfl

@[simp] theorem den_assocR (A B C : Ty) (x : (⟦A⟧ × ⟦B⟧) × ⟦C⟧) :
    (assocR A B C).den x = (x.1.1, (x.1.2, x.2)) := rfl

@[simp] theorem den_distR_inl (A B C : Ty) (a : ⟦A⟧) (b : ⟦B⟧) :
    (distR A B C).den (a, Sum.inl b) = Sum.inl (a, b) := rfl

@[simp] theorem den_distR_inr (A B C : Ty) (a : ⟦A⟧) (c : ⟦C⟧) :
    (distR A B C).den (a, Sum.inr c) = Sum.inr (a, c) := rfl

@[simp] theorem den_distL_inl (A B C : Ty) (a : ⟦A⟧) (c : ⟦C⟧) :
    (distL A B C).den (Sum.inl a, c) = Sum.inl (a, c) := rfl

@[simp] theorem den_distL_inr (A B C : Ty) (b : ⟦B⟧) (c : ⟦C⟧) :
    (distL A B C).den (Sum.inr b, c) = Sum.inr (b, c) := rfl

@[simp] theorem den_cons_inl (A : Ty) (u : Unit) :
    (cons A).den (Sum.inl u) = ([] : List ⟦A⟧) := rfl

@[simp] theorem den_cons_inr (A : Ty) (a : ⟦A⟧) (l : List ⟦A⟧) :
    (cons A).den (Sum.inr (a, l)) = a :: l := rfl

@[simp] theorem den_uncons_nil (A : Ty) :
    (uncons A).den ([] : List ⟦A⟧) = Sum.inl () := rfl

@[simp] theorem den_uncons_cons (A : Ty) (a : ⟦A⟧) (l : List ⟦A⟧) :
    (uncons A).den (a :: l) = Sum.inr (a, l) := rfl

@[simp] theorem den_snoc_inl (A : Ty) (u : Unit) :
    (snoc A).den (Sum.inl u) = ([] : List ⟦A⟧) := rfl

@[simp] theorem den_snoc_inr (A : Ty) (l : List ⟦A⟧) (a : ⟦A⟧) :
    (snoc A).den (Sum.inr (l, a)) = l ++ [a] := rfl

@[simp] theorem den_snoc (A : Ty) (x : Unit ⊕ (List ⟦A⟧ × ⟦A⟧)) :
    (snoc A).den x = snocDen x := rfl

@[simp] theorem den_unsnoc (A : Ty) (l : List ⟦A⟧) :
    (unsnoc A).den l = unsnocDen l := rfl

@[simp] theorem den_concat (A : Ty) (l : List (List ⟦A⟧)) :
    (concat A).den l = l.flatten := rfl

@[simp] theorem den_split (A B : Ty) (l : List (⟦A⟧ ⊕ ⟦B⟧)) :
    (split A B).den l = splitDen l := rfl

@[simp] theorem den_shiftR (A B : Ty) (l : List (⟦A⟧ × ⟦B⟧)) (a : ⟦A⟧) :
    (shiftR A B).den (l, a) = shiftRDen l a := rfl

@[simp] theorem den_shiftL (A B : Ty) (a : ⟦A⟧) (l : List (⟦B⟧ × ⟦A⟧)) :
    (shiftL A B).den (a, l) = shiftLDen a l := rfl

@[simp] theorem den_pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (l : List (⟦A⟧ × ⟦Ty.finAlph n⟧)) :
    (pref A G).den l = letI := G; prefixMul (1 : ⟦Ty.finAlph n⟧) l := rfl

/-! ### Denotations of the combinators, as functions -/

@[simp] theorem den_comp_fun {A B C : Ty} (f : Term A B) (g : Term B C) :
    (f ⨟ g).den = fun x => g.den (f.den x) := rfl

@[simp] theorem den_listF_fun {A B : Ty} (f : Term A B) :
    (listF f).den = List.map f.den := rfl

@[simp] theorem den_prodF_fun {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) :
    (prodF f g).den = fun x => (f.den x.1, g.den x.2) := rfl

@[simp] theorem den_sumF_fun {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) :
    (sumF f g).den = Sum.map f.den g.den := by
  funext x; cases x <;> rfl

@[simp] theorem den_id_fun (A : Ty) : (Term.id A).den = _root_.id := rfl

/-! ### Denotations of the derived terms -/

@[simp] theorem den_toUnit (A : Ty) (x : ⟦A⟧) : (toUnit A).den x = () := rfl

@[simp] theorem den_either {A₁ A₂ B : Ty} (f : Term A₁ B) (g : Term A₂ B)
    (x : ⟦A₁⟧ ⊕ ⟦A₂⟧) : (either f g).den x = Sum.elim f.den g.den x := by
  cases x <;> rfl

@[simp] theorem den_nilT (A : Ty) (u : Unit) : (nilT A).den u = ([] : List ⟦A⟧) := rfl

@[simp] theorem den_prepend (A : Ty) (a : ⟦A⟧) (l : List ⟦A⟧) :
    (prepend A).den (a, l) = a :: l := rfl

@[simp] theorem den_append (A : Ty) (l : List ⟦A⟧) (a : ⟦A⟧) :
    (append A).den (l, a) = l ++ [a] := rfl

@[simp] theorem den_pureT (A : Ty) (a : ⟦A⟧) : (pureT A).den a = [a] := rfl

@[simp] theorem den_pureT_fun (A : Ty) : (pureT A).den = fun a => [a] := rfl

@[simp] theorem den_nilT_fun (A : Ty) : (nilT A).den = fun _ => ([] : List ⟦A⟧) := rfl

@[simp] theorem den_prepend_fun (A : Ty) :
    (prepend A).den = fun x : ⟦A⟧ × List ⟦A⟧ => x.1 :: x.2 := rfl

@[simp] theorem den_binconcat (A : Ty) (l₁ l₂ : List ⟦A⟧) :
    (binconcat A).den (l₁, l₂) = l₁ ++ l₂ := by
  show ([l₁, l₂] : List (List ⟦A⟧)).flatten = l₁ ++ l₂
  simp

@[simp] theorem den_homT {A B : Ty} (f : Term A B⋆) (l : List ⟦A⟧) :
    (homT f).den l = (l.map f.den).flatten := rfl

@[simp] theorem den_fdot {A₁ A₂ B : Ty} (f : Term A₁ B⋆) (g : Term A₂ B⋆)
    (x : ⟦A₁⟧ × ⟦A₂⟧) :
    (f ⊙ g).den x = List.append (f.den x.1) (g.den x.2) := by
  simp [fdot]

@[simp] theorem den_undistR_inl (A B C : Ty) (a : ⟦A⟧) (b : ⟦B⟧) :
    (undistR A B C).den (Sum.inl (a, b)) = (a, Sum.inl b) := rfl

@[simp] theorem den_undistR_inr (A B C : Ty) (a : ⟦A⟧) (c : ⟦C⟧) :
    (undistR A B C).den (Sum.inr (a, c)) = (a, Sum.inr c) := rfl

@[simp] theorem den_undistL_inl (A B C : Ty) (a : ⟦A⟧) (c : ⟦C⟧) :
    (undistL A B C).den (Sum.inl (a, c)) = (Sum.inl a, c) := rfl

@[simp] theorem den_undistL_inr (A B C : Ty) (b : ⟦B⟧) (c : ⟦C⟧) :
    (undistL A B C).den (Sum.inr (b, c)) = (Sum.inr b, c) := rfl

@[simp] theorem den_comm_inl (A B : Ty) (a : ⟦A⟧) :
    (comm A B).den (Sum.inl a) = Sum.inr a := rfl

@[simp] theorem den_comm_inr (A B : Ty) (b : ⟦B⟧) :
    (comm A B).den (Sum.inr b) = Sum.inl b := rfl

@[simp] theorem den_pairL {A B C : Ty} (v : Value C) (f : Term A B) (x : ⟦A⟧) :
    (pairL v f).den x = (v.den (), f.den x) := rfl

@[simp] theorem den_pairR {A B C : Ty} (f : Term A B) (v : Value C) (x : ⟦A⟧) :
    (pairR f v).den x = (f.den x, v.den ()) := rfl

@[simp] theorem den_dotL {A B : Ty} (w : Value B⋆) (f : Term A B⋆) (x : ⟦A⟧) :
    (dotL w f).den x = List.append (w.den ()) (f.den x) := by
  simp [dotL]

@[simp] theorem den_dotR {A B : Ty} (f : Term A B⋆) (w : Value B⋆) (x : ⟦A⟧) :
    (dotR f w).den x = List.append (f.den x) (w.den ()) := by
  simp [dotR]

@[simp] theorem den_sing {A : Ty} (v : Value A) (u : Unit) :
    (sing v).den u = [v.den ()] := rfl

/-! ### `snoc`, `unsnoc`, `split`, `shift` -/

@[simp] theorem snocDen_inl {α : Type} (u : Unit) : snocDen (Sum.inl u : Unit ⊕ (List α × α)) = [] := rfl

@[simp] theorem snocDen_inr {α : Type} (l : List α) (a : α) :
    snocDen (Sum.inr (l, a)) = l ++ [a] := rfl

theorem unsnocDen_append_singleton {α : Type} (l : List α) (a : α) :
    unsnocDen (l ++ [a]) = Sum.inr (l, a) := by
  simp [unsnocDen]

@[simp] theorem snocDen_unsnocDen {α : Type} (l : List α) : snocDen (unsnocDen l) = l := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
  · subst h; rfl
  · rw [List.concat_eq_append, unsnocDen_append_singleton]; rfl

@[simp] theorem unsnocDen_snocDen {α : Type} (x : Unit ⊕ (List α × α)) :
    unsnocDen (snocDen x) = x := by
  rcases x with ⟨⟩ | ⟨l, a⟩
  · rfl
  · rw [show snocDen (Sum.inr (l, a)) = l ++ [a] from rfl, unsnocDen_append_singleton]

/-- The denotation of the term `unsplit`. -/
def unsplitDen {α β : Type} (x : List α × List (β × List α)) : List (α ⊕ β) :=
  x.1.map Sum.inl ++ (x.2.map (fun p => Sum.inr p.1 :: p.2.map Sum.inl)).flatten

theorem den_unsplit (A B : Ty) (x : List ⟦A⟧ × List (⟦B⟧ × List ⟦A⟧)) :
    (unsplit A B).den x = unsplitDen x := by
  obtain ⟨l, ls⟩ := x
  have h3 : ∀ l : List ⟦A⟧,
      (l.map (fun a => ([Sum.inl a] : List ⟦A ⊕' B⟧))).flatten = l.map Sum.inl := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.map_cons, List.flatten_cons, ih, List.cons_append, List.nil_append]
  simp only [unsplit, TyF2.concatMap, den_fdot, den_homT]
  have h1 : ⟦inl A B ⨟ pureT (A ⊕' B)⟧ₜ = fun a => ([Sum.inl a] : List ⟦A ⊕' B⟧) := rfl
  have h2 : ⟦(inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B)).homT⟧ₜ
      = fun p : ⟦B⟧ × List ⟦A⟧ => Sum.inr p.1 :: p.2.map Sum.inl := by
    funext p
    simp only [den_fdot, den_homT, h1, den_comp, den_inr, den_pureT, h3]
    rfl
  rw [h1, h2, h3]
  rfl

@[simp] theorem splitDen_nil {α β : Type} :
    splitDen ([] : List (α ⊕ β)) = ([], []) := rfl

@[simp] theorem splitDen_inl {α β : Type} (a : α) (t : List (α ⊕ β)) :
    splitDen (Sum.inl a :: t) = (a :: (splitDen t).1, (splitDen t).2) := rfl

@[simp] theorem splitDen_inr {α β : Type} (b : β) (t : List (α ⊕ β)) :
    splitDen (Sum.inr b :: t) = ([], (b, (splitDen t).1) :: (splitDen t).2) := rfl

theorem splitDen_map_inl_append {α β : Type} (l : List α) (r : List (α ⊕ β)) :
    splitDen (l.map Sum.inl ++ r) = (l ++ (splitDen r).1, (splitDen r).2) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.cons_append, splitDen_inl, ih]

@[simp] theorem splitDen_unsplitDen {α β : Type} (x : List α × List (β × List α)) :
    splitDen (unsplitDen x) = x := by
  obtain ⟨l, ls⟩ := x
  have key : ∀ ls : List (β × List α),
      splitDen ((ls.map (fun p => Sum.inr p.1 :: p.2.map Sum.inl)).flatten) = ([], ls) := by
    intro ls
    induction ls with
    | nil => rfl
    | cons p ps ih =>
      obtain ⟨b, l'⟩ := p
      simp only [List.map_cons, List.flatten_cons, List.cons_append, splitDen_inr,
        splitDen_map_inl_append, ih]
      simp
  simp only [unsplitDen, splitDen_map_inl_append, key]
  simp

@[simp] theorem unsplitDen_splitDen {α β : Type} (l : List (α ⊕ β)) :
    unsplitDen (splitDen l) = l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    cases x with
    | inl a =>
      simp only [splitDen_inl, unsplitDen, List.map_cons, List.cons_append]
      exact congrArg _ ih
    | inr b =>
      simp only [splitDen_inr, unsplitDen, List.map_nil, List.nil_append, List.map_cons,
        List.flatten_cons, List.cons_append]
      exact congrArg _ ih

/-! ### Flattening -/

theorem flatten_map_pure {α : Type} (l : List α) : (l.map (fun a => [a])).flatten = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.flatten_cons, ih, List.cons_append,
      List.nil_append]

theorem flatten_map_nil {α β : Type} (l : List α) :
    (l.map (fun _ => ([] : List β))).flatten = [] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.flatten_cons, ih, List.nil_append]

/-! ### `unsnoc` -/

theorem unsnocDen_map {α β : Type} (f : α → β) (l : List α) :
    unsnocDen (l.map f) =
      Sum.map _root_.id (fun p : List α × α => (p.1.map f, f p.2)) (unsnocDen l) := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
  · subst h; rfl
  · rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
      unsnocDen_append_singleton, unsnocDen_append_singleton]
    rfl

/-! ### `shiftR` and `shiftL` -/

@[simp] theorem shiftRDen_nil {α β : Type} (a : α) :
    shiftRDen ([] : List (α × β)) a = (a, []) := rfl

@[simp] theorem shiftRDen_cons {α β : Type} (a₁ : α) (b₁ : β) (t : List (α × β)) (a : α) :
    shiftRDen ((a₁, b₁) :: t) a = (a₁, (b₁, (shiftRDen t a).1) :: (shiftRDen t a).2) := rfl

@[simp] theorem shiftLDen_nil {α β : Type} (a : α) :
    shiftLDen a ([] : List (β × α)) = ([], a) := rfl

@[simp] theorem shiftLDen_cons {α β : Type} (a : α) (b₁ : β) (a₂ : α) (t : List (β × α)) :
    shiftLDen a ((b₁, a₂) :: t) =
      ((a, b₁) :: (shiftLDen a₂ t).1, (shiftLDen a₂ t).2) := rfl

theorem shiftLDen_shiftRDen {α β : Type} (l : List (α × β)) (a : α) :
    shiftLDen (shiftRDen l a).1 (shiftRDen l a).2 = (l, a) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a₁, b₁⟩ := p
    simp only [shiftRDen_cons, shiftLDen_cons, ih]

theorem shiftRDen_shiftLDen {α β : Type} (a : α) (l : List (β × α)) :
    shiftRDen (shiftLDen a l).1 (shiftLDen a l).2 = (a, l) := by
  induction l generalizing a with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨b₁, a₂⟩ := p
    simp only [shiftLDen_cons, shiftRDen_cons, ih]

theorem shiftRDen_map {α α' β β' : Type} (f : α → α') (g : β → β') (l : List (α × β))
    (a : α) :
    shiftRDen (l.map (fun p => (f p.1, g p.2))) (f a) =
      (f (shiftRDen l a).1, (shiftRDen l a).2.map (fun p => (g p.1, f p.2))) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a₁, b₁⟩ := p
    simp only [List.map_cons, shiftRDen_cons, ih]

theorem shiftLDen_map {α α' β β' : Type} (f : α → α') (g : β → β') (a : α)
    (l : List (β × α)) :
    shiftLDen (f a) (l.map (fun p => (g p.1, f p.2))) =
      ((shiftLDen a l).1.map (fun p => (f p.1, g p.2)), f (shiftLDen a l).2) := by
  induction l generalizing a with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨b₁, a₂⟩ := p
    simp only [List.map_cons, shiftLDen_cons, ih]

/-! ### Naturality of `split` -/

theorem splitDen_map {α α' β β' : Type} (f : α → α') (g : β → β') (l : List (α ⊕ β)) :
    splitDen (l.map (Sum.map f g)) =
      ((splitDen l).1.map f, (splitDen l).2.map (fun p => (g p.1, p.2.map f))) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    cases x with
    | inl a => simp only [List.map_cons, Sum.map_inl, splitDen_inl, ih]
    | inr b => simp only [List.map_cons, Sum.map_inr, splitDen_inr, ih, List.map_nil]

/-! ### The group prefix operation and its inverse -/

/-- The semantics of `unpref`: the inverse of the prefix multiplication. -/
def unprefDen {α G : Type} [Group G] : G → List (α × G) → List (α × G)
  | _, [] => []
  | acc, (a, g) :: t => (a, acc⁻¹ * g) :: unprefDen g t

@[simp] theorem unprefDen_nil {α G : Type} [Group G] (acc : G) :
    unprefDen acc ([] : List (α × G)) = [] := rfl

@[simp] theorem unprefDen_cons {α G : Type} [Group G] (acc : G) (a : α) (g : G)
    (t : List (α × G)) :
    unprefDen acc ((a, g) :: t) = (a, acc⁻¹ * g) :: unprefDen g t := rfl

@[simp] theorem prefixMul_nil {α G : Type} [Mul G] (acc : G) :
    prefixMul acc ([] : List (α × G)) = [] := rfl

@[simp] theorem prefixMul_cons {α G : Type} [Mul G] (acc : G) (a : α) (g : G)
    (t : List (α × G)) :
    prefixMul acc ((a, g) :: t) = (a, acc * g) :: prefixMul (acc * g) t := rfl

theorem unprefDen_prefixMul {α G : Type} [Group G] (acc : G) (l : List (α × G)) :
    unprefDen acc (prefixMul acc l) = l := by
  induction l generalizing acc with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, g⟩ := p
    simp [ih]

theorem prefixMul_unprefDen {α G : Type} [Group G] (acc : G) (l : List (α × G)) :
    prefixMul acc (unprefDen acc l) = l := by
  induction l generalizing acc with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, g⟩ := p
    simp only [unprefDen_cons, prefixMul_cons, mul_inv_cancel_left, ih]

/-! ### Denotations of the auxiliary terms for finite alphabets -/

@[simp] theorem den_constFin : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) → (constFin g).den () = g
  | 0, () => rfl
  | (_ + 1), .inl () => rfl
  | (n + 1), .inr g => by
    show Sum.inr ((constFin g).den ()) = Sum.inr g
    rw [den_constFin g]

@[simp] theorem den_caseR : {n : ℕ} → {A B : Ty} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (a : ⟦A⟧) → (g : ⟦Ty.finAlph n⟧) → (caseR t).den (a, g) = (t g).den a
  | 0, _, _, _, _, () => rfl
  | (_ + 1), _, _, _, _, .inl () => rfl
  | (_ + 1), _, _, t, a, .inr g => den_caseR (fun g => t (.inr g)) a g

@[simp] theorem den_caseL : {n : ℕ} → {A B : Ty} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (a : ⟦A⟧) → (g : ⟦Ty.finAlph n⟧) → (caseL t).den (g, a) = (t g).den a
  | 0, _, _, _, _, () => rfl
  | (_ + 1), _, _, _, _, .inl () => rfl
  | (_ + 1), _, _, t, a, .inr g => den_caseL (fun g => t (.inr g)) a g

@[simp] theorem den_grepeat (A : Ty) (n : ℕ) (a : ⟦A⟧) (g : ⟦Ty.finAlph n⟧) :
    (grepeat A n).den (a, g) = (g, (a, g)) := by
  simp [grepeat]

@[simp] theorem den_gdiv (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (h g : ⟦Ty.finAlph n⟧)
    (a : ⟦A⟧) :
    (gdiv A G).den (h, (g, a)) = (a, letI := G; h⁻¹ * g) := by
  simp [gdiv]

theorem den_unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (l : List (⟦A⟧ × ⟦Ty.finAlph n⟧)) :
    (unpref A G).den l = letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧) l := by
  letI := G
  have key : ∀ (acc : ⟦Ty.finAlph n⟧) (l : List (⟦A⟧ × ⟦Ty.finAlph n⟧)),
      ((shiftLDen acc (l.map (fun p => ((p.2, p.1), p.2)))).1).map
        (fun q : ⟦Ty.finAlph n⟧ × (⟦Ty.finAlph n⟧ × ⟦A⟧) => (q.2.2, q.1⁻¹ * q.2.1)) =
        unprefDen acc l := by
    intro acc l
    induction l generalizing acc with
    | nil => rfl
    | cons p t ih =>
      obtain ⟨a, g⟩ := p
      simp only [List.map_cons, shiftLDen_cons, List.map_cons, ih, unprefDen_cons]
  have hg : (gdiv A G).den =
      fun q : ⟦Ty.finAlph n⟧ × (⟦Ty.finAlph n⟧ × ⟦A⟧) => (q.2.2, q.1⁻¹ * q.2.1) := by
    funext q
    obtain ⟨h, g, a⟩ := q
    exact den_gdiv A G h g a
  have hl : (l.map (grepeat A n).den).map (assocL (Ty.finAlph n) A (Ty.finAlph n)).den =
      l.map (fun p => ((p.2, p.1), p.2)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    obtain ⟨a, g⟩ := p
    simp
  show ((shiftLDen ((constFin (1 : ⟦Ty.finAlph n⟧)).den ())
      ((l.map (grepeat A n).den).map (assocL (Ty.finAlph n) A (Ty.finAlph n)).den)).1).map
      (gdiv A G).den = unprefDen 1 l
  rw [den_constFin, hg, hl, key]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
