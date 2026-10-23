import Lax149335Proofs.RationalFunctions.Types

/-!
# Simple rational functions (Sections 2.3, 2.4 and 2.5)

This file contains the "baby version" of the equational theory: simple rational terms
(Definition 2.5), the equational theory `≃ₛ` for them, the conjugacy completeness theorem
(Theorem 2.6) together with Claim 2.7 that is used in its proof, the decidability corollary
(Corollary 2.8), and the simplification theorem (Theorem 2.9).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace SimpleTerm

variable {Bs : Type}

/-- Soundness of the rules of Theorem 2.6: provably equal simple rational terms define the
same function.  The only interesting case is the conjugacy rule, which is proved by induction
on the length of the input list. -/
theorem SEq.sound {Bs : Type} {A : Ty} {f g : SimpleTerm Bs A}
    (h : SEq f g) : f.den = g.den := by
  induction h with
  | refl f => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr_either _ _ ih₁ ih₂ =>
      funext x
      match x with
      | .inl a => exact congrFun ih₁ a
      | .inr b => exact congrFun ih₂ b
  | congr_conc _ _ ih₁ ih₂ =>
      funext x
      show den _ x.1 ++ den _ x.2 = den _ x.1 ++ den _ x.2
      rw [congrFun ih₁ x.1, congrFun ih₂ x.2]
  | congr_hom _ ih =>
      funext l
      show (l.map (den _)).flatten = (l.map (den _)).flatten
      rw [ih]
  | congr_pre w _ ih =>
      funext a
      show w ++ den _ a = w ++ den _ a
      rw [congrFun ih a]
  | congr_post w _ ih =>
      funext a
      show den _ a ++ w = den _ a ++ w
      rw [congrFun ih a]
  | post_post f w v => funext a; exact List.append_assoc _ _ _
  | pre_pre f w v => funext a; exact (List.append_assoc _ _ _).symm
  | post_nil f => funext a; exact List.append_nil _
  | pre_nil f => funext a; exact List.nil_append _
  | pre_post f w v => funext a; exact List.append_assoc _ _ _
  | conc_shift f g w => funext x; exact List.append_assoc _ _ _
  | @case_left A₁ A₂ A f₁ g₁ f₂ g₂ h _ ih =>
      funext x
      obtain ⟨s, c⟩ := x
      match s with
      | .inl a => exact congrFun ih (.inl (a, c))
      | .inr b => exact congrFun ih (.inr (b, c))
  | @case_right A₁ A₂ A f₁ g₁ f₂ g₂ h _ ih =>
      funext x
      obtain ⟨c, s⟩ := x
      match s with
      | .inl a => exact congrFun ih (.inl (c, a))
      | .inr b => exact congrFun ih (.inr (c, b))
  | @conjugacy A f g w _ ih =>
      funext l
      show (l.map (den f)).flatten ++ w = w ++ (l.map (den g)).flatten
      have hfg : ∀ a, den f a ++ w = w ++ den g a := fun a => congrFun ih a
      induction l with
      | nil => simp
      | cons a t iht =>
          show (den f a ++ (t.map (den f)).flatten) ++ w =
            w ++ (den g a ++ (t.map (den g)).flatten)
          calc (den f a ++ (t.map (den f)).flatten) ++ w
              = den f a ++ ((t.map (den f)).flatten ++ w) := List.append_assoc _ _ _
            _ = den f a ++ (w ++ (t.map (den g)).flatten) := by rw [iht]
            _ = (den f a ++ w) ++ (t.map (den g)).flatten :=
                (List.append_assoc _ _ _).symm
            _ = (w ++ den g a) ++ (t.map (den g)).flatten := by rw [hfg a]
            _ = w ++ (den g a ++ (t.map (den g)).flatten) := List.append_assoc _ _ _
  | move_empty w =>
      funext a
      show den (Bs := Bs) .empty a ++ w = w ++ den (Bs := Bs) .empty a
      simp [den]
  | pre_either w f₁ f₂ =>
      funext x
      match x with
      | .inl a => rfl
      | .inr b => rfl
  | post_either w f₁ f₂ =>
      funext x
      match x with
      | .inl a => rfl
      | .inr b => rfl
  | pre_conc w f₁ f₂ =>
      funext x
      exact (List.append_assoc _ _ _).symm
  | post_conc w f₁ f₂ =>
      funext x
      exact List.append_assoc _ _ _

/-! ### Completeness of the rules of Theorem 2.6

The proof is by induction on the input type.  The rules for moving string constants
(`move_empty`, `pre_conc`, `post_conc`, `pre_either`, `post_either`) make it possible to
normalise a term according to its input type: a term with input
type `1` is a constant, a term with a co-product input type is a co-pairing, a term with a
product input type is a concatenation, and a term with a list input type is a homomorphism
with a constant on each side.  The induction step for products and the one for lists then
follow from Levi's lemma for strings, the latter using the conjugacy rule. -/

instance instTransSEq {Bs : Type} {A : Ty} :
    Trans (α := SimpleTerm Bs A) (@SEq Bs A) (@SEq Bs A) (@SEq Bs A) := ⟨SEq.trans⟩

/-- A term with input type `1` is a constant. -/
theorem norm_unit {Bs : Type} : (f : SimpleTerm Bs Ty.unit) → ∃ w, f ≃ₛ .pre w .empty
  | .empty => ⟨[], (SEq.pre_nil _).symm⟩
  | .pre w f => by
      obtain ⟨v, hv⟩ := norm_unit f
      exact ⟨w ++ v, (SEq.congr_pre w hv).trans (SEq.pre_pre _ _ _)⟩
  | .post f w => by
      obtain ⟨v, hv⟩ := norm_unit f
      refine ⟨v ++ w, ?_⟩
      calc (SimpleTerm.post f w) ≃ₛ SimpleTerm.post (.pre v .empty) w := SEq.congr_post w hv
        _ ≃ₛ SimpleTerm.pre v (.post .empty w) := SEq.pre_post _ _ _
        _ ≃ₛ SimpleTerm.pre v (.pre w .empty) :=
            SEq.congr_pre v (SEq.move_empty w)
        _ ≃ₛ SimpleTerm.pre (v ++ w) .empty := SEq.pre_pre _ _ _

/-- A term with a co-product input type is a co-pairing. -/
theorem norm_sum {Bs : Type} : {A₁ A₂ : Ty} → (f : SimpleTerm Bs (A₁ ⊕' A₂)) →
    ∃ f₁ f₂, f ≃ₛ .either f₁ f₂
  | _, _, .either f₁ f₂ => ⟨f₁, f₂, SEq.refl _⟩
  | _, _, .pre w f => by
      obtain ⟨f₁, f₂, hf⟩ := norm_sum f
      exact ⟨.pre w f₁, .pre w f₂,
        (SEq.congr_pre w hf).trans (SEq.pre_either w f₁ f₂)⟩
  | _, _, .post f w => by
      obtain ⟨f₁, f₂, hf⟩ := norm_sum f
      exact ⟨.post f₁ w, .post f₂ w,
        (SEq.congr_post w hf).trans (SEq.post_either w f₁ f₂)⟩

/-- A term with a product input type is a concatenation. -/
theorem norm_prod {Bs : Type} : {A₁ A₂ : Ty} → (f : SimpleTerm Bs (A₁ ⊗ A₂)) →
    ∃ f₁ f₂, f ≃ₛ .conc f₁ f₂
  | _, _, .conc f₁ f₂ => ⟨f₁, f₂, SEq.refl _⟩
  | _, _, .pre w f => by
      obtain ⟨f₁, f₂, hf⟩ := norm_prod f
      exact ⟨.pre w f₁, f₂, (SEq.congr_pre w hf).trans (SEq.pre_conc w f₁ f₂)⟩
  | _, _, .post f w => by
      obtain ⟨f₁, f₂, hf⟩ := norm_prod f
      exact ⟨f₁, .post f₂ w, (SEq.congr_post w hf).trans (SEq.post_conc w f₁ f₂)⟩

/-- A term with a list input type is a homomorphism with a constant on each side. -/
theorem norm_list {Bs : Type} : {A : Ty} → (f : SimpleTerm Bs A⋆) →
    ∃ (w : List Bs) (h : SimpleTerm Bs A) (v : List Bs), f ≃ₛ .pre w (.post (.hom h) v)
  | _, .hom h => ⟨[], h, [], ((SEq.pre_nil _).trans (SEq.post_nil _)).symm⟩
  | _, .pre u f => by
      obtain ⟨w, h, v, hf⟩ := norm_list f
      exact ⟨u ++ w, h, v, (SEq.congr_pre u hf).trans (SEq.pre_pre _ _ _)⟩
  | _, .post f u => by
      obtain ⟨w, h, v, hf⟩ := norm_list f
      refine ⟨w, h, v ++ u, ?_⟩
      calc (SimpleTerm.post f u) ≃ₛ SimpleTerm.post (.pre w (.post (.hom h) v)) u :=
            SEq.congr_post u hf
        _ ≃ₛ SimpleTerm.pre w (.post (.post (.hom h) v) u) := SEq.pre_post _ _ _
        _ ≃ₛ SimpleTerm.pre w (.post (.hom h) (v ++ u)) :=
            SEq.congr_pre w (SEq.post_post _ _ _)

/-- Completeness of the rules of Theorem 2.6, by induction on the input type. -/
theorem complete_of_den_eq {Bs : Type} :
    (A : Ty) → (f g : SimpleTerm Bs A) → f.den = g.den → f ≃ₛ g
  | .unit, f, g, h => by
      obtain ⟨w, hw⟩ := norm_unit f
      obtain ⟨v, hv⟩ := norm_unit g
      have h1 : (SimpleTerm.pre w (.empty : SimpleTerm Bs Ty.unit)).den =
          (SimpleTerm.pre v (.empty : SimpleTerm Bs Ty.unit)).den := by
        rw [← SEq.sound hw, ← SEq.sound hv]; exact h
      have h2 : w = v := by
        have h3 := congrFun h1 ()
        simpa [den] using h3
      subst h2
      exact hw.trans hv.symm
  | .sum A₁ A₂, f, g, h => by
      obtain ⟨f₁, f₂, hf⟩ := norm_sum f
      obtain ⟨g₁, g₂, hg⟩ := norm_sum g
      have h1 : (SimpleTerm.either f₁ f₂).den = (SimpleTerm.either g₁ g₂).den := by
        rw [← SEq.sound hf, ← SEq.sound hg]; exact h
      have e₁ : f₁.den = g₁.den := by funext a; exact congrFun h1 (.inl a)
      have e₂ : f₂.den = g₂.den := by funext b; exact congrFun h1 (.inr b)
      exact hf.trans ((SEq.congr_either (complete_of_den_eq A₁ f₁ g₁ e₁)
        (complete_of_den_eq A₂ f₂ g₂ e₂)).trans hg.symm)
  | .prod A₁ A₂, f, g, h => by
      obtain ⟨F₁, F₂, hf⟩ := norm_prod f
      obtain ⟨G₁, G₂, hg⟩ := norm_prod g
      have h1 : (SimpleTerm.conc F₁ F₂).den = (SimpleTerm.conc G₁ G₂).den := by
        rw [← SEq.sound hf, ← SEq.sound hg]; exact h
      have hFG : ∀ (a : ⟦A₁⟧) (b : ⟦A₂⟧), F₁.den a ++ F₂.den b = G₁.den a ++ G₂.den b :=
        fun a b => congrFun h1 (a, b)
      rcases List.append_eq_append_iff.1 (hFG (Ty.someElem A₁) (Ty.someElem A₂)) with
        ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
      · -- the second term produces `x` more on the left component
        have hF₂ : ∀ b, F₂.den b = x ++ G₂.den b := by
          intro b
          have h5 := hFG (Ty.someElem A₁) b
          rw [hx1, List.append_assoc] at h5
          exact List.append_cancel_left h5
        have hG₁ : ∀ a, G₁.den a = F₁.den a ++ x := by
          intro a
          have h5 := hFG a (Ty.someElem A₂)
          rw [hF₂ (Ty.someElem A₂)] at h5
          simp only [← List.append_assoc] at h5
          exact (List.append_cancel_right h5).symm
        have e₂ : F₂.den = (SimpleTerm.pre x G₂).den := by funext b; exact hF₂ b
        have e₁ : G₁.den = (SimpleTerm.post F₁ x).den := by funext a; exact hG₁ a
        calc f ≃ₛ SimpleTerm.conc F₁ F₂ := hf
          _ ≃ₛ SimpleTerm.conc F₁ (.pre x G₂) :=
              SEq.congr_conc (SEq.refl _) (complete_of_den_eq A₂ _ _ e₂)
          _ ≃ₛ SimpleTerm.conc (.post F₁ x) G₂ := (SEq.conc_shift F₁ G₂ x).symm
          _ ≃ₛ SimpleTerm.conc G₁ G₂ :=
              SEq.congr_conc (complete_of_den_eq A₁ _ _ e₁).symm (SEq.refl _)
          _ ≃ₛ g := hg.symm
      · -- the first term produces `x` more on the left component
        have hG₂ : ∀ b, G₂.den b = x ++ F₂.den b := by
          intro b
          have h5 := hFG (Ty.someElem A₁) b
          rw [hx1, List.append_assoc] at h5
          exact (List.append_cancel_left h5).symm
        have hF₁ : ∀ a, F₁.den a = G₁.den a ++ x := by
          intro a
          have h5 := hFG a (Ty.someElem A₂)
          rw [hG₂ (Ty.someElem A₂)] at h5
          simp only [← List.append_assoc] at h5
          exact List.append_cancel_right h5
        have e₁ : F₁.den = (SimpleTerm.post G₁ x).den := by funext a; exact hF₁ a
        have e₂ : G₂.den = (SimpleTerm.pre x F₂).den := by funext b; exact hG₂ b
        calc f ≃ₛ SimpleTerm.conc F₁ F₂ := hf
          _ ≃ₛ SimpleTerm.conc (.post G₁ x) F₂ :=
              SEq.congr_conc (complete_of_den_eq A₁ _ _ e₁) (SEq.refl _)
          _ ≃ₛ SimpleTerm.conc G₁ (.pre x F₂) := SEq.conc_shift G₁ F₂ x
          _ ≃ₛ SimpleTerm.conc G₁ G₂ :=
              SEq.congr_conc (SEq.refl _) (complete_of_den_eq A₂ _ _ e₂).symm
          _ ≃ₛ g := hg.symm
  | .list A, f, g, h => by
      obtain ⟨w, F, v, hf⟩ := norm_list f
      obtain ⟨w', G, v', hg⟩ := norm_list g
      have h1 : (SimpleTerm.pre w (.post (.hom F) v)).den =
          (SimpleTerm.pre w' (.post (.hom G) v')).den := by
        rw [← SEq.sound hf, ← SEq.sound hg]; exact h
      have hden : ∀ l : List ⟦A⟧,
          w ++ ((l.map F.den).flatten ++ v) = w' ++ ((l.map G.den).flatten ++ v') :=
        fun l => congrFun h1 l
      have h0 : w ++ v = w' ++ v' := by simpa using hden []
      rcases List.append_eq_append_iff.1 h0 with ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
      · -- the second constant on the left is longer by `x`
        subst hx1; subst hx2
        have hconj : ∀ a, F.den a ++ x = x ++ G.den a := by
          intro a
          have h2 := hden [a]
          simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, ← List.append_assoc] at h2
          have h4 := List.append_cancel_right h2
          simp only [List.append_assoc] at h4
          exact List.append_cancel_left h4
        have hc : (SimpleTerm.post F x).den = (SimpleTerm.pre x G).den := by
          funext a; exact hconj a
        have hhom : SimpleTerm.post (.hom F) x ≃ₛ SimpleTerm.pre x (.hom G) :=
          SEq.conjugacy x (complete_of_den_eq A _ _ hc)
        calc f ≃ₛ SimpleTerm.pre w (.post (.hom F) (x ++ v')) := hf
          _ ≃ₛ SimpleTerm.pre w (.post (.post (.hom F) x) v') :=
              SEq.congr_pre w (SEq.post_post _ _ _).symm
          _ ≃ₛ SimpleTerm.pre w (.post (.pre x (.hom G)) v') :=
              SEq.congr_pre w (SEq.congr_post v' hhom)
          _ ≃ₛ SimpleTerm.pre w (.pre x (.post (.hom G) v')) :=
              SEq.congr_pre w (SEq.pre_post _ _ _)
          _ ≃ₛ SimpleTerm.pre (w ++ x) (.post (.hom G) v') := SEq.pre_pre _ _ _
          _ ≃ₛ g := hg.symm
      · -- the first constant on the left is longer by `x`
        subst hx1; subst hx2
        have hconj : ∀ a, G.den a ++ x = x ++ F.den a := by
          intro a
          have h2 := hden [a]
          simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, ← List.append_assoc] at h2
          have h4 := List.append_cancel_right h2
          simp only [List.append_assoc] at h4
          exact (List.append_cancel_left h4).symm
        have hc : (SimpleTerm.post G x).den = (SimpleTerm.pre x F).den := by
          funext a; exact hconj a
        have hhom : SimpleTerm.post (.hom G) x ≃ₛ SimpleTerm.pre x (.hom F) :=
          SEq.conjugacy x (complete_of_den_eq A _ _ hc)
        refine SEq.symm ?_
        calc g ≃ₛ SimpleTerm.pre w' (.post (.hom G) (x ++ v)) := hg
          _ ≃ₛ SimpleTerm.pre w' (.post (.post (.hom G) x) v) :=
              SEq.congr_pre w' (SEq.post_post _ _ _).symm
          _ ≃ₛ SimpleTerm.pre w' (.post (.pre x (.hom F)) v) :=
              SEq.congr_pre w' (SEq.congr_post v hhom)
          _ ≃ₛ SimpleTerm.pre w' (.pre x (.post (.hom F) v)) :=
              SEq.congr_pre w' (SEq.pre_post _ _ _)
          _ ≃ₛ SimpleTerm.pre (w' ++ x) (.post (.hom F) v) := SEq.pre_pre _ _ _
          _ ≃ₛ f := hf.symm

/-- Completeness of the rules of Theorem 2.6. -/
theorem SEq.complete {Bs : Type} {A : Ty} (f g : SimpleTerm Bs A) (h : f.den = g.den) :
    f ≃ₛ g := complete_of_den_eq A f g h

/-- **Theorem 2.6 (Conjugacy completeness).**  Two simple rational terms define the same
function if and only if their equality can be proved using the rules of the theorem:
congruence, concatenation monoidality, constants and copairing, case splitting and
conjugacy. -/
theorem conjugacy_completeness {Bs : Type} {A : Ty} (f g : SimpleTerm Bs A) :
    f.den = g.den ↔ f ≃ₛ g :=
  ⟨SEq.complete f g, SEq.sound⟩

/-- **Claim 2.7.**  In the situation of the induction step for products in the proof of
Theorem 2.6, i.e. for two terms
`f = w₀ · (hom f₁ · w₁) ⋯ (hom fₙ · wₙ)` and `g = v₀ · (hom g₁ · v₁) ⋯ (hom gₙ · vₙ)`
that define the same function, for every `i ∈ {1,…,n}` and every `a ∈ Aᵢ` the strings
`fᵢ(a)` and `gᵢ(a)` have the same length. -/
theorem claim_same_lengths {Bs : Type} : {As : List Ty} → (F G : HomList Bs As) →
    (w₀ v₀ : List Bs) →
    (SimpleTerm.pre w₀ F.term).den = (SimpleTerm.pre v₀ G.term).den →
    F.SameLengths G
  | [], .nil, .nil, _, _, _ => trivial
  | (A :: As), .cons f w F', .cons g v G', w₀, v₀, h => by
      refine ⟨?_, ?_⟩
      · -- the first components: compare the outputs on the empty list and on a one element
        -- list in the first component
        intro a
        have e₀ := congrFun h (([] : List ⟦A⟧), Ty.someElem (prodListTy As))
        have e₁ := congrFun h (([a] : List ⟦A⟧), Ty.someElem (prodListTy As))
        have l₀ := congrArg List.length e₀
        have l₁ := congrArg List.length e₁
        simp [SimpleTerm.den, HomList.term] at l₀ l₁
        omega
      · -- the remaining components: restrict to inputs whose first component is empty
        refine claim_same_lengths F' G' (w₀ ++ w) (v₀ ++ v) ?_
        funext rest
        have hr := congrFun h (([] : List ⟦A⟧), rest)
        simpa [SimpleTerm.den, HomList.term] using hr

/-! **Corollary 2.8** (equivalence for simple rational functions is decidable; the paper
shows moreover that it is decidable in polynomial time, which is not expressible here) is
stated and proved in `Lax149335Proofs.RationalFunctions.Decidability`, as
`Lax149335Proofs.SimpleTerm.decidableDenEq`.  Asking for a `Decidable` instance rather than for
the — classically trivial — proposition "equality of denotations is decidable" forces an
actual algorithm to be supplied, and the algorithm needs the decomposition of a simple
rational term according to its input type, which is developed in that file. -/

end SimpleTerm

end Lax149335Proofs

bridge_export Lax149335Proofs
