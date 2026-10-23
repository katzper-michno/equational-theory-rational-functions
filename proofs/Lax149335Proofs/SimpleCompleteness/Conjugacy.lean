import Lax149335Proofs.SimpleCompleteness.Bridge
import Lax149335Proofs.Appendix.Bundles.Composition

/-!
# Towards the conjugacy rule of Lemma 6.1

This file collects the equational material used by the proof of the conjugacy rule (18) of
Lemma 6.1: the interaction of the concatenation maps with the homomorphism combinator, the
closure properties of conjugacy, and the terms that are *provably equal* to a simple rational
term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Terms that are provably equal to a simple rational term

The constructions in the proof of Lemma 6.1 produce terms that are provably, but not
syntactically, simple; the following class is what the completeness rule is applied to. -/

/-- A term is *equationally simple* if it is provably equal to a simple rational term. -/
def EqSimple (B : Ty) {A : Ty} (f : Term A B⋆) : Prop := ∃ s : Term A B⋆, IsSimple B s ∧ f ≡ₜ s

namespace EqSimple

variable {A B : Ty}

theorem of_isSimple {f : Term A B⋆} (hf : IsSimple B f) : EqSimple B f := ⟨f, hf, PEq.refl f⟩

theorem congr {f g : Term A B⋆} (h : f ≡ₜ g) (hg : EqSimple B g) : EqSimple B f := by
  obtain ⟨s, hs, hgs⟩ := hg
  exact ⟨s, hs, h.trans hgs⟩

theorem either {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : EqSimple B f₁) (h₂ : EqSimple B f₂) : EqSimple B (Term.either f₁ f₂) := by
  obtain ⟨s₁, hs₁, he₁⟩ := h₁
  obtain ⟨s₂, hs₂, he₂⟩ := h₂
  exact ⟨Term.either s₁ s₂, IsSimple.either hs₁ hs₂, Term.either_congr he₁ he₂⟩

theorem fdot {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : EqSimple B f₁) (h₂ : EqSimple B f₂) : EqSimple B (f₁ ⊙ f₂) := by
  obtain ⟨s₁, hs₁, he₁⟩ := h₁
  obtain ⟨s₂, hs₂, he₂⟩ := h₂
  exact ⟨s₁ ⊙ s₂, IsSimple.fdot hs₁ hs₂, Term.fdot_congr he₁ he₂⟩

theorem hom {f : Term A B⋆} (h : EqSimple B f) : EqSimple B (homT f) := by
  obtain ⟨s, hs, he⟩ := h
  exact ⟨homT s, IsSimple.hom hs, Term.homT_congr he⟩

theorem dotL {f : Term A B⋆} (w : Value B⋆) (h : EqSimple B f) : EqSimple B (Term.dotL w f) := by
  obtain ⟨s, hs, he⟩ := h
  exact ⟨Term.dotL w s, IsSimple.dotL w hs, Term.dotL_congr (PEq.refl _) he⟩

theorem dotR {f : Term A B⋆} (w : Value B⋆) (h : EqSimple B f) : EqSimple B (Term.dotR f w) := by
  obtain ⟨s, hs, he⟩ := h
  exact ⟨Term.dotR s w, IsSimple.dotR w hs, Term.dotR_congr he (PEq.refl _)⟩

/-- The constantly empty term is equationally simple, for every input type. -/
theorem nilconst : (A : Ty) → (B : Ty) → EqSimple B (toUnit A ⨟ nilT B)
  | .unit, B => ⟨nilT B, IsSimple.nil,
      (PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans (PEq.id_comp _)⟩
  | .prod A₁ A₂, B => by
      refine congr ?_ (fdot (nilconst A₁ B) (nilconst A₂ B))
      refine PEq.symm ?_
      calc ((toUnit A₁ ⨟ nilT B) ⊙ (toUnit A₂ ⨟ nilT B))
          ≡ₜ (fst A₁ A₂ ⨟ (toUnit A₁ ⨟ nilT B)) :=
            prodF_nilconst_binconcat (toUnit A₁ ⨟ nilT B)
        _ ≡ₜ ((fst A₁ A₂ ⨟ toUnit A₁) ⨟ nilT B) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (toUnit (A₁ ⊗ A₂) ⨟ nilT B) :=
            PEq.compL _ (PEq.unit_unique _ _)
  | .sum A₁ A₂, B => by
      refine congr ?_ (either (nilconst A₁ B) (nilconst A₂ B))
      exact PEq.symm (Term.either_nilconst A₁ A₂ B)
  | .list A, B => by
      refine congr ?_ (hom (nilconst A B))
      exact PEq.symm (Term.homT_nilconst A B)

end EqSimple

/-! ### Concatenation maps followed by a homomorphism -/

namespace Term

/-- Whether a shape is free of the list constructor. -/
def TyF.listFree : TyF → Bool
  | .param => true
  | .unit => true
  | .prod F G => TyF.listFree F && TyF.listFree G
  | .sum F G => TyF.listFree F && TyF.listFree G
  | .list _ => false

bridge_export Lax149335Proofs

/-- The term `F(A) → B*` obtained by applying `f` to every entry of an element of `F(A)` and
concatenating the results; this is what a concatenation map followed by the homomorphism
combinator computes. -/
def TyF.homMap : (F : TyF) → {A B : Ty} → Term A B⋆ → Term (F.app A) B⋆
  | .param, _, _, f => f
  | .unit, _, B, _ => nilT B
  | .prod F G, _, _, f => (TyF.homMap F f) ⊙ (TyF.homMap G f)
  | .sum F G, _, _, f => Term.either (TyF.homMap F f) (TyF.homMap G f)
  | .list F, _, _, f => homT (TyF.homMap F f)

bridge_export Lax149335Proofs

/-- A concatenation map followed by a homomorphism applies the homomorphised term to every
entry. -/
theorem TyF.concatMap_homT : (F : TyF) → {A B : Ty} → (f : Term A B⋆) →
    (F.concatMap A ⨟ homT f) ≡ₜ F.homMap f
  | .param, _, _, f => Term.homT_pure f
  | .unit, _, _, f => Term.homT_nil f
  | .prod F G, A, _, f =>
      (Term.fdot_comp_homT (F.concatMap A) (G.concatMap A) f).trans
        (Term.fdot_congr (TyF.concatMap_homT F f) (TyF.concatMap_homT G f))
  | .sum F G, A, _, f =>
      (Term.either_comp (F.concatMap A) (G.concatMap A) (homT f)).trans
        (Term.either_congr (TyF.concatMap_homT F f) (TyF.concatMap_homT G f))
  | .list F, A, _, f =>
      (Term.homT_comp (F.concatMap A) f).trans (Term.homT_congr (TyF.concatMap_homT F f))

bridge_export Lax149335Proofs

/-- Pre-composition in the right factor of a concatenation. -/
theorem fdot_comp_right {W X Y B : Ty} (f : Term W B⋆) (q : Term Y X) (T : Term X B⋆) :
    (prodF (Term.id W) q ⨟ (f ⊙ T)) ≡ₜ (f ⊙ (q ⨟ T)) := by
  calc (prodF (Term.id W) q ⨟ (prodF f T ⨟ binconcat B))
      ≡ₜ ((prodF (Term.id W) q ⨟ prodF f T) ⨟ binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id W ⨟ f) (q ⨟ T) ⨟ binconcat B) := PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (prodF f (q ⨟ T) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))

/-- Pre-composition in the left factor of a concatenation. -/
theorem fdot_comp_left {W X Y B : Ty} (f : Term W B⋆) (q : Term Y X) (T : Term X B⋆) :
    (prodF q (Term.id W) ⨟ (T ⊙ f)) ≡ₜ ((q ⨟ T) ⊙ f) := by
  calc (prodF q (Term.id W) ⨟ (prodF T f ⨟ binconcat B))
      ≡ₜ ((prodF q (Term.id W) ⨟ prodF T f) ⨟ binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (q ⨟ T) (Term.id W ⨟ f) ⨟ binconcat B) := PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (prodF (q ⨟ T) f ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))

end Term

/-! ### Closure properties of provable conjugacy -/

namespace ProvConjugate

variable {A B : Ty}

/-- Provable conjugacy is preserved by the concatenation combinator. -/
theorem fdot {A₁ A₂ : Ty} {w : Value B⋆} {f₁ g₁ : Term A₁ B⋆} {f₂ g₂ : Term A₂ B⋆}
    (h₁ : ProvConjugate w f₁ g₁) (h₂ : ProvConjugate w f₂ g₂) :
    ProvConjugate w (f₁ ⊙ f₂) (g₁ ⊙ g₂) := by
  calc Term.dotR (f₁ ⊙ f₂) w
      ≡ₜ (f₁ ⊙ Term.dotR f₂ w) := PEq.symm (Term.dotR_fdot f₁ f₂ w)
    _ ≡ₜ (f₁ ⊙ Term.dotL w g₂) := Term.fdot_congr (PEq.refl _) h₂
    _ ≡ₜ (Term.dotR f₁ w ⊙ g₂) := PEq.symm (Term.fdot_dotR_dotL f₁ g₂ w)
    _ ≡ₜ (Term.dotL w g₁ ⊙ g₂) := Term.fdot_congr h₁ (PEq.refl _)
    _ ≡ₜ Term.dotL w (g₁ ⊙ g₂) := Term.dotL_fdot w g₁ g₂

/-- Provable conjugacy is preserved by co-pairing. -/
theorem either {A₁ A₂ : Ty} {w : Value B⋆} {f₁ g₁ : Term A₁ B⋆} {f₂ g₂ : Term A₂ B⋆}
    (h₁ : ProvConjugate w f₁ g₁) (h₂ : ProvConjugate w f₂ g₂) :
    ProvConjugate w (Term.either f₁ f₂) (Term.either g₁ g₂) :=
  (Term.dotR_either f₁ f₂ w).trans
    ((Term.either_congr h₁ h₂).trans (PEq.symm (Term.dotL_either w g₁ g₂)))

/-- The constantly empty term is provably conjugate to itself. -/
theorem nilconst (X B : Ty) (w : Value B⋆) :
    ProvConjugate w (toUnit X ⨟ nilT B) (toUnit X ⨟ nilT B) :=
  (Term.dotR_nilconst X B w).trans (PEq.symm (Term.dotL_nilconst X B w))

/-- The empty function is provably conjugate to itself. -/
theorem nil (B : Ty) (w : Value B⋆) : ProvConjugate w (nilT B) (nilT B) := by
  have h : (toUnit Ty.unit ⨟ nilT B) ≡ₜ nilT B :=
    (PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans (PEq.id_comp _)
  refine (Term.dotR_congr (PEq.symm h) (PEq.refl _)).trans ?_
  exact (nilconst Ty.unit B w).trans (Term.dotL_congr (PEq.refl _) h)

/-- Provable conjugacy is preserved by the entrywise application of a list-free shape. -/
theorem homMap : (F : TyF) → F.listFree = true → {w : Value B⋆} → {f g : Term A B⋆} →
    ProvConjugate w f g → ProvConjugate w (F.homMap f) (F.homMap g)
  | .param, _, _, _, _, h => h
  | .unit, _, w, _, _, _ => nil B w
  | .prod F G, hF, _, _, _, h => by
      simp only [Term.TyF.listFree, Bool.and_eq_true] at hF
      exact fdot (homMap F hF.1 h) (homMap G hF.2 h)
  | .sum F G, hF, _, _, _, h => by
      simp only [Term.TyF.listFree, Bool.and_eq_true] at hF
      exact either (homMap F hF.1 h) (homMap G hF.2 h)
  | .list _, hF, _, _, _, _ => by
      exact absurd hF (by simp [Term.TyF.listFree])

bridge_export Lax149335Proofs

/-- The shape `Aᵏ` is free of the list constructor. -/
theorem _root_.Lax149335Proofs.Term.TyF.pow_listFree : (k : ℕ) → (Term.TyF.pow k).listFree = true
  | 0 => rfl
  | (k + 1) => by
      simp only [Term.TyF.pow, Term.TyF.listFree, Bool.and_eq_true]
      exact ⟨trivial, Term.TyF.pow_listFree k⟩

/-- The shape `A^{<k+1}` is free of the list constructor. -/
theorem _root_.Lax149335Proofs.Term.TyF.lt_listFree : (k : ℕ) → (Term.TyF.lt k).listFree = true
  | 0 => rfl
  | (k + 1) => by
      simp only [Term.TyF.lt, Term.TyF.listFree, Bool.and_eq_true]
      exact ⟨Term.TyF.lt_listFree k, Term.TyF.pow_listFree (k + 1)⟩

end ProvConjugate

/-! ### Joint case decompositions

The proof of the conjugacy rule distributes the `k`-fold concatenation of a co-pairing into a
co-pairing of concatenations, and this has to be done *simultaneously* for the two terms `f`
and `g`, since the two are afterwards compared by the completeness rule.  The following
inductive predicate records such a joint decomposition: `JointCases B P T S` says that `T`
and `S` are provably co-pairings, along a common re-organisation of the input type by
provable isomorphisms, of components that are related by `P`. -/

/-- A joint decomposition of two terms into co-pairings of components related by `P`. -/
inductive JointCases (B : Ty) (P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop) :
    {X : Ty} → Term X B⋆ → Term X B⋆ → Prop
  /-- A single component. -/
  | leaf {X : Ty} {T S : Term X B⋆} : P T S → JointCases B P T S
  /-- Two decompositions of the two cases of a co-pairing. -/
  | node {X₁ X₂ : Ty} {T₁ S₁ : Term X₁ B⋆} {T₂ S₂ : Term X₂ B⋆} :
      JointCases B P T₁ S₁ → JointCases B P T₂ S₂ →
      JointCases B P (Term.either T₁ T₂) (Term.either S₁ S₂)
  /-- Re-organising the input type by a provable isomorphism that does not increase the list
  nesting depth. -/
  | precomp {X Y : Ty} {q : Term Y X} {T S : Term X B⋆} : ProvableIso q →
      Y.listDepth ≤ X.listDepth → JointCases B P (q ⨟ T) (q ⨟ S) → JointCases B P T S
  /-- Provable equality of the two terms. -/
  | congr {X : Ty} {T T' S S' : Term X B⋆} : T ≡ₜ T' → S ≡ₜ S' →
      JointCases B P T' S' → JointCases B P T S

namespace JointCases

variable {B : Ty}

/-- A joint decomposition for a weaker relation on the components. -/
theorem mono {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop}
    (h : ∀ {Y : Ty} (T S : Term Y B⋆), P T S → P' T S) :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S → JointCases B P' T S := by
  intro X T S hTS
  induction hTS with
  | leaf hP => exact leaf (h _ _ hP)
  | node _ _ ih₁ ih₂ => exact node ih₁ ih₂
  | precomp hq hd _ ih => exact precomp hq hd ih
  | congr h₁ h₂ _ ih => exact congr h₁ h₂ ih

/-- A property of the denotations that is inherited by the components can be added to the
relation on the components. -/
theorem addDen {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop}
    (QL QR : List ⟦B⟧ → Prop) :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S →
      (∀ x : ⟦X⟧, QL (T.den x)) → (∀ x : ⟦X⟧, QR (S.den x)) →
      JointCases B (fun {Y} T S => P T S ∧ (∀ y : ⟦Y⟧, QL (T.den y)) ∧
        (∀ y : ⟦Y⟧, QR (S.den y))) T S := by
  intro X T S hTS
  induction hTS with
  | leaf hP => exact fun hL hR => leaf ⟨hP, hL, hR⟩
  | node _ _ ih₁ ih₂ =>
      intro hL hR
      exact node (ih₁ (fun x => hL (.inl x)) (fun x => hR (.inl x)))
        (ih₂ (fun x => hL (.inr x)) (fun x => hR (.inr x)))
  | precomp hq hd _ ih =>
      intro hL hR
      exact precomp hq hd (ih (fun y => hL _) (fun y => hR _))
  | congr h₁ h₂ _ ih =>
      intro hL hR
      refine congr h₁ h₂ (ih (fun x => ?_) (fun x => ?_))
      · rw [← congrFun (PEq.sound h₁) x]; exact hL x
      · rw [← congrFun (PEq.sound h₂) x]; exact hR x

/-- The distributivity terms are provable isomorphisms. -/
theorem _root_.Lax149335Proofs.ProvableIso.undistL (A B C : Ty) : ProvableIso (Term.undistL A B C) :=
  ⟨Term.distL A B C, PEq.undistL_distL A B C, PEq.distL_undistL A B C⟩

/-- The distributivity terms are provable isomorphisms. -/
theorem _root_.Lax149335Proofs.ProvableIso.undistR (A B C : Ty) : ProvableIso (Term.undistR A B C) :=
  ⟨Term.distR A B C, PEq.undistR_distR A B C, PEq.distR_undistR A B C⟩

/-- A joint decomposition is preserved by concatenating a fixed pair of terms on the left,
given a joint decomposition of every component after the concatenation. -/
theorem fdot_left {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {W : Ty}
    (f g : Term W B⋆)
    (hstep : ∀ {Y : Ty} (T S : Term Y B⋆), P T S → JointCases B P' (f ⊙ T) (g ⊙ S)) :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S → JointCases B P' (f ⊙ T) (g ⊙ S) := by
  intro X T S hTS
  induction hTS with
  | leaf hP => exact hstep _ _ hP
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      refine congr (Term.fdot_either_distR f T₁ T₂) (Term.fdot_either_distR g S₁ S₂) ?_
      refine precomp (ProvableIso.undistR W X₁ X₂) ?_ ?_
      · simp only [Ty.listDepth]
        omega
      · refine congr ?_ ?_ (node ih₁ ih₂)
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistR_distR W X₁ X₂)).trans (PEq.id_comp _))
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistR_distR W X₁ X₂)).trans (PEq.id_comp _))
  | @precomp X Y q T S hq hd _ ih =>
      refine precomp (ProvableIso.prodF (ProvableIso.id W) hq) ?_ ?_
      · simp only [Ty.listDepth]
        omega
      · refine congr ?_ ?_ ih
        · exact Term.fdot_comp_right f q T
        · exact Term.fdot_comp_right g q S
  | congr h₁ h₂ _ ih =>
      exact congr (Term.fdot_congr (PEq.refl _) h₁) (Term.fdot_congr (PEq.refl _) h₂) ih

end JointCases

/-- A joint decomposition into co-pairings, without any re-organisation of the input type. -/
inductive JointCopairTree (B : Ty) (P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop) :
    {X : Ty} → Term X B⋆ → Term X B⋆ → Prop
  /-- A single component. -/
  | leaf {X : Ty} {T S T' S' : Term X B⋆} : T ≡ₜ T' → S ≡ₜ S' → P T' S' → JointCopairTree B P T S
  /-- Two decompositions of the two cases of a co-pairing. -/
  | node {X₁ X₂ : Ty} {T S : Term (X₁ ⊕' X₂) B⋆} {T₁ S₁ : Term X₁ B⋆} {T₂ S₂ : Term X₂ B⋆} :
      T ≡ₜ Term.either T₁ T₂ → S ≡ₜ Term.either S₁ S₂ →
      JointCopairTree B P T₁ S₁ → JointCopairTree B P T₂ S₂ → JointCopairTree B P T S

namespace JointCopairTree

variable {B : Ty}

/-- Co-pairing decompositions are stable under provable equality. -/
theorem congr {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {X : Ty} {T T' S S' : Term X B⋆}
    (h₁ : T ≡ₜ T') (h₂ : S ≡ₜ S') (h : JointCopairTree B P T' S') : JointCopairTree B P T S := by
  cases h with
  | leaf e₁ e₂ hP => exact leaf (h₁.trans e₁) (h₂.trans e₂) hP
  | node e₁ e₂ h₁' h₂' => exact node (h₁.trans e₁) (h₂.trans e₂) h₁' h₂'

/-- Collapsing a co-pairing decomposition whose components have a common prefix `w` on the
left and a common suffix `w` on the right. -/
theorem collapse {w : Value B⋆} {X : Ty} {T S : Term X B⋆}
    (h : JointCopairTree B (fun {Y} T S => ∃ H H' : Term Y B⋆, EqSimple B H ∧ EqSimple B H' ∧
        T ≡ₜ Term.dotL w H ∧ S ≡ₜ Term.dotR H' w) T S) :
    ∃ H H' : Term X B⋆, EqSimple B H ∧ EqSimple B H' ∧
      T ≡ₜ Term.dotL w H ∧ S ≡ₜ Term.dotR H' w := by
  induction h with
  | leaf e₁ e₂ hP =>
      obtain ⟨H, H', hH, hH', hT, hS⟩ := hP
      exact ⟨H, H', hH, hH', e₁.trans hT, e₂.trans hS⟩
  | node e₁ e₂ _ _ ih₁ ih₂ =>
      obtain ⟨H₁, H₁', hH₁, hH₁', hT₁, hS₁⟩ := ih₁
      obtain ⟨H₂, H₂', hH₂, hH₂', hT₂, hS₂⟩ := ih₂
      refine ⟨Term.either H₁ H₂, Term.either H₁' H₂', EqSimple.either hH₁ hH₂,
        EqSimple.either hH₁' hH₂', ?_, ?_⟩
      · exact e₁.trans ((Term.either_congr hT₁ hT₂).trans
          (PEq.symm (Term.dotL_either w H₁ H₂)))
      · exact e₂.trans ((Term.either_congr hS₁ hS₂).trans
          (PEq.symm (Term.dotR_either H₁' H₂' w)))

end JointCopairTree

namespace JointCases

variable {B : Ty}

/-- Every joint decomposition becomes a plain co-pairing decomposition after a provable
isomorphism of the input type that does not increase the list nesting depth. -/
theorem toIso {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S →
      ∃ (Z : Ty) (p : Term Z X), ProvableIso p ∧ Z.listDepth ≤ X.listDepth ∧
        JointCopairTree B P (p ⨟ T) (p ⨟ S) := by
  intro X T S h
  induction h with
  | @leaf X T S hP =>
      exact ⟨X, Term.id X, ProvableIso.id X, le_rfl,
        JointCopairTree.leaf (PEq.id_comp _) (PEq.id_comp _) hP⟩
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      obtain ⟨Z₁, p₁, hp₁, hd₁, hc₁⟩ := ih₁
      obtain ⟨Z₂, p₂, hp₂, hd₂, hc₂⟩ := ih₂
      refine ⟨Z₁ ⊕' Z₂, Term.sumF p₁ p₂, ProvableIso.sumF hp₁ hp₂, ?_, ?_⟩
      · simp only [Ty.listDepth]
        omega
      · exact JointCopairTree.node (Term.sumF_either p₁ p₂ T₁ T₂) (Term.sumF_either p₁ p₂ S₁ S₂)
          hc₁ hc₂
  | @precomp X Y q T S hq hd _ ih =>
      obtain ⟨Z, p, hp, hdZ, hc⟩ := ih
      refine ⟨Z, p ⨟ q, ProvableIso.comp hp hq, by omega, ?_⟩
      exact JointCopairTree.congr (PEq.comp_assoc _ _ _) (PEq.comp_assoc _ _ _) hc
  | congr h₁ h₂ _ ih =>
      obtain ⟨Z, p, hp, hdZ, hc⟩ := ih
      exact ⟨Z, p, hp, hdZ, JointCopairTree.congr (PEq.compR _ h₁) (PEq.compR _ h₂) hc⟩

end JointCases

/-! ### Products of `k`-guarded terms

The leaves of the joint decomposition produced by the proof of the conjugacy rule are
`k`-fold concatenations of `k`-guarded terms that never produce the empty list. -/

/-- `KProdT k B j T` says that `T` is a `j`-fold concatenation, associated to the right, of
`k`-guarded terms that never produce the empty list. -/
inductive KProdT (k : ℕ) (B : Ty) : ℕ → {Y : Ty} → Term Y B⋆ → Prop
  /-- The empty concatenation. -/
  | nil : KProdT k B 0 (nilT B)
  /-- One more factor, on the left. -/
  | cons {j : ℕ} {Y₁ Y₂ : Ty} {f : Term Y₁ B⋆} {T : Term Y₂ B⋆} :
      KGuarded k B f → NonemptyOutput f → KProdT k B j T → KProdT k B (j + 1) (f ⊙ T)

namespace KProdT

variable {k : ℕ} {B : Ty}

/-- The length of the value obtained by prepending one value to another. -/
theorem _root_.Lax149335Proofs.valLength_dotL (c u : Value B⋆) :
    valLength (Term.dotL c u) = valLength c + valLength u := by
  simp [valLength, Term.den_dotL]

/-- **The prefix of a product of `k`-guarded nonempty terms.**  A `j`-fold concatenation of
`k`-guarded terms with nonempty outputs is provably a value of length at least `min j k`
followed by an equationally simple term. -/
theorem dotL_factor {j : ℕ} : {Y : Ty} → {T : Term Y B⋆} → KProdT k B j T →
    ∃ (u : Value B⋆) (H : Term Y B⋆), min j k ≤ valLength u ∧ EqSimple B H ∧
      T ≡ₜ Term.dotL u H := by
  intro Y T h
  induction h with
  | nil =>
      exact ⟨nilT B, nilT B, by simp, EqSimple.of_isSimple IsSimple.nil,
        PEq.symm (Term.dotL_nil _)⟩
  | @cons j Y₁ Y₂ f T hf hne _ ih =>
      obtain ⟨u', H', hlen, hH', hT'⟩ := ih
      rcases hf with ⟨c, rfl⟩ | ⟨u, v, hh, hsim, hu, -, rfl⟩
      · -- a constant factor: its value is prepended to the prefix of the rest
        have hc : 1 ≤ valLength c := by
          have := hne (Ty.someElem Y₁)
          simp only [Term.den_comp, valLength] at this ⊢
          rcases hd : c.den () with _ | ⟨a, l⟩
          · exact absurd (by simp [hd]) this
          · simp
        refine ⟨Term.dotL c u', (toUnit Y₁ ⨟ nilT B) ⊙ H', ?_,
          EqSimple.fdot (EqSimple.nilconst Y₁ B) hH', ?_⟩
        · rw [valLength_dotL]
          omega
        · calc ((toUnit Y₁ ⨟ c) ⊙ T)
              ≡ₜ (Term.dotL c (toUnit Y₁ ⨟ nilT B) ⊙ T) :=
                Term.fdot_congr (PEq.symm (Term.dotL_nilconst Y₁ B c)) (PEq.refl _)
            _ ≡ₜ Term.dotL c ((toUnit Y₁ ⨟ nilT B) ⊙ T) := Term.dotL_fdot _ _ _
            _ ≡ₜ Term.dotL c ((toUnit Y₁ ⨟ nilT B) ⊙ Term.dotL u' H') :=
                Term.dotL_congr (PEq.refl _) (Term.fdot_congr (PEq.refl _) hT')
            _ ≡ₜ Term.dotL c (Term.dotR (toUnit Y₁ ⨟ nilT B) u' ⊙ H') :=
                Term.dotL_congr (PEq.refl _)
                  (PEq.symm (Term.fdot_dotR_dotL _ _ _))
            _ ≡ₜ Term.dotL c (Term.dotL u' (toUnit Y₁ ⨟ nilT B) ⊙ H') :=
                Term.dotL_congr (PEq.refl _) (Term.fdot_congr
                  ((Term.dotR_nilconst Y₁ B u').trans
                    (PEq.symm (Term.dotL_nilconst Y₁ B u'))) (PEq.refl _))
            _ ≡ₜ Term.dotL c (Term.dotL u' ((toUnit Y₁ ⨟ nilT B) ⊙ H')) :=
                Term.dotL_congr (PEq.refl _) (Term.dotL_fdot _ _ _)
            _ ≡ₜ Term.dotL (Term.dotL c u') ((toUnit Y₁ ⨟ nilT B) ⊙ H') :=
                Term.dotL_dotL _ _ _
      · -- a long factor: it already starts with a value of length `k`
        refine ⟨u, hh ⊙ Term.dotL v T, ?_,
          EqSimple.fdot (EqSimple.of_isSimple hsim)
            (EqSimple.dotL v (EqSimple.congr hT' (EqSimple.dotL u' hH'))), ?_⟩
        · omega
        · calc (Term.dotR (Term.dotL u hh) v ⊙ T)
              ≡ₜ (Term.dotL u hh ⊙ Term.dotL v T) := Term.fdot_dotR_dotL _ _ _
            _ ≡ₜ Term.dotL u (hh ⊙ Term.dotL v T) := Term.dotL_fdot _ _ _

/-- The auxiliary statement behind `KProdT.dotR_factor`: a product of `k`-guarded nonempty
terms either ends with a value of length at least `k`, or is provably a constant whose value
has length at least the number of factors. -/
theorem dotR_aux {j : ℕ} : {Y : Ty} → {T : Term Y B⋆} → KProdT k B j T →
    (∃ (v : Value B⋆) (H : Term Y B⋆), k ≤ valLength v ∧ EqSimple B H ∧
        T ≡ₜ Term.dotR H v) ∨
    (∃ c : Value B⋆, j ≤ valLength c ∧ T ≡ₜ Term.dotR (toUnit Y ⨟ nilT B) c) := by
  intro Y T h
  induction h with
  | nil =>
      refine Or.inr ⟨nilT B, by simp, ?_⟩
      refine PEq.symm ((Term.dotR_nil _).trans ?_)
      exact (PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans
        (PEq.id_comp _)
  | @cons j Y₁ Y₂ f T hf hne _ ih =>
      rcases ih with ⟨v', H', hlen, hH', hT'⟩ | ⟨c', hlen, hT'⟩
      · -- the rest already ends with a long value
        refine Or.inl ⟨v', f ⊙ H', hlen, EqSimple.fdot ?_ hH', ?_⟩
        · rcases hf with ⟨c, rfl⟩ | ⟨u, v, hh, hsim, -, -, rfl⟩
          · exact EqSimple.congr (PEq.symm (Term.dotL_nilconst Y₁ B c))
              (EqSimple.dotL c (EqSimple.nilconst Y₁ B))
          · exact EqSimple.dotR v (EqSimple.dotL u (EqSimple.of_isSimple hsim))
        · exact (Term.fdot_congr (PEq.refl _) hT').trans (Term.dotR_fdot _ _ _)
      · -- the rest is a constant
        have hstep : (f ⊙ T) ≡ₜ Term.dotR (Term.fst Y₁ Y₂ ⨟ f) c' :=
          (Term.fdot_congr (PEq.refl _) hT').trans
            ((Term.dotR_fdot _ _ _).trans
              (Term.dotR_congr (Term.prodF_nilconst_binconcat f) (PEq.refl _)))
        rcases hf with ⟨c, rfl⟩ | ⟨u, v, hh, hsim, -, hv, rfl⟩
        · -- a constant factor: the whole product is a constant
          have hc : 1 ≤ valLength c := by
            have := hne (Ty.someElem Y₁)
            simp only [Term.den_comp, valLength] at this ⊢
            rcases hd : c.den () with _ | ⟨a, l⟩
            · exact absurd (by simp [hd]) this
            · simp
          refine Or.inr ⟨Term.dotL c c', ?_, ?_⟩
          · rw [valLength_dotL]; omega
          · refine hstep.trans ?_
            have h1 : (Term.fst Y₁ Y₂ ⨟ (toUnit Y₁ ⨟ c)) ≡ₜ
                Term.dotR (toUnit (Y₁ ⊗ Y₂) ⨟ nilT B) c :=
              ((PEq.symm (PEq.comp_assoc _ _ _)).trans
                (PEq.compL _ (PEq.unit_unique _ _))).trans
                (PEq.symm (Term.dotR_nilconst _ B c))
            exact (Term.dotR_congr h1 (PEq.refl _)).trans (Term.dotR_dotR _ _ _)
        · -- a long factor: the product ends with the long value followed by the constant
          refine Or.inl ⟨Term.dotL v c', Term.fst Y₁ Y₂ ⨟ Term.dotL u hh, ?_, ?_, ?_⟩
          · rw [valLength_dotL]; omega
          · refine EqSimple.congr (Term.comp_dotL _ _ _) ?_
            refine EqSimple.dotL u ?_
            exact EqSimple.congr (PEq.symm (Term.prodF_nilconst_binconcat hh))
              (EqSimple.fdot (EqSimple.of_isSimple hsim) (EqSimple.nilconst Y₂ B))
          · refine hstep.trans ?_
            have h1 : (Term.fst Y₁ Y₂ ⨟ Term.dotR (Term.dotL u hh) v) ≡ₜ
                Term.dotR (Term.fst Y₁ Y₂ ⨟ Term.dotL u hh) v :=
              Term.comp_dotR _ _ _
            exact (Term.dotR_congr h1 (PEq.refl _)).trans (Term.dotR_dotR _ _ _)

/-- **The suffix of a product of `k`-guarded nonempty terms.** -/
theorem dotR_factor {j : ℕ} {Y : Ty} {T : Term Y B⋆} (h : KProdT k B j T) :
    ∃ (v : Value B⋆) (H : Term Y B⋆), min j k ≤ valLength v ∧ EqSimple B H ∧
      T ≡ₜ Term.dotR H v := by
  rcases dotR_aux h with ⟨v, H, hlen, hH, hT⟩ | ⟨c, hlen, hT⟩
  · exact ⟨v, H, by omega, hH, hT⟩
  · exact ⟨c, toUnit Y ⨟ nilT B, by omega, EqSimple.nilconst Y B, hT⟩

end KProdT

/-! ### Distributing a power of a co-pairing -/

/-- Two terms are a *matching pair of co-pairings of `k`-guarded nonempty terms* if they are
co-pairings with the same case structure whose components are all `k`-guarded and never
produce the empty list. -/
inductive KCopair2 (k : ℕ) (B : Ty) : {X : Ty} → Term X B⋆ → Term X B⋆ → Prop
  /-- A single component. -/
  | leaf {X : Ty} {f g : Term X B⋆} : KGuarded k B f → KGuarded k B g →
      NonemptyOutput f → NonemptyOutput g → KCopair2 k B f g
  /-- Two co-pairings. -/
  | node {X₁ X₂ : Ty} {f₁ g₁ : Term X₁ B⋆} {f₂ g₂ : Term X₂ B⋆} :
      KCopair2 k B f₁ g₁ → KCopair2 k B f₂ g₂ →
      KCopair2 k B (Term.either f₁ f₂) (Term.either g₁ g₂)

namespace KCopair2

variable {k : ℕ} {B : Ty}

/-- Prefixing a matching pair of co-pairings to a pair of products of `k`-guarded nonempty
terms yields a joint decomposition into products with one more factor. -/
theorem fdot_jointCases {j : ℕ} : {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G →
    ∀ {Y : Ty} {T S : Term Y B⋆}, KProdT k B j T → KProdT k B j S →
      JointCases B (fun T S => KProdT k B (j + 1) T ∧ KProdT k B (j + 1) S) (F ⊙ T) (G ⊙ S) := by
  intro X F G h
  induction h with
  | leaf hf hg hnf hng =>
      exact fun hT hS => JointCases.leaf ⟨KProdT.cons hf hnf hT, KProdT.cons hg hng hS⟩
  | @node X₁ X₂ f₁ g₁ f₂ g₂ _ _ ih₁ ih₂ =>
      intro Y T S hT hS
      refine JointCases.congr (Term.fdot_either_distL f₁ f₂ T)
        (Term.fdot_either_distL g₁ g₂ S) ?_
      refine JointCases.precomp (ProvableIso.undistL X₁ X₂ Y) ?_ ?_
      · simp only [Ty.listDepth]
        omega
      · refine JointCases.congr ?_ ?_ (JointCases.node (ih₁ hT hS) (ih₂ hT hS))
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistL_distL X₁ X₂ Y)).trans (PEq.id_comp _))
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistL_distL X₁ X₂ Y)).trans (PEq.id_comp _))

/-- **The distribution step.**  The `j`-fold concatenation power of a matching pair of
co-pairings of `k`-guarded nonempty terms decomposes jointly into `j`-fold products of
`k`-guarded nonempty terms. -/
theorem pow_jointCases {X : Ty} {F G : Term X B⋆} (h : KCopair2 k B F G) :
    (j : ℕ) → JointCases B (fun T S => KProdT k B j T ∧ KProdT k B j S)
      ((Term.TyF.pow j).homMap F) ((Term.TyF.pow j).homMap G)
  | 0 => JointCases.leaf ⟨KProdT.nil, KProdT.nil⟩
  | (j + 1) => JointCases.fdot_left F G
      (fun _ _ hTS => h.fdot_jointCases hTS.1 hTS.2) (pow_jointCases h j)

end KCopair2

end Lax149335Proofs

bridge_export Lax149335Proofs
