import Lax149335Proofs.Preliminaries.StringRepresentation
import Lax149335Proofs.EquationalTheory.DerivedRules
import Lax149335Proofs.EquationalTheory.Soundness
import Lax149335Proofs.GeneralCompleteness.AtomicFactorisation

/-!
# Lifts and drops (Section 7, Definition 7.1 and Table 1)

The two classes of terms used by the completeness proof for all rational terms: lifts, which
annotate the input with some structure, and drops, which erase such an annotation.  The file
also contains the closure properties of the two classes that are used everywhere, and
Lemma 7.2, which says that every lift is an isomorphism whose inverse is a drop.

The remaining results of Section 7 are in `Lax149335Proofs.GeneralCompleteness.Statements`; they are
separated off because the appendix files that prove Lemma 7.3 need the definitions below,
while `Lax149335Proofs.GeneralCompleteness.Statements` needs those appendix files.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- Every lift is aperiodic: none of the prime lifts of Table 1 uses the group prefix
multiplication, and the three functoriality combinators and composition preserve that. -/
theorem IsLift.isAperiodic {A B : Ty} {f : Term A B} (hf : IsLift f) : IsAperiodic f := by
  induction hf with
  | comp _ _ ih₁ ih₂ => simpa [Term.isAperiodic_comp] using ⟨ih₁, ih₂⟩
  | prodF _ _ ih₁ ih₂ => simpa [Term.isAperiodic_prodF] using ⟨ih₁, ih₂⟩
  | sumF _ _ ih₁ ih₂ => simpa [Term.isAperiodic_sumF] using ⟨ih₁, ih₂⟩
  | listF _ ih => simpa [Term.isAperiodic_listF] using ih
  | _ =>
      simp [IsAperiodic, Term.usesPref, Term.sumAssocL, Term.sumAssocR, Term.comm,
        Term.either, Term.shift]

/-- Associativity of the co-product, from left to right, is a drop. -/
theorem isDrop_sumAssocR (A B C : Ty) : IsDrop (Term.sumAssocR A B C) := by
  refine IsDrop.comp (IsDrop.sumF ?_ ?_) (IsDrop.codiag _)
  · exact IsDrop.comp (IsDrop.sumF (IsDrop.inl _ _) (IsDrop.comp (IsDrop.inl _ _)
      (IsDrop.inr _ _))) (IsDrop.codiag _)
  · exact IsDrop.comp (IsDrop.inr _ _) (IsDrop.inr _ _)

/-- Associativity of the co-product, from right to left, is a drop. -/
theorem isDrop_sumAssocL (A B C : Ty) : IsDrop (Term.sumAssocL A B C) := by
  refine IsDrop.comp (IsDrop.sumF ?_ ?_) (IsDrop.codiag _)
  · exact IsDrop.comp (IsDrop.inl _ _) (IsDrop.inl _ _)
  · exact IsDrop.comp (IsDrop.sumF (IsDrop.comp (IsDrop.inr _ _) (IsDrop.inl _ _))
      (IsDrop.inr _ _)) (IsDrop.codiag _)

/-- Commutativity of the co-product is a drop. -/
theorem isDrop_comm (A B : Ty) : IsDrop (Term.comm A B) :=
  IsDrop.comp (IsDrop.sumF (IsDrop.inr B A) (IsDrop.inl B A)) (IsDrop.codiag (B ⊕' A))

/-- The inverse of distributivity on the left is a drop. -/
theorem isDrop_undistL (A B C : Ty) : IsDrop (Term.undistL A B C) :=
  IsDrop.comp
    (IsDrop.sumF (IsDrop.prodF (IsDrop.inl A B) (IsDrop.id C))
      (IsDrop.prodF (IsDrop.inr A B) (IsDrop.id C)))
    (IsDrop.codiag ((A ⊕' B) ⊗ C))

/-- The inverse of distributivity on the right is a drop. -/
theorem isDrop_undistR (A B C : Ty) : IsDrop (Term.undistR A B C) :=
  IsDrop.comp
    (IsDrop.sumF (IsDrop.prodF (IsDrop.id A) (IsDrop.inl B C))
      (IsDrop.prodF (IsDrop.id A) (IsDrop.inr B C)))
    (IsDrop.codiag (A ⊗ (B ⊕' C)))

/-- The inverse of `split` is a concatenation map, and concatenation maps are drops. -/
theorem isDrop_unsplit (A B : Ty) : IsDrop (Term.unsplit A B) := by
  have hl : IsDrop (Term.homT (Term.inl A B ⨟ Term.pureT (A ⊕' B))) :=
    IsDrop.comp (IsDrop.listF (IsDrop.comp (IsDrop.inl A B) (IsDrop.pureT (A ⊕' B))))
      (IsDrop.concat (A ⊕' B))
  have hr : IsDrop (Term.homT ((Term.inr A B ⨟ Term.pureT (A ⊕' B)) ⊙
      Term.homT (Term.inl A B ⨟ Term.pureT (A ⊕' B)))) :=
    IsDrop.comp
      (IsDrop.listF (IsDrop.comp
        (IsDrop.prodF (IsDrop.comp (IsDrop.inr A B) (IsDrop.pureT (A ⊕' B))) hl)
        (IsDrop.binconcat (A ⊕' B))))
      (IsDrop.concat (A ⊕' B))
  exact IsDrop.comp (IsDrop.prodF hl hr) (IsDrop.binconcat (A ⊕' B))

/-- **Lemma 7.2.**  Every lift is an isomorphism, and its inverse is a drop. -/
theorem lift_iso {A B : Ty} (f : Term A B) (hf : IsLift f) :
    ∃ g : Term B A, IsDrop g ∧ (f ⨟ g) ≡ₜ Term.id A ∧ (g ⨟ f) ≡ₜ Term.id B := by
  induction hf with
  | @comp A B C f g _ _ ihf ihg =>
    obtain ⟨f', hf', hff', hf'f⟩ := ihf
    obtain ⟨g', hg', hgg', hg'g⟩ := ihg
    refine ⟨g' ⨟ f', IsDrop.comp hg' hf', ?_, ?_⟩
    · calc ((f ⨟ g) ⨟ (g' ⨟ f')) ≡ₜ (f ⨟ (g ⨟ (g' ⨟ f'))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (f ⨟ ((g ⨟ g') ⨟ f')) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (f ⨟ (Term.id B ⨟ f')) := PEq.compR _ (PEq.compL _ hgg')
        _ ≡ₜ (f ⨟ f') := PEq.compR _ (PEq.id_comp _)
        _ ≡ₜ Term.id A := hff'
    · calc ((g' ⨟ f') ⨟ (f ⨟ g)) ≡ₜ (g' ⨟ (f' ⨟ (f ⨟ g))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (g' ⨟ ((f' ⨟ f) ⨟ g)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (g' ⨟ (Term.id B ⨟ g)) := PEq.compR _ (PEq.compL _ hf'f)
        _ ≡ₜ (g' ⨟ g) := PEq.compR _ (PEq.id_comp _)
        _ ≡ₜ Term.id C := hg'g
  | @prodF A₁ A₂ B₁ B₂ f g _ _ ihf ihg =>
    obtain ⟨f', hf', hff', hf'f⟩ := ihf
    obtain ⟨g', hg', hgg', hg'g⟩ := ihg
    refine ⟨Term.prodF f' g', IsDrop.prodF hf' hg', ?_, ?_⟩
    · exact (PEq.prod_comp _ _ _ _).trans
        ((PEq.congr_prodF hff' hgg').trans (PEq.prod_id A₁ A₂))
    · exact (PEq.prod_comp _ _ _ _).trans
        ((PEq.congr_prodF hf'f hg'g).trans (PEq.prod_id B₁ B₂))
  | @sumF A₁ A₂ B₁ B₂ f g _ _ ihf ihg =>
    obtain ⟨f', hf', hff', hf'f⟩ := ihf
    obtain ⟨g', hg', hgg', hg'g⟩ := ihg
    refine ⟨Term.sumF f' g', IsDrop.sumF hf' hg', ?_, ?_⟩
    · exact (PEq.sum_comp _ _ _ _).trans
        ((PEq.congr_sumF hff' hgg').trans (PEq.sum_id A₁ A₂))
    · exact (PEq.sum_comp _ _ _ _).trans
        ((PEq.congr_sumF hf'f hg'g).trans (PEq.sum_id B₁ B₂))
  | @listF A B f _ ih =>
    obtain ⟨f', hf', hff', hf'f⟩ := ih
    refine ⟨Term.listF f', IsDrop.listF hf', ?_, ?_⟩
    · exact (PEq.list_comp _ _).trans ((PEq.congr_listF hff').trans (PEq.list_id A))
    · exact (PEq.list_comp _ _).trans ((PEq.congr_listF hf'f).trans (PEq.list_id B))
  | id A => exact ⟨Term.id A, IsDrop.id A, PEq.id_comp _, PEq.id_comp _⟩
  | unitR A => exact ⟨Term.fst A Ty.unit, IsDrop.fst A Ty.unit, PEq.unitR_fst A, PEq.fst_unitR A⟩
  | unitL A => exact ⟨Term.snd Ty.unit A, IsDrop.snd Ty.unit A, PEq.unitL_snd A, PEq.snd_unitL A⟩
  | assocL A B C =>
    exact ⟨Term.assocR A B C, IsDrop.assocR A B C, PEq.assocL_assocR A B C,
      PEq.assocR_assocL A B C⟩
  | assocR A B C =>
    exact ⟨Term.assocL A B C, IsDrop.assocL A B C, PEq.assocR_assocL A B C,
      PEq.assocL_assocR A B C⟩
  | sumAssocL A B C =>
    exact ⟨Term.sumAssocR A B C, isDrop_sumAssocR A B C, Term.sumAssocL_sumAssocR A B C,
      Term.sumAssocR_sumAssocL A B C⟩
  | sumAssocR A B C =>
    exact ⟨Term.sumAssocL A B C, isDrop_sumAssocL A B C, Term.sumAssocR_sumAssocL A B C,
      Term.sumAssocL_sumAssocR A B C⟩
  | comm A B => exact ⟨Term.comm B A, isDrop_comm B A, Term.comm_comm A B, Term.comm_comm B A⟩
  | distL A B C =>
    exact ⟨Term.undistL A B C, isDrop_undistL A B C, PEq.distL_undistL A B C,
      PEq.undistL_distL A B C⟩
  | distR A B C =>
    exact ⟨Term.undistR A B C, isDrop_undistR A B C, PEq.distR_undistR A B C,
      PEq.undistR_distR A B C⟩
  | split A B =>
    exact ⟨Term.unsplit A B, isDrop_unsplit A B, PEq.split_unsplit A B, PEq.unsplit_split A B⟩
  | shift A B =>
    exact ⟨Term.unshift A B, IsDrop.unshift A B, Term.shift_unshift A B, Term.unshift_shift A B⟩

/-! ### Terms that are provably equal to a drop, and lift-drop factorisations

The two auxiliary predicates that the proofs of Section 7 use everywhere.  They are recorded
here, together with the closure properties that do *not* need the exchange lemma; closure of
`Lax149335Proofs.IsLiftDrop` under composition is exactly the exchange lemma and is proved in
`Lax149335Proofs.GeneralCompleteness.Statements`. -/

/-- Terms that are provably equal to a drop. -/
def IsEqDrop {A B : Ty} (f : Term A B) : Prop := ∃ d : Term A B, IsDrop d ∧ f ≡ₜ d

/-- Terms that are provably equal to a lift followed by a drop; this is the conclusion of
Lemma 7.4. -/
def IsLiftDrop {A B : Ty} (f : Term A B) : Prop :=
  ∃ (C : Ty) (l : Term A C) (d : Term C B), IsLift l ∧ IsDrop d ∧ f ≡ₜ (l ⨟ d)

namespace IsEqDrop

theorem of_isDrop {A B : Ty} {f : Term A B} (h : IsDrop f) : IsEqDrop f := ⟨f, h, PEq.refl f⟩

theorem congr {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) (hg : IsEqDrop g) : IsEqDrop f :=
  ⟨hg.choose, hg.choose_spec.1, h.trans hg.choose_spec.2⟩

theorem comp {A B C : Ty} {f : Term A B} {g : Term B C} (hf : IsEqDrop f) (hg : IsEqDrop g) :
    IsEqDrop (f ⨟ g) := by
  obtain ⟨d₁, hd₁, h₁⟩ := hf
  obtain ⟨d₂, hd₂, h₂⟩ := hg
  exact ⟨d₁ ⨟ d₂, IsDrop.comp hd₁ hd₂, PEq.congr_comp h₁ h₂⟩

theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsEqDrop f) (hg : IsEqDrop g) : IsEqDrop (Term.prodF f g) := by
  obtain ⟨d₁, hd₁, h₁⟩ := hf
  obtain ⟨d₂, hd₂, h₂⟩ := hg
  exact ⟨Term.prodF d₁ d₂, IsDrop.prodF hd₁ hd₂, PEq.congr_prodF h₁ h₂⟩

theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsEqDrop f) (hg : IsEqDrop g) : IsEqDrop (Term.sumF f g) := by
  obtain ⟨d₁, hd₁, h₁⟩ := hf
  obtain ⟨d₂, hd₂, h₂⟩ := hg
  exact ⟨Term.sumF d₁ d₂, IsDrop.sumF hd₁ hd₂, PEq.congr_sumF h₁ h₂⟩

theorem listF {A B : Ty} {f : Term A B} (hf : IsEqDrop f) : IsEqDrop (Term.listF f) := by
  obtain ⟨d, hd, h⟩ := hf
  exact ⟨Term.listF d, IsDrop.listF hd, PEq.congr_listF h⟩

theorem either {A₁ A₂ B : Ty} {f : Term A₁ B} {g : Term A₂ B}
    (hf : IsEqDrop f) (hg : IsEqDrop g) : IsEqDrop (Term.either f g) :=
  (hf.sumF hg).comp (of_isDrop (IsDrop.codiag B))

end IsEqDrop

/-- The empty list is provably equal to a drop. -/
theorem isEqDrop_nilT (A : Ty) : IsEqDrop (Term.nilT A) :=
  IsEqDrop.congr (Term.nilT_unshift A)
    (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.comp (IsDrop.inl _ _) (IsDrop.unshift _ _))
      (IsDrop.listF (IsDrop.fst _ _))))

/-- Prepending is provably equal to a drop (Axiom 13). -/
theorem isEqDrop_prepend (A : Ty) : IsEqDrop (Term.prepend A) :=
  IsEqDrop.congr (PEq.prepend_def A)
    (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.prodF (IsDrop.pureT A) (IsDrop.id A⋆))
      (IsDrop.binconcat A)))

/-- Appending is provably equal to a drop (Axiom 13). -/
theorem isEqDrop_append (A : Ty) : IsEqDrop (Term.append A) :=
  IsEqDrop.congr (PEq.append_def A)
    (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.prodF (IsDrop.id A⋆) (IsDrop.pureT A))
      (IsDrop.binconcat A)))

/-- `cons` is provably equal to a drop. -/
theorem isEqDrop_cons (A : Ty) : IsEqDrop (Term.cons A) :=
  IsEqDrop.congr (Term.cons_either A) ((isEqDrop_nilT A).either (isEqDrop_prepend A))

/-- `snoc` is provably equal to a drop. -/
theorem isEqDrop_snoc (A : Ty) : IsEqDrop (Term.snoc A) :=
  IsEqDrop.congr (Term.snoc_either A) ((isEqDrop_nilT A).either (isEqDrop_append A))

namespace IsLiftDrop

theorem congr {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) (hg : IsLiftDrop g) : IsLiftDrop f := by
  obtain ⟨C, l, d, hl, hd, hgld⟩ := hg
  exact ⟨C, l, d, hl, hd, h.trans hgld⟩

theorem of_isLift {A B : Ty} {f : Term A B} (h : IsLift f) : IsLiftDrop f :=
  ⟨B, f, Term.id B, h, IsDrop.id B, PEq.symm (PEq.comp_id f)⟩

theorem of_isEqDrop {A B : Ty} {f : Term A B} (h : IsEqDrop f) : IsLiftDrop f := by
  obtain ⟨d, hd, hfd⟩ := h
  exact ⟨A, Term.id A, d, IsLift.id A, hd, hfd.trans (PEq.symm (PEq.id_comp d))⟩

theorem of_isDrop {A B : Ty} {f : Term A B} (h : IsDrop f) : IsLiftDrop f :=
  of_isEqDrop (IsEqDrop.of_isDrop h)

/-- A lift followed by a lift-drop factorisation is one. -/
theorem comp_left {A B C : Ty} {l : Term A B} {f : Term B C} (hl : IsLift l)
    (hf : IsLiftDrop f) : IsLiftDrop (l ⨟ f) := by
  obtain ⟨D, l', d', hl', hd', he⟩ := hf
  refine ⟨D, l ⨟ l', d', IsLift.comp hl hl', hd', ?_⟩
  exact (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))

/-- A lift-drop factorisation followed by a drop is one. -/
theorem comp_right {A B C : Ty} {f : Term A B} {d : Term B C} (hf : IsLiftDrop f)
    (hd : IsDrop d) : IsLiftDrop (f ⨟ d) := by
  obtain ⟨D, l', d', hl', hd', he⟩ := hf
  refine ⟨D, l', d' ⨟ d, hl', IsDrop.comp hd' hd, ?_⟩
  exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)

/-- A lift-drop factorisation followed by a term that is provably equal to a drop is one. -/
theorem comp_eqDrop {A B C : Ty} {f : Term A B} {d : Term B C} (hf : IsLiftDrop f)
    (hd : IsEqDrop d) : IsLiftDrop (f ⨟ d) := by
  obtain ⟨d', hd', he⟩ := hd
  exact congr (PEq.compR _ he) (comp_right hf hd')

theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsLiftDrop f) (hg : IsLiftDrop g) : IsLiftDrop (Term.prodF f g) := by
  obtain ⟨C₁, l₁, d₁, hl₁, hd₁, h₁⟩ := hf
  obtain ⟨C₂, l₂, d₂, hl₂, hd₂, h₂⟩ := hg
  refine ⟨C₁ ⊗ C₂, Term.prodF l₁ l₂, Term.prodF d₁ d₂, IsLift.prodF hl₁ hl₂,
    IsDrop.prodF hd₁ hd₂, ?_⟩
  exact (PEq.congr_prodF h₁ h₂).trans (PEq.symm (PEq.prod_comp _ _ _ _))

theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsLiftDrop f) (hg : IsLiftDrop g) : IsLiftDrop (Term.sumF f g) := by
  obtain ⟨C₁, l₁, d₁, hl₁, hd₁, h₁⟩ := hf
  obtain ⟨C₂, l₂, d₂, hl₂, hd₂, h₂⟩ := hg
  refine ⟨C₁ ⊕' C₂, Term.sumF l₁ l₂, Term.sumF d₁ d₂, IsLift.sumF hl₁ hl₂,
    IsDrop.sumF hd₁ hd₂, ?_⟩
  exact (PEq.congr_sumF h₁ h₂).trans (PEq.symm (PEq.sum_comp _ _ _ _))

theorem listF {A B : Ty} {f : Term A B} (hf : IsLiftDrop f) : IsLiftDrop (Term.listF f) := by
  obtain ⟨C, l, d, hl, hd, h⟩ := hf
  exact ⟨C⋆, Term.listF l, Term.listF d, IsLift.listF hl, IsDrop.listF hd,
    (PEq.congr_listF h).trans (PEq.symm (PEq.list_comp _ _))⟩

theorem either {A₁ A₂ B : Ty} {f : Term A₁ B} {g : Term A₂ B}
    (hf : IsLiftDrop f) (hg : IsLiftDrop g) : IsLiftDrop (Term.either f g) :=
  (hf.sumF hg).comp_right (IsDrop.codiag B)

end IsLiftDrop

end Lax149335Proofs

bridge_export Lax149335Proofs
