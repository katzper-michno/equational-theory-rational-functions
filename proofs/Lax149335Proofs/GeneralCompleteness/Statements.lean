import Lax149335Proofs.GeneralCompleteness.LiftsAndDrops
import Lax149335Proofs.SimpleCompleteness.Proof
import Lax149335Proofs.Appendix.Drops.JointSimplification
import Lax149335Proofs.Appendix.Drops.ExchangeShiftSplit
import Lax149335Proofs.Appendix.Drops.SplitExchange
import Mathlib.Tactic.Set

/-!
# Completeness for all rational terms (Section 7)

The reduction of drops to simple rational terms (Lemma 7.3), the lift-drop factorisation
(Lemma 7.4), the exchange lemma (Lemma 7.5) and completeness in the aperiodic case
(Corollary 7.6).

Lifts and drops themselves (Definition 7.1 and Table 1) and Lemma 7.2 are in
`Lax149335Proofs.GeneralCompleteness.LiftsAndDrops`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- **Lemma 7.3.**  If `B` is a finite alphabet and `f, g : A ⇒ B*` are drops, then there is a
lift `A ⊸ C` whose drop inverse `π : C ⇒ A` is such that `π; f` and `π; g` are both provably
equivalent to simple rational terms. -/
theorem drops_to_simple {A B : Ty} (hB : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsDrop f) (hg : IsDrop g) :
    ∃ (C : Ty) (l : Term A C) (π : Term C A),
      IsLift l ∧ IsDrop π ∧ (l ⨟ π) ≡ₜ Term.id A ∧ (π ⨟ l) ≡ₜ Term.id C ∧
      (∃ f' : Term C B⋆, IsSimple B f' ∧ (π ⨟ f) ≡ₜ f') ∧
      (∃ g' : Term C B⋆, IsSimple B g' ∧ (π ⨟ g) ≡ₜ g') := by
  obtain ⟨D, l, pi, lvf, lvg, hl, hpi, hlp, hpl, hf', hg'⟩ :=
    drops_to_common_shape hB f g hf hg
  obtain ⟨sf, hsf, hsfe⟩ := shapeOf_isSimple B D lvf
  obtain ⟨sg, hsg, hsge⟩ := shapeOf_isSimple B D lvg
  exact ⟨D, l, pi, hl, hpi, hlp, hpl, ⟨sf, hsf, hf'.trans hsfe⟩, ⟨sg, hsg, hg'.trans hsge⟩⟩

/-! Aperiodic terms (`Lax149335Proofs.IsAperiodic`) are defined in `Lax149335Proofs.Terms.Terms`. -/

/-- The value that represents an element of a type does not use the prefix multiplication of
groups. -/
theorem aperiodic_encV : ∀ (A : Ty) (x : ⟦A⟧), IsAperiodic (encV A x) := by
  intro A
  induction A with
  | unit => intro x; rfl
  | prod A B ihA ihB =>
      intro x
      simp only [encV, Term.pairR, IsAperiodic, Term.usesPref, Bool.or_eq_false_iff]
      exact ⟨trivial, ihA x.1, ihB x.2⟩
  | sum A B ihA ihB =>
      intro x
      cases x with
      | inl a => simpa [IsAperiodic, Term.usesPref] using ihA a
      | inr b => simpa [IsAperiodic, Term.usesPref] using ihB b
  | list A ih =>
      intro l
      induction l with
      | nil => simp [encV, Term.nilT, IsAperiodic, Term.usesPref]
      | cons a t iht =>
          simp only [encV, List.foldr] at *
          simp only [Term.dotL, Term.sing, Term.pairL, IsAperiodic, Term.usesPref,
            Bool.or_eq_false_iff] at *
          exact ⟨⟨trivial, ⟨ih a, rfl⟩, iht⟩, rfl⟩

/-- Drops do not use the prefix multiplication of groups, up to provable equality.

The prime drop `1 ; v` may of course mention `pref` inside the value `v`; but every value is
provably equal to the value that represents its denotation, which does not. -/
theorem IsDrop.eqAperiodic {A B : Ty} {f : Term A B} (hf : IsDrop f) :
    ∃ f' : Term A B, IsAperiodic f' ∧ f ≡ₜ f' := by
  induction hf with
  | @comp A B C f g _ _ ihf ihg =>
      obtain ⟨f', hf', hef⟩ := ihf
      obtain ⟨g', hg', heg⟩ := ihg
      exact ⟨f' ⨟ g', by simp [hf', hg'], PEq.congr_comp hef heg⟩
  | @prodF _ _ _ _ f g _ _ ihf ihg =>
      obtain ⟨f', hf', hef⟩ := ihf
      obtain ⟨g', hg', heg⟩ := ihg
      exact ⟨Term.prodF f' g', by simp [hf', hg'], PEq.congr_prodF hef heg⟩
  | @sumF _ _ _ _ f g _ _ ihf ihg =>
      obtain ⟨f', hf', hef⟩ := ihf
      obtain ⟨g', hg', heg⟩ := ihg
      exact ⟨Term.sumF f' g', by simp [hf', hg'], PEq.congr_sumF hef heg⟩
  | @listF _ _ f _ ih =>
      obtain ⟨f', hf', hef⟩ := ih
      exact ⟨Term.listF f', by simp [hf'], PEq.congr_listF hef⟩
  | bangV A v =>
      refine ⟨Term.toUnit A ⨟ encV _ (v.den ()), ?_, ?_⟩
      · simpa [IsAperiodic, Term.usesPref, Term.toUnit] using aperiodic_encV _ (v.den ())
      · exact PEq.compR _ ((PEq.symm (PEq.id_comp v)).trans (computes v ()))
  | _ => exact ⟨_, by rfl, PEq.refl _⟩

bridge_export Lax149335Proofs

/-- **Lemma 7.5 (Exchange).**  Every composition of the form drop-lift is provably equivalent
to a composition of the form lift-drop.

The induction of the appendix on the lift is carried out in
`Lax149335Proofs.Appendix.Drops.ExchangeProof`: `Lax149335Proofs.exchange_of_shift_split` proves this
statement from the two hard cases of the appendix, namely that the prime lifts `shift` and
`split` admit exchange (`Lax149335Proofs.AdmitsExchange`).  All the other cases -- the four
combinators and the ten remaining prime lifts of Table 1 -- are proved there.  The case
*Shift* is `Lax149335Proofs.admitsExchange_shift`
(`Lax149335Proofs.Appendix.Drops.ExchangeShiftSplit`) and the case *Split* is
`Lax149335Proofs.admitsExchange_split` (`Lax149335Proofs.Appendix.Drops.SplitExchange`). -/
theorem exchange {A B C : Ty} (d : Term A B) (l : Term B C) (hd : IsDrop d) (hl : IsLift l) :
    ∃ (D : Ty) (l' : Term A D) (d' : Term D C),
      IsLift l' ∧ IsDrop d' ∧ (d ⨟ l) ≡ₜ (l' ⨟ d') :=
  exchange_of_shift_split admitsExchange_shift admitsExchange_split d l hd hl

/-! ### The lift-drop factorisation (Lemma 7.4)

The proof is an induction on the term.  Since the classes of lifts and of drops are not
closed under provable equality, the two auxiliary predicates `IsEqDrop` (provably equal to a
drop) and `IsLiftDrop` (provably equal to a lift followed by a drop) are used; the latter is
exactly the conclusion of Lemma 7.4.  The base cases are supplied by
`Lax149335Proofs.GeneralCompleteness.AtomicFactorisation`, and the case of a composition is the exchange lemma. -/

namespace IsLiftDrop

/-- The composition case: this is the exchange lemma (Lemma 7.5), taken as the hypothesis
`hex`. -/
theorem comp_of (hex : type_of% @Lax149335.Exchange.exchange) {A B C : Ty} {f : Term A B} {g : Term B C}
    (hf : IsLiftDrop f) (hg : IsLiftDrop g) : IsLiftDrop (f ⨟ g) := by
  obtain ⟨C₁, l₁, d₁, hl₁, hd₁, h₁⟩ := hf
  obtain ⟨C₂, l₂, d₂, hl₂, hd₂, h₂⟩ := hg
  obtain ⟨D, l', d', hl', hd', hex⟩ := hex d₁ l₂ hd₁ hl₂
  refine ⟨D, l₁ ⨟ l', d' ⨟ d₂, IsLift.comp hl₁ hl', IsDrop.comp hd' hd₂, ?_⟩
  calc (f ⨟ g) ≡ₜ ((l₁ ⨟ d₁) ⨟ (l₂ ⨟ d₂)) := PEq.congr_comp h₁ h₂
    _ ≡ₜ (l₁ ⨟ (d₁ ⨟ (l₂ ⨟ d₂))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (l₁ ⨟ ((d₁ ⨟ l₂) ⨟ d₂)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (l₁ ⨟ ((l' ⨟ d') ⨟ d₂)) := PEq.compR _ (PEq.compL _ hex)
    _ ≡ₜ (l₁ ⨟ (l' ⨟ (d' ⨟ d₂))) := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((l₁ ⨟ l') ⨟ (d' ⨟ d₂)) := PEq.symm (PEq.comp_assoc _ _ _)

/-- The composition case. -/
theorem comp {A B C : Ty} {f : Term A B} {g : Term B C} (hf : IsLiftDrop f)
    (hg : IsLiftDrop g) : IsLiftDrop (f ⨟ g) :=
  comp_of exchange hf hg

end IsLiftDrop

/-- Every canonical value admits a lift-drop factorisation. -/
theorem isLiftDrop_defaultValue (A : Ty) : IsLiftDrop (Term.defaultValue A) := by
  induction A with
  | unit => exact IsLiftDrop.of_isLift (IsLift.id Ty.unit)
  | prod A B ihA ihB =>
      exact (IsLiftDrop.of_isLift (IsLift.unitR Ty.unit)).comp (ihA.prodF ihB)
  | sum A B ihA _ => exact ihA.comp (IsLiftDrop.of_isDrop (IsDrop.inl A B))
  | list A _ => exact IsLiftDrop.of_isEqDrop (isEqDrop_nilT A)

/-- Every canonical term between two types admits a lift-drop factorisation. -/
theorem isLiftDrop_anyTerm (A B : Ty) : IsLiftDrop (Term.anyTerm A B) :=
  IsLiftDrop.of_isDrop (IsDrop.bangV A (Term.defaultValue B))

/-- The retraction of the right co-projection admits a lift-drop factorisation. -/
theorem isLiftDrop_inrRetract (A B : Ty) :
    IsLiftDrop (Term.either (Term.anyTerm A B) (Term.id B)) :=
  (isLiftDrop_anyTerm A B).either (IsLiftDrop.of_isLift (IsLift.id B))

/-- A term can be recovered from its product with an identity, so the lift-drop factorisation
transfers from `id × h` to `h`. -/
theorem IsLiftDrop.of_prodF_id {A X Y : Ty} (h : Term X Y)
    (hp : IsLiftDrop (Term.prodF (Term.id A) h)) : IsLiftDrop h := by
  have key : h ≡ₜ (((Term.unitL X ⨟ Term.prodF (Term.defaultValue A) (Term.id X)) ⨟
      Term.prodF (Term.id A) h) ⨟ Term.snd A Y) := by
    calc h ≡ₜ (Term.id X ⨟ h) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ ((Term.unitL X ⨟ Term.snd Ty.unit X) ⨟ h) := PEq.compL _ (PEq.symm (PEq.unitL_snd X))
      _ ≡ₜ (Term.unitL X ⨟ (Term.snd Ty.unit X ⨟ h)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.unitL X ⨟ (Term.prodF (Term.defaultValue A) h ⨟ Term.snd A Y)) :=
          PEq.compR _ (PEq.symm (PEq.nat_snd _ _))
      _ ≡ₜ (Term.unitL X ⨟ ((Term.prodF (Term.defaultValue A) (Term.id X) ⨟
            Term.prodF (Term.id A) h) ⨟ Term.snd A Y)) := by
          refine PEq.compR _ (PEq.compL _ ?_)
          exact PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _)))
      _ ≡ₜ ((Term.unitL X ⨟ (Term.prodF (Term.defaultValue A) (Term.id X) ⨟
            Term.prodF (Term.id A) h)) ⨟ Term.snd A Y) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ _ := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
  refine IsLiftDrop.congr key (IsLiftDrop.comp (IsLiftDrop.comp ?_ hp) ?_)
  · exact (IsLiftDrop.of_isLift (IsLift.unitL X)).comp
      ((isLiftDrop_defaultValue A).prodF (IsLiftDrop.of_isLift (IsLift.id X)))
  · exact IsLiftDrop.of_isDrop (IsDrop.snd A Y)

/-! #### The base cases -/

/-- `uncons` admits a lift-drop factorisation. -/
theorem isLiftDrop_uncons (A : Ty) : IsLiftDrop (Term.uncons A) := by
  refine IsLiftDrop.congr (Term.uncons_factor A) ?_
  refine IsLiftDrop.comp ?_ (IsLiftDrop.of_isDrop ?_)
  · exact (IsLiftDrop.of_isLift (IsLift.listF (IsLift.unitR A))).comp
      (IsLiftDrop.of_isLift (IsLift.shift A Ty.unit))
  · exact IsDrop.sumF (IsDrop.id Ty.unit)
      (IsDrop.prodF (IsDrop.id A) (IsDrop.comp (IsDrop.fst _ _) (IsDrop.listF (IsDrop.snd _ _))))

/-- `unsnoc` admits a lift-drop factorisation. -/
theorem isLiftDrop_unsnoc (A : Ty) : IsLiftDrop (Term.unsnoc A) := by
  refine IsLiftDrop.congr (Term.unsnoc_factor A) ?_
  refine IsLiftDrop.comp ?_ (IsLiftDrop.of_isDrop ?_)
  · exact (IsLiftDrop.of_isLift (IsLift.listF (IsLift.unitL A))).comp
      (IsLiftDrop.of_isLift (IsLift.shift Ty.unit A))
  · exact IsDrop.sumF (IsDrop.id Ty.unit)
      (IsDrop.comp (IsDrop.snd _ _) (IsDrop.prodF (IsDrop.listF (IsDrop.fst _ _))
        (IsDrop.id A)))

/-- The left inverse of `prepend` admits a lift-drop factorisation. -/
theorem isLiftDrop_unprepend (A : Ty) : IsLiftDrop (Term.unprepend A) :=
  (isLiftDrop_uncons A).comp
    ((isLiftDrop_defaultValue (A ⊗ A⋆)).either (IsLiftDrop.of_isLift (IsLift.id (A ⊗ A⋆))))

/-- `shiftL`, paired with an identity, admits a lift-drop factorisation. -/
theorem isLiftDrop_prodF_shiftL (A B : Ty) :
    IsLiftDrop (Term.prodF (Term.id A) (Term.shiftL B A)) := by
  -- the composite that `shift` performs on a non-empty list
  have hG : (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) ≡ₜ
      ((Term.prepend (A ⊗ B) ⨟ Term.shift A B) ⨟
        Term.either (Term.anyTerm Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)))
          (Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B)))) := by
    have hpre : (Term.prepend (A ⊗ B) ⨟ Term.shift A B) ≡ₜ
        ((Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) ⨟
          Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B))) := by
      calc ((Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆) ⨟ Term.cons (A ⊗ B)) ⨟
            (Term.uncons (A ⊗ B) ⨟ Term.sumF (Term.id Ty.unit)
              (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A))))
          ≡ₜ (Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆) ⨟ (Term.cons (A ⊗ B) ⨟
              (Term.uncons (A ⊗ B) ⨟ Term.sumF (Term.id Ty.unit)
                (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆) ⨟ ((Term.cons (A ⊗ B) ⨟
              Term.uncons (A ⊗ B)) ⨟ Term.sumF (Term.id Ty.unit)
                (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)))) :=
            PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆) ⨟
              (Term.id (Ty.unit ⊕' ((A ⊗ B) ⊗ (A ⊗ B)⋆)) ⨟ Term.sumF (Term.id Ty.unit)
                (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)))) :=
            PEq.compR _ (PEq.compL _ (PEq.cons_uncons _))
        _ ≡ₜ (Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆) ⨟ Term.sumF (Term.id Ty.unit)
              (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A))) :=
            PEq.compR _ (PEq.id_comp _)
        _ ≡ₜ _ := PEq.nat_inr _ _
    calc (Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A))
        ≡ₜ ((Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) ⨟
            Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B))) := PEq.symm (PEq.comp_id _)
      _ ≡ₜ ((Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) ⨟
            (Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)) ⨟
              Term.either (Term.anyTerm Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)))
                (Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B))))) :=
          PEq.compR _ (PEq.symm (Term.inr_retract Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B))))
      _ ≡ₜ (((Term.assocR A B ((A ⊗ B)⋆) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) ⨟
            Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B))) ⨟
              Term.either (Term.anyTerm Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)))
                (Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B)))) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ _ := PEq.compL _ (PEq.symm hpre)
  have hGLD : IsLiftDrop (Term.assocR A B ((A ⊗ B)⋆) ⨟
      Term.prodF (Term.id A) (Term.shiftL B A)) := by
    refine IsLiftDrop.congr hG (IsLiftDrop.comp (IsLiftDrop.comp ?_ ?_) ?_)
    · exact IsLiftDrop.of_isEqDrop (isEqDrop_prepend (A ⊗ B))
    · exact IsLiftDrop.of_isLift (IsLift.shift A B)
    · exact isLiftDrop_inrRetract Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B))
  refine IsLiftDrop.congr ?_ ((IsLiftDrop.of_isDrop (IsDrop.assocL A B ((A ⊗ B)⋆))).comp hGLD)
  calc Term.prodF (Term.id A) (Term.shiftL B A)
      ≡ₜ (Term.id (A ⊗ (B ⊗ (A ⊗ B)⋆)) ⨟ Term.prodF (Term.id A) (Term.shiftL B A)) :=
        PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((Term.assocL A B ((A ⊗ B)⋆) ⨟ Term.assocR A B ((A ⊗ B)⋆)) ⨟
          Term.prodF (Term.id A) (Term.shiftL B A)) :=
        PEq.compL _ (PEq.symm (PEq.assocL_assocR _ _ _))
    _ ≡ₜ _ := PEq.comp_assoc _ _ _

/-- `shiftL` admits a lift-drop factorisation. -/
theorem isLiftDrop_shiftL (X Y : Ty) : IsLiftDrop (Term.shiftL X Y) :=
  IsLiftDrop.of_prodF_id _ (isLiftDrop_prodF_shiftL Y X)

/-- `shiftR`, paired with an identity, admits a lift-drop factorisation. -/
theorem isLiftDrop_prodF_shiftR (A B : Ty) :
    IsLiftDrop (Term.prodF (Term.id A) (Term.shiftR B A)) := by
  -- the composite that `unshift` performs on a non-empty list
  have hpre : (Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)) ⨟ Term.unshift A B) ≡ₜ
      ((Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
        Term.prepend (A ⊗ B)) := by
    calc (Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)) ⨟
          (Term.sumF (Term.id Ty.unit)
            (Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
              Term.cons (A ⊗ B)))
        ≡ₜ ((Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)) ⨟
            Term.sumF (Term.id Ty.unit)
              (Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆))) ⨟
            Term.cons (A ⊗ B)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
            Term.inr Ty.unit ((A ⊗ B) ⊗ (A ⊗ B)⋆)) ⨟ Term.cons (A ⊗ B)) :=
          PEq.compL _ (PEq.nat_inr _ _)
      _ ≡ₜ _ := PEq.comp_assoc _ _ _
  have hH : (Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ≡ₜ
      ((Term.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)) ⨟ Term.unshift A B) ⨟
        Term.unprepend (A ⊗ B)) := by
    calc (Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆))
        ≡ₜ ((Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
            Term.id ((A ⊗ B) ⊗ (A ⊗ B)⋆)) := PEq.symm (PEq.comp_id _)
      _ ≡ₜ ((Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
            (Term.prepend (A ⊗ B) ⨟ Term.unprepend (A ⊗ B))) :=
          PEq.compR _ (PEq.symm (Term.prepend_unprepend (A ⊗ B)))
      _ ≡ₜ (((Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.assocL A B ((A ⊗ B)⋆)) ⨟
            Term.prepend (A ⊗ B)) ⨟ Term.unprepend (A ⊗ B)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ _ := PEq.compL _ (PEq.symm hpre)
  have hHLD : IsLiftDrop (Term.prodF (Term.id A) (Term.shiftR B A) ⨟
      Term.assocL A B ((A ⊗ B)⋆)) := by
    refine IsLiftDrop.congr hH (IsLiftDrop.comp ?_ (isLiftDrop_unprepend (A ⊗ B)))
    exact (IsLiftDrop.of_isDrop (IsDrop.inr Ty.unit (A ⊗ ((B ⊗ A)⋆ ⊗ B)))).comp
      (IsLiftDrop.of_isDrop (IsDrop.unshift A B))
  refine IsLiftDrop.congr ?_ (hHLD.comp (IsLiftDrop.of_isDrop (IsDrop.assocR A B ((A ⊗ B)⋆))))
  calc Term.prodF (Term.id A) (Term.shiftR B A)
      ≡ₜ (Term.prodF (Term.id A) (Term.shiftR B A) ⨟ Term.id (A ⊗ (B ⊗ (A ⊗ B)⋆))) :=
        PEq.symm (PEq.comp_id _)
    _ ≡ₜ (Term.prodF (Term.id A) (Term.shiftR B A) ⨟
          (Term.assocL A B ((A ⊗ B)⋆) ⨟ Term.assocR A B ((A ⊗ B)⋆))) :=
        PEq.compR _ (PEq.symm (PEq.assocL_assocR _ _ _))
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- `shiftR` admits a lift-drop factorisation. -/
theorem isLiftDrop_shiftR (X Y : Ty) : IsLiftDrop (Term.shiftR X Y) :=
  IsLiftDrop.of_prodF_id _ (isLiftDrop_prodF_shiftR Y X)

/-- The induction behind Lemma 7.4, with the exchange lemma (Lemma 7.5) taken as the
hypothesis `hex`. -/
theorem isLiftDrop_of_aperiodic_of (hex : type_of% @Lax149335.Exchange.exchange) :
    ∀ {A B : Ty} (f : Term A B), IsAperiodic f → IsLiftDrop f := by
  intro A B f
  induction f with
  | comp f g ihf ihg =>
      intro h
      rw [Term.isAperiodic_comp] at h
      exact IsLiftDrop.comp_of hex (ihf h.1) (ihg h.2)
  | prodF f g ihf ihg =>
      intro h
      rw [Term.isAperiodic_prodF] at h
      exact (ihf h.1).prodF (ihg h.2)
  | sumF f g ihf ihg =>
      intro h
      rw [Term.isAperiodic_sumF] at h
      exact (ihf h.1).sumF (ihg h.2)
  | listF f ih =>
      intro h
      rw [Term.isAperiodic_listF] at h
      exact (ih h).listF
  | id A => exact fun _ => IsLiftDrop.of_isLift (IsLift.id A)
  | inl A B => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.inl A B)
  | inr A B => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.inr A B)
  | codiag A => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.codiag A)
  | fst A B => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.fst A B)
  | snd A B => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.snd A B)
  | unitR A => exact fun _ => IsLiftDrop.of_isLift (IsLift.unitR A)
  | unitL A => exact fun _ => IsLiftDrop.of_isLift (IsLift.unitL A)
  | assocL A B C => exact fun _ => IsLiftDrop.of_isLift (IsLift.assocL A B C)
  | assocR A B C => exact fun _ => IsLiftDrop.of_isLift (IsLift.assocR A B C)
  | distR A B C => exact fun _ => IsLiftDrop.of_isLift (IsLift.distR A B C)
  | distL A B C => exact fun _ => IsLiftDrop.of_isLift (IsLift.distL A B C)
  | cons A => exact fun _ => IsLiftDrop.of_isEqDrop (isEqDrop_cons A)
  | uncons A => exact fun _ => isLiftDrop_uncons A
  | snoc A => exact fun _ => IsLiftDrop.of_isEqDrop (isEqDrop_snoc A)
  | unsnoc A => exact fun _ => isLiftDrop_unsnoc A
  | concat A => exact fun _ => IsLiftDrop.of_isDrop (IsDrop.concat A)
  | split A B => exact fun _ => IsLiftDrop.of_isLift (IsLift.split A B)
  | shiftR A B => exact fun _ => isLiftDrop_shiftR A B
  | shiftL A B => exact fun _ => isLiftDrop_shiftL A B
  | pref A G =>
      intro h
      exact absurd h (by simp [IsAperiodic, Term.usesPref])

/-- The induction behind Lemma 7.4. -/
theorem isLiftDrop_of_aperiodic {A B : Ty} (f : Term A B) (hf : IsAperiodic f) :
    IsLiftDrop f :=
  isLiftDrop_of_aperiodic_of exchange f hf

/-- **Lemma 7.4 (Lift-drop factorisation).**  Every aperiodic rational term is provably
equivalent to a composition of a lift followed by a drop. -/
theorem lift_drop_factorisation {A B : Ty} (f : Term A B) (hf : IsAperiodic f) :
    ∃ (C : Ty) (l : Term A C) (d : Term C B), IsLift l ∧ IsDrop d ∧ f ≡ₜ (l ⨟ d) :=
  isLiftDrop_of_aperiodic f hf

/-- **Completeness for drops.**  Two drops with the same denotation and with outputs that
are lists over a finite alphabet are provably equal.  This is the consequence of Lemma 7.3
and Lemma 6.1 that is noted in the paper right after Lemma 7.3. -/
theorem drop_completeness_of (h55 : type_of% @Lax149335.Cancellation.cancel)
    (h61 : type_of% @Lax149335.SimpleCompleteness.completeness_simple)
    (h73 : type_of% @Lax149335.JointSimplification.drops_to_simple)
    {A B : Ty} (hB : Ty.IsFinAlph B) (d₁ d₂ : Term A B⋆)
    (h₁ : IsDrop d₁) (h₂ : IsDrop d₂) (h : d₁.den = d₂.den) : d₁ ≡ₜ d₂ := by
  obtain ⟨C, l, π, -, -, hlπ, -, ⟨f', hf'simple, hf'⟩, ⟨g', hg'simple, hg'⟩⟩ :=
    h73 hB d₁ d₂ h₁ h₂
  have hden : f'.den = g'.den := by
    have e₁ : (π ⨟ d₁).den = f'.den := PEq.sound hf'
    have e₂ : (π ⨟ d₂).den = g'.den := PEq.sound hg'
    rw [← e₁, ← e₂]
    funext x
    simp [h]
  have hsimple : f' ≡ₜ g' :=
    (h61 hB f' g' hf'simple hg'simple (Term.nilT B)).1 hden
  have hcomp : (π ⨟ d₁) ≡ₜ (π ⨟ d₂) := hf'.trans (hsimple.trans hg'.symm)
  exact ((h55 d₁ d₂).2 C π ⟨l, hlπ⟩).2 hcomp

/-- **Corollary 7.6.**  If two aperiodic rational terms have the same denotation, then they
are provably equal.  Lemmas 5.5, 5.6, 6.1, 7.2, 7.3 and 7.4 are taken as hypotheses. -/
theorem completeness_aperiodic_of (h55 : type_of% @Lax149335.Cancellation.cancel)
    (h56 : type_of% @Lax149335.StringRepresentations.exists_injective_binary_encoding)
    (h61 : type_of% @Lax149335.SimpleCompleteness.completeness_simple)
    (h72 : type_of% @Lax149335.LiftInverses.lift_iso)
    (h73 : type_of% @Lax149335.JointSimplification.drops_to_simple)
    (h74 : type_of% @Lax149335.LiftDropFactorisation.lift_drop_factorisation)
    {A B : Ty} (f g : Term A B)
    (hf : IsAperiodic f) (hg : IsAperiodic g) (h : f.den = g.den) : f ≡ₜ g := by
  -- First reduce to the case of terms with outputs that are strings over a finite alphabet.
  obtain ⟨enc, hencap, hencinj⟩ := h56 B
  refine ((h55 f g).1 _ enc hencinj).2 ?_
  -- Factorise `f; enc` as a lift followed by a drop.
  obtain ⟨C, l, d₁, hl, hd₁, hfl⟩ :=
    h74 (f ⨟ enc) (by simp [hf, hencap])
  obtain ⟨π, hdπ, hlπ, hπl⟩ := h72 l hl
  -- Factorise `π; g; enc` as a lift followed by a drop; the two factorisations then share
  -- the common lift `l; l₂`.
  obtain ⟨π', hapπ', heπ'⟩ := hdπ.eqAperiodic
  obtain ⟨D, l₂, d₂, hl₂, hd₂, hgl⟩ :
      ∃ (D : Ty) (l₂ : Term C D) (d₂ : Term D _),
        IsLift l₂ ∧ IsDrop d₂ ∧ (π ⨟ (g ⨟ enc)) ≡ₜ (l₂ ⨟ d₂) := by
    obtain ⟨D, l₂, d₂, hl₂, hd₂, hgl⟩ :=
      h74 (π' ⨟ (g ⨟ enc)) (by simp [hapπ', hg, hencap])
    exact ⟨D, l₂, d₂, hl₂, hd₂, (PEq.compL _ heπ').trans hgl⟩
  obtain ⟨π₂, hdπ₂, hlπ₂, hπl₂⟩ := h72 l₂ hl₂
  set mu : Term A D := l ⨟ l₂ with hmu
  set nu : Term D A := π₂ ⨟ π with hnu
  -- `mu` is a provable isomorphism, hence its denotation is a bijection.
  have hmunu : (mu ⨟ nu) ≡ₜ Term.id A := by
    calc ((l ⨟ l₂) ⨟ (π₂ ⨟ π)) ≡ₜ (l ⨟ (l₂ ⨟ (π₂ ⨟ π))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (l ⨟ ((l₂ ⨟ π₂) ⨟ π)) := PEq.congr_comp (PEq.refl l) (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (l ⨟ (Term.id C ⨟ π)) :=
          PEq.congr_comp (PEq.refl l) (PEq.congr_comp hlπ₂ (PEq.refl π))
      _ ≡ₜ (l ⨟ π) := PEq.congr_comp (PEq.refl l) (PEq.id_comp π)
      _ ≡ₜ Term.id A := hlπ
  have hnumu : (nu ⨟ mu) ≡ₜ Term.id D := by
    calc ((π₂ ⨟ π) ⨟ (l ⨟ l₂)) ≡ₜ (π₂ ⨟ (π ⨟ (l ⨟ l₂))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (π₂ ⨟ ((π ⨟ l) ⨟ l₂)) :=
          PEq.congr_comp (PEq.refl π₂) (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (π₂ ⨟ (Term.id C ⨟ l₂)) :=
          PEq.congr_comp (PEq.refl π₂) (PEq.congr_comp hπl (PEq.refl l₂))
      _ ≡ₜ (π₂ ⨟ l₂) := PEq.congr_comp (PEq.refl π₂) (PEq.id_comp l₂)
      _ ≡ₜ Term.id D := hπl₂
  -- The two drops in the common factorisation.
  have hf2 : (f ⨟ enc) ≡ₜ (mu ⨟ (π₂ ⨟ d₁)) := by
    refine hfl.trans ?_
    calc (l ⨟ d₁) ≡ₜ (l ⨟ (Term.id C ⨟ d₁)) :=
          PEq.congr_comp (PEq.refl l) (PEq.symm (PEq.id_comp d₁))
      _ ≡ₜ (l ⨟ ((l₂ ⨟ π₂) ⨟ d₁)) :=
          PEq.congr_comp (PEq.refl l) (PEq.congr_comp (PEq.symm hlπ₂) (PEq.refl d₁))
      _ ≡ₜ (l ⨟ (l₂ ⨟ (π₂ ⨟ d₁))) := PEq.congr_comp (PEq.refl l) (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((l ⨟ l₂) ⨟ (π₂ ⨟ d₁)) := PEq.symm (PEq.comp_assoc _ _ _)
  have hg2 : (g ⨟ enc) ≡ₜ (mu ⨟ d₂) := by
    calc (g ⨟ enc) ≡ₜ (Term.id A ⨟ (g ⨟ enc)) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ ((l ⨟ π) ⨟ (g ⨟ enc)) := PEq.congr_comp (PEq.symm hlπ) (PEq.refl _)
      _ ≡ₜ (l ⨟ (π ⨟ (g ⨟ enc))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (l ⨟ (l₂ ⨟ d₂)) := PEq.congr_comp (PEq.refl l) hgl
      _ ≡ₜ ((l ⨟ l₂) ⨟ d₂) := PEq.symm (PEq.comp_assoc _ _ _)
  -- The two drops have the same denotation, because `mu` denotes a bijection.
  have hdrops : (π₂ ⨟ d₁).den = d₂.den := by
    have hmn : ∀ y : ⟦D⟧, mu.den (nu.den y) = y := by
      intro y
      have := PEq.sound hnumu
      exact congrFun this y
    have hcomp : (mu ⨟ (π₂ ⨟ d₁)).den = (mu ⨟ d₂).den := by
      rw [← PEq.sound hf2, ← PEq.sound hg2]
      funext x
      simp [h]
    funext y
    have h1 : (π₂ ⨟ d₁).den (mu.den (nu.den y)) = d₂.den (mu.den (nu.den y)) :=
      congrFun hcomp (nu.den y)
    rwa [hmn y] at h1
  have hd : (π₂ ⨟ d₁) ≡ₜ d₂ :=
    drop_completeness_of h55 h61 h73 ⟨1, rfl⟩ _ _ (IsDrop.comp hdπ₂ hd₁) hd₂ hdrops
  exact hf2.trans ((PEq.congr_comp (PEq.refl mu) hd).trans (PEq.symm hg2))

/-- **Corollary 7.6.**  If two aperiodic rational terms have the same denotation, then they
are provably equal. -/
theorem completeness_aperiodic {A B : Ty} (f g : Term A B)
    (hf : IsAperiodic f) (hg : IsAperiodic g) (h : f.den = g.den) : f ≡ₜ g :=
  completeness_aperiodic_of cancel exists_injective_binary_encoding completeness_simple lift_iso
    drops_to_simple lift_drop_factorisation f g hf hg h

end Lax149335Proofs

bridge_export Lax149335Proofs
