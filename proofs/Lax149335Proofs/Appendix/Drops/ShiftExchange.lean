import Lax149335Proofs.Appendix.Drops.ShiftListNode

/-!
# The shift exchange lemma (appendix, *Shift exchange lemma*)

This file formalises the special case of the exchange lemma (Lemma 7.5) in which the
drop-lift composition consists of a drop **in normal form** with codomain `(S × T)*`
followed by the prime lift `shift`.

The appendix section contains two statements.

* *The type `1 + S × (T × S)* × T` is injective.*  This is
  `Lax149335Proofs.Term.shiftCod_injective`, proved in `Lax149335Proofs.Appendix.Drops.InjectiveTypes`
  (together with the injectivity of `(S × T)*`, `Lax149335Proofs.Term.listPair_injective`, which the
  same proof establishes).
* *Shift exchange* (`Lax149335Proofs.exchange_normal_shift` below): for a drop in normal form
  `F(f⃗); genconc : F(A⃗) ⇒ (S × T)*`, the composition with `shift` is provably equal to a lift
  followed by a co-pairing of drops `g⃗`, where each `gᵢ` is either the constant `(1;1); Left`
  or of the shape

  `((snd; xᵢ) × (Hᵢ(h⃗ᵢ); genconc) × (fst; yᵢ)); Right`,

  with `x⃗, y⃗ ⪯ f⃗` and `Hᵢ(h⃗ᵢ); genconc` a drop in normal form with codomain `(T × S)*` whose
  leaves are of the restricted shapes `(1;v)`, `[(fst × id); k]` and `((fst × id); k)*`, with
  `k⃗ ⪯ f⃗`.

The three notions of shape that the conclusion uses are `Lax149335Proofs.IsShiftInnerLeaf` (the
restricted leaves), `Lax149335Proofs.IsShiftInnerForm` (the normal form built from them) and
`Lax149335Proofs.IsShiftExchangeShape` (the co-pairing of the `gᵢ`).

Two remarks on the reading of the statement.

* The appendix writes the codomain of the inner normal form, and of the drops `k⃗`, as
  `(S × T)*` and `S × T`; this is a typo for `(T × S)*` and `T × S`, which is the middle
  component of the codomain `1 + S × (T × S)* × T` of `shift`, and is what the use of the
  lemma in the proof of the list normalisation lemma requires.
* The `n`-ary co-pairing `either⃗ᵢ (gᵢ)` of the appendix is formalised, as everywhere in this
  development, by an arbitrary binary co-pairing tree (the constructor
  `Lax149335Proofs.IsShiftExchangeShape.either`), which the re-association of co-products that the
  appendix performs inside the lift `α` makes equivalent.

The consequences of the lemma are the case *Shift* of the list normalisation lemma
(`Lax149335Proofs.normListable_comp_unshift`, in `Lax149335Proofs.Appendix.Drops.UnshiftListNormal`) and the
case *Shift* of the exchange lemma (`Lax149335Proofs.admitsExchange_shift`, in
`Lax149335Proofs.Appendix.Drops.ExchangeShiftBlock`).

The three notions of shape are defined in `Lax149335Proofs.Appendix.Drops.ShiftShapes`, and the
content calculus that the proofs of the cases use is in
`Lax149335Proofs.Appendix.Drops.ShiftShapeContent`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The cases of the induction -/

/-- **Unit node**, `F = 1`: the empty list followed by `shift` is the left co-projection. -/
theorem shiftExch_nil (S T : Ty) (r : ℕ) : ShiftExch S T r (nilT (S ⊗ T)) := by
  refine ⟨Ty.unit, Term.id Ty.unit, _, IsLift.id Ty.unit,
    IsShiftExchangeShape.empty Ty.unit, ?_⟩
  calc (nilT (S ⊗ T) ⨟ Term.shift S T)
      ≡ₜ ((Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟ Term.unshift S T) ⨟ Term.shift S T) :=
        PEq.compL _ (PEq.symm (Term.inl_unshift S T))
    _ ≡ₜ (Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟
          (Term.unshift S T ⨟ Term.shift S T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟ Term.id (shiftCod S T)) :=
        PEq.compR _ (Term.unshift_shift S T)
    _ ≡ₜ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) := PEq.comp_id _
    _ ≡ₜ (Term.toUnit Ty.unit ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) :=
        PEq.symm ((PEq.compL _ (PEq.unit_unique (Term.toUnit Ty.unit)
          (Term.id Ty.unit))).trans (PEq.id_comp _))
    _ ≡ₜ (Term.id Ty.unit ⨟ (Term.toUnit Ty.unit ⨟
          Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)))) := PEq.symm (PEq.id_comp _)

/-- The two lifts `1 ⊸ 1 × 1` agree: appending a unit on the left or on the right of the
unit type is the same rebracketing. -/
theorem Term.unitL_unit_peq_unitR : Term.unitL Ty.unit ≡ₜ Term.unitR Ty.unit := by
  calc Term.unitL Ty.unit
      ≡ₜ (Term.unitL Ty.unit ⨟ Term.id (Ty.unit ⊗ Ty.unit)) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (Term.unitL Ty.unit ⨟ (Term.fst Ty.unit Ty.unit ⨟ Term.unitR Ty.unit)) :=
        PEq.compR _ (PEq.symm (PEq.fst_unitR Ty.unit))
    _ ≡ₜ ((Term.unitL Ty.unit ⨟ Term.fst Ty.unit Ty.unit) ⨟ Term.unitR Ty.unit) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id Ty.unit ⨟ Term.unitR Ty.unit) := PEq.compL _ (PEq.unit_unique _ _)
    _ ≡ₜ Term.unitR Ty.unit := PEq.id_comp _

/-- The lift `A ⊸ (1 × 1) × (A × (1 × 1))` which appends the units that the shape of the
conclusion of the shift exchange lemma requires around a constant triple. -/
def constTripleLift (A : Ty) : Term A ((Ty.unit ⊗ Ty.unit) ⊗ (A ⊗ (Ty.unit ⊗ Ty.unit))) :=
  Term.unitL A ⨟ Term.prodF (Term.unitL Ty.unit)
    (Term.unitR A ⨟ Term.prodF (Term.id A) (Term.unitL Ty.unit))

/-- Appending units is a lift. -/
theorem isLift_constTripleLift (A : Ty) : IsLift (constTripleLift A) :=
  IsLift.comp (IsLift.unitL A)
    (IsLift.prodF (IsLift.unitL Ty.unit)
      (IsLift.comp (IsLift.unitR A) (IsLift.prodF (IsLift.id A) (IsLift.unitL Ty.unit))))

/-- A constant triple of values, as produced by value completeness, is the constant lift
`constTripleLift` followed by a term of the shape required by the shift exchange lemma. -/
theorem const_triple_eq {S T : Ty} {A : Ty} (vs : Value S) (vl : Value ((T ⊗ S)⋆))
    (vt : Value T) :
    (Term.toUnit A ⨟ Term.pairR vs (Term.pairR vl vt)) ≡ₜ
      (constTripleLift A ⨟
        Term.prodF (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs))
          (Term.prodF (Term.toUnit A ⨟ vl)
            (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))) := by
  set P : Value (((T ⊗ S)⋆) ⊗ T) := Term.pairR vl vt with hP
  have h1 : (Term.unitL Ty.unit ⨟ (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs)))
      ≡ₜ vs := by
    calc (Term.unitL Ty.unit ⨟ (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs)))
        ≡ₜ ((Term.unitL Ty.unit ⨟ Term.snd Ty.unit Ty.unit) ⨟ (Term.toUnit Ty.unit ⨟ vs)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs)) :=
          PEq.compL _ (PEq.unitL_snd Ty.unit)
      _ ≡ₜ (Term.toUnit Ty.unit ⨟ vs) := PEq.id_comp _
      _ ≡ₜ (Term.id Ty.unit ⨟ vs) := PEq.compL _ (PEq.unit_unique _ _)
      _ ≡ₜ vs := PEq.id_comp _
  have h2 : ((Term.unitR A ⨟ Term.prodF (Term.id A) (Term.unitL Ty.unit)) ⨟
        Term.prodF (Term.toUnit A ⨟ vl)
          (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))
      ≡ₜ (Term.toUnit A ⨟ P) := by
    have hy : (Term.unitL Ty.unit ⨟ (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))
        ≡ₜ vt := by
      calc (Term.unitL Ty.unit ⨟ (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))
          ≡ₜ ((Term.unitL Ty.unit ⨟ Term.fst Ty.unit Ty.unit) ⨟ (Term.toUnit Ty.unit ⨟ vt)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)) :=
            PEq.compL _ (PEq.unit_unique _ _)
        _ ≡ₜ (Term.toUnit Ty.unit ⨟ vt) := PEq.id_comp _
        _ ≡ₜ (Term.id Ty.unit ⨟ vt) := PEq.compL _ (PEq.unit_unique _ _)
        _ ≡ₜ vt := PEq.id_comp _
    calc ((Term.unitR A ⨟ Term.prodF (Term.id A) (Term.unitL Ty.unit)) ⨟
          Term.prodF (Term.toUnit A ⨟ vl)
            (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))
        ≡ₜ (Term.unitR A ⨟ (Term.prodF (Term.id A) (Term.unitL Ty.unit) ⨟
              Term.prodF (Term.toUnit A ⨟ vl)
                (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.unitR A ⨟ Term.prodF (Term.id A ⨟ (Term.toUnit A ⨟ vl))
              (Term.unitL Ty.unit ⨟
                (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))) :=
          PEq.compR _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (Term.unitR A ⨟ Term.prodF (Term.toUnit A ⨟ vl) vt) :=
          PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) hy)
      _ ≡ₜ (Term.unitR A ⨟ Term.prodF (Term.toUnit A ⨟ vl) (Term.id Ty.unit ⨟ vt)) :=
          PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.id_comp _)))
      _ ≡ₜ (Term.unitR A ⨟ (Term.prodF (Term.toUnit A) (Term.id Ty.unit) ⨟
              Term.prodF vl vt)) := PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _))
      _ ≡ₜ ((Term.unitR A ⨟ Term.prodF (Term.toUnit A) (Term.id Ty.unit)) ⨟
              Term.prodF vl vt) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((Term.toUnit A ⨟ Term.unitR Ty.unit) ⨟ Term.prodF vl vt) :=
          PEq.compL _ (PEq.symm (PEq.nat_unitR (Term.toUnit A)))
      _ ≡ₜ (Term.toUnit A ⨟ (Term.unitR Ty.unit ⨟ Term.prodF vl vt)) := PEq.comp_assoc _ _ _
  calc (Term.toUnit A ⨟ Term.pairR vs P)
      ≡ₜ (Term.toUnit A ⨟ (Term.unitL Ty.unit ⨟ Term.prodF vs P)) :=
        PEq.compR _ (PEq.compL _ (PEq.symm Term.unitL_unit_peq_unitR))
    _ ≡ₜ ((Term.toUnit A ⨟ Term.unitL Ty.unit) ⨟ Term.prodF vs P) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.unitL A ⨟ Term.prodF (Term.id Ty.unit) (Term.toUnit A)) ⨟ Term.prodF vs P) :=
        PEq.compL _ (PEq.nat_unitL (Term.toUnit A))
    _ ≡ₜ (Term.unitL A ⨟ (Term.prodF (Term.id Ty.unit) (Term.toUnit A) ⨟ Term.prodF vs P)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.unitL A ⨟ Term.prodF (Term.id Ty.unit ⨟ vs) (Term.toUnit A ⨟ P)) :=
        PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.unitL A ⨟ Term.prodF vs (Term.toUnit A ⨟ P)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))
    _ ≡ₜ (Term.unitL A ⨟ Term.prodF
            (Term.unitL Ty.unit ⨟ (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs)))
            ((Term.unitR A ⨟ Term.prodF (Term.id A) (Term.unitL Ty.unit)) ⨟
              Term.prodF (Term.toUnit A ⨟ vl)
                (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt)))) :=
        PEq.compR _ (PEq.congr_prodF (PEq.symm h1) (PEq.symm h2))
    _ ≡ₜ (Term.unitL A ⨟ (Term.prodF (Term.unitL Ty.unit)
            (Term.unitR A ⨟ Term.prodF (Term.id A) (Term.unitL Ty.unit)) ⨟
          Term.prodF (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vs))
            (Term.prodF (Term.toUnit A ⨟ vl)
              (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ vt))))) :=
        PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _))
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- **Leaf node, value**, `f = 1;v`: a constant list of pairs, followed by `shift`, is a
constant of the codomain of `shift`, which by value completeness is either the empty
summand or a triple of values. -/
theorem shiftExch_const {S T : Ty} {r : ℕ} {A : Ty} (v : Value ((S ⊗ T)⋆)) :
    ShiftExch S T r (Term.toUnit A ⨟ v) := by
  obtain ⟨z, hz⟩ : ∃ z, (v ⨟ Term.shift S T) ≡ₜ encV (shiftCod S T) z :=
    ⟨_, PEq.trans (PEq.symm (PEq.id_comp _)) (computes (v ⨟ Term.shift S T) ())⟩
  cases z with
  | inl u =>
      refine ⟨A, Term.id A, Term.toUnit A ⨟ Term.inl Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)),
        IsLift.id A, IsShiftExchangeShape.empty A, ?_⟩
      calc ((Term.toUnit A ⨟ v) ⨟ Term.shift S T)
          ≡ₜ (Term.toUnit A ⨟ (v ⨟ Term.shift S T)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.toUnit A ⨟ (Term.id Ty.unit ⨟ Term.inl Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)))) :=
            PEq.compR _ hz
        _ ≡ₜ (Term.toUnit A ⨟ Term.inl Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T))) :=
            PEq.compR _ (PEq.id_comp _)
        _ ≡ₜ (Term.id A ⨟ (Term.toUnit A ⨟ Term.inl Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)))) :=
            PEq.symm (PEq.id_comp _)
  | inr p =>
      obtain ⟨s, l, t⟩ := p
      refine ⟨(Ty.unit ⊗ Ty.unit) ⊗ (A ⊗ (Ty.unit ⊗ Ty.unit)), constTripleLift A,
        Term.prodF (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ encV S s))
            (Term.prodF (Term.toUnit A ⨟ encV ((T ⊗ S)⋆) l)
              (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ encV T t))) ⨟
          Term.inr Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)),
        isLift_constTripleLift A,
        IsShiftExchangeShape.inner (IsDrop.bangV _ _) ?_ (IsDrop.bangV _ _) ?_
          (IsShiftInnerForm.leaf (IsShiftInnerLeaf.const _)), ?_⟩
      · rw [rank_const]; exact Nat.zero_le r
      · rw [rank_const]; exact Nat.zero_le r
      · calc ((Term.toUnit A ⨟ v) ⨟ Term.shift S T)
            ≡ₜ (Term.toUnit A ⨟ (v ⨟ Term.shift S T)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (Term.toUnit A ⨟ (Term.pairR (encV S s)
                (Term.pairR (encV ((T ⊗ S)⋆) l) (encV T t)) ⨟
                Term.inr Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T)))) := PEq.compR _ hz
          _ ≡ₜ ((Term.toUnit A ⨟ Term.pairR (encV S s)
                (Term.pairR (encV ((T ⊗ S)⋆) l) (encV T t))) ⨟
                Term.inr Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T))) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((constTripleLift A ⨟
                Term.prodF (Term.snd Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ encV S s))
                  (Term.prodF (Term.toUnit A ⨟ encV ((T ⊗ S)⋆) l)
                    (Term.fst Ty.unit Ty.unit ⨟ (Term.toUnit Ty.unit ⨟ encV T t)))) ⨟
                Term.inr Ty.unit (S ⊗ ((T ⊗ S)⋆ ⊗ T))) :=
              PEq.compL _ (const_triple_eq _ _ _)
          _ ≡ₜ _ := PEq.comp_assoc _ _ _

/-- **Leaf node, singleton**, `f = [k]`: the shifted singleton is a single pair, with an
empty middle component. -/
theorem shiftExch_sing {S T : Ty} {r : ℕ} {A : Ty} {k : Term A (S ⊗ T)} (hk : IsDrop k)
    (hr : rank k ≤ r) : ShiftExch S T r (k ⨟ pureT (S ⊗ T)) := by
  obtain ⟨D, alpha, g, ha, _, hnorm, he⟩ := drops_with_prod_codomain_of_rank k hk
  refine ShiftExch_of_SC (SC.congr ?_ (SC.mono hr (SC.lift_comp ha (SC.of_normalProd hnorm))))
  calc ((k ⨟ pureT (S ⊗ T)) ⨟ pairContent S T)
      ≡ₜ (k ⨟ (pureT (S ⊗ T) ⨟ pairContent S T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (k ⨟ (sLetter S T ⊙ tLetter S T)) := PEq.compR _ (homT_pure _)
    _ ≡ₜ ((alpha ⨟ g) ⨟ (sLetter S T ⊙ tLetter S T)) := PEq.compL _ he
    _ ≡ₜ (alpha ⨟ (g ⨟ (sLetter S T ⊙ tLetter S T))) := PEq.comp_assoc _ _ _

/-- **Product node**, `F = F₁ × F₂`. -/
theorem shiftExch_fdot {S T : Ty} {r : ℕ} {A₁ A₂ : Ty} {f₁ : Term A₁ ((S ⊗ T)⋆)}
    {f₂ : Term A₂ ((S ⊗ T)⋆)} (h₁ : ShiftExch S T r f₁) (h₂ : ShiftExch S T r f₂) :
    ShiftExch S T r (f₁ ⊙ f₂) := by
  refine ShiftExch_of_SC (SC.congr ?_ (SC.fdot (SC_of_ShiftExch h₁) (SC_of_ShiftExch h₂)))
  exact fdot_comp_homT _ _ _

/-- **List node**, `F = G*`. -/
theorem shiftExch_homT {S T : Ty} {r : ℕ} {A : Ty} {f : Term A ((S ⊗ T)⋆)}
    (h : ShiftExch S T r f) : ShiftExch S T r (Term.homT f) := by
  refine ShiftExch_of_SC (SC.congr ?_ (SC.homT (SC_of_ShiftExch h)))
  exact homT_comp f (sLetter S T ⊙ tLetter S T)

/-- **Leaf node, list**, `f = k*`: this is the list node applied to a singleton leaf, since
`k* = hom [k]`. -/
theorem shiftExch_map {S T : Ty} {r : ℕ} {A : Ty} {k : Term A (S ⊗ T)} (hk : IsDrop k)
    (hr : rank k ≤ r) : ShiftExch S T r (listF k) := by
  refine ShiftExch.congr ?_ (shiftExch_homT (shiftExch_sing hk hr))
  calc listF k ≡ₜ (listF k ⨟ Term.id ((S ⊗ T)⋆)) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (listF k ⨟ (listF (pureT (S ⊗ T)) ⨟ concat (S ⊗ T))) :=
        PEq.compR _ (PEq.symm (PEq.listF_pure_concat (S ⊗ T)))
    _ ≡ₜ ((listF k ⨟ listF (pureT (S ⊗ T))) ⨟ concat (S ⊗ T)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (listF (k ⨟ pureT (S ⊗ T)) ⨟ concat (S ⊗ T)) := PEq.compL _ (PEq.list_comp _ _)

/-- A leaf of a normal form satisfies the conclusion of the shift exchange lemma. -/
theorem shiftExch_of_leaf {S T : Ty} {r : ℕ} : {A : Ty} → {f : Term A ((S ⊗ T)⋆)} →
    IsNormalListLeafLe (S ⊗ T) r f → ShiftExch S T r f
  | _, _, .const v => shiftExch_const v
  | _, _, .sing hk hr => shiftExch_sing hk hr
  | _, _, .map hk hr => shiftExch_map hk hr

/-! ### The lemma -/

/-- **Lemma (Shift exchange)** (appendix).  A drop in normal form with codomain `(S × T)*`,
followed by the prime lift `shift`, is provably equal to a lift followed by a co-pairing of
drops of the two shapes of `Lax149335Proofs.IsShiftExchangeShape`: the constant `(1;1); Left`, and
`((snd; x) × (m × (fst; y))); Right` where `m` is an inner normal form with codomain
`(T × S)*`.

The rank bounds are the appendix's `⪯`: the drops `x`, `y` and the drops `k` inside the
leaves of `m` have at most the rank bound of the leaves of the given normal form. -/
theorem exchange_normal_shift {S T : Ty} {r : ℕ} {A : Ty} {f : Term A ((S ⊗ T)⋆)}
    (hf : IsListNormalForm (S ⊗ T) r f) :
    ∃ (D : Ty) (alpha : Term A D) (g : Term D (shiftCod S T)),
      IsLift alpha ∧ IsShiftExchangeShape S T r g ∧ (f ⨟ Term.shift S T) ≡ₜ (alpha ⨟ g) := by
  induction hf with
  | leaf hl => exact shiftExch_of_leaf hl
  | nil => exact shiftExch_nil _ _ _
  | fdot _ _ ih₁ ih₂ => exact shiftExch_fdot ih₁ ih₂
  | either _ _ ih₁ ih₂ => exact ShiftExch.either ih₁ ih₂
  | homT _ ih => exact shiftExch_homT ih

end Lax149335Proofs

bridge_export Lax149335Proofs
