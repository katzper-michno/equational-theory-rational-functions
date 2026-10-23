import Lax149335Proofs.Appendix.ConjugacyRule.Soundness
import Lax149335Proofs.Appendix.Drops.ShiftShapes
import Lax149335Proofs.Appendix.Drops.SumProdNormalisation
import Lax149335Proofs.Appendix.Drops.Contents

/-!
# The content calculus of the shift exchange lemma

The codomain of `shift` is an injective type (`Lax149335Proofs.Term.shiftCod_injective`), so an
equation between two terms with that codomain may be proved by comparing the *contents* of
the two sides, that is, their images in `(S + T)*` under the concatenation map
`Lax149335Proofs.shiftContent`.  This file sets up that reduction for the shift exchange lemma:

* `Lax149335Proofs.SC` is the conclusion of the lemma, read on contents: a content is `SC` if it is
  provably equal to a lift followed by the content of a drop of the shape
  `Lax149335Proofs.IsShiftExchangeShape`;
* `Lax149335Proofs.ShiftExch_of_SC` turns a content statement back into the statement about `shift`
  that the lemma asks for;
* the closure properties of `SC` that the cases of the induction need: constants, the two
  ways of erasing a factor that carries no letter of the conclusion, co-pairings, and the
  basic non-empty shape.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty} {r : ℕ}

/-! ### Contents -/

/-- The content of a list of `(T × S)`-pairs, read in `(S + T)*`. -/
def pairContentTS (S T : Ty) : Term ((T ⊗ S)⋆) ((S ⊕' T)⋆) :=
  homT (tLetter S T ⊙ sLetter S T)

/-- The content of the empty component of a shape. -/
theorem content_empty (S T : Ty) (A : Ty) :
    ((toUnit A ⨟ inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T) ≡ₜ
      (toUnit A ⨟ nilT (S ⊕' T)) :=
  (PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either _ _))

/-- The content of a non-empty component of a shape. -/
theorem content_inner {W X M Y V : Ty} (x : Term X S) (m : Term M ((T ⊗ S)⋆)) (y : Term Y T) :
    ((prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
        inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T) ≡ₜ
      (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙
        ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))) := by
  calc ((prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
        inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T)
      ≡ₜ (prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
          (inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T)) ⨟ shiftContent S T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
          (sLetter S T ⊙ (pairContentTS S T ⊙ tLetter S T))) :=
        PEq.compR _ (inr_either _ _)
    _ ≡ₜ (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙
          (prodF m (Term.fst Y V ⨟ y) ⨟ (pairContentTS S T ⊙ tLetter S T))) :=
        fdot_precomp _ _ _ _
    _ ≡ₜ (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙
          ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))) :=
        fdot_congr (PEq.refl _) (fdot_precomp _ _ _ _)

/-! ### The conclusion of the lemma, read on contents -/

/-- `SC S T r c` says that the content `c` is provably equal to a lift followed by the
content of a drop of the shape of `Lax149335Proofs.IsShiftExchangeShape`. -/
def SC (S T : Ty) (r : ℕ) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (D : Ty) (alpha : Term A D) (g : Term D (shiftCod S T)),
    IsLift alpha ∧ IsShiftExchangeShape S T r g ∧ c ≡ₜ (alpha ⨟ (g ⨟ shiftContent S T))

namespace SC

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : SC S T r c') :
    SC S T r c :=
  let ⟨D, alpha, g, ha, hg, he⟩ := hc
  ⟨D, alpha, g, ha, hg, h.trans he⟩

theorem mono {r' : ℕ} (h : r ≤ r') {A : Ty} {c : Term A ((S ⊕' T)⋆)} (hc : SC S T r c) :
    SC S T r' c :=
  let ⟨D, alpha, g, ha, hg, he⟩ := hc
  ⟨D, alpha, g, ha, hg.mono h, he⟩

/-- Pre-composing a content with a lift. -/
theorem lift_comp {A A' : Ty} {beta : Term A' A} (hb : IsLift beta)
    {c : Term A ((S ⊕' T)⋆)} (hc : SC S T r c) : SC S T r (beta ⨟ c) :=
  let ⟨D, alpha, g, ha, hg, he⟩ := hc
  ⟨D, beta ⨟ alpha, g, IsLift.comp hb ha, hg,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

/-- The constant empty content. -/
theorem empty (S T : Ty) (r : ℕ) (A : Ty) : SC S T r (toUnit A ⨟ nilT (S ⊕' T)) :=
  ⟨A, Term.id A, _, IsLift.id A, IsShiftExchangeShape.empty A,
    (PEq.symm (content_empty S T A)).trans (PEq.symm (PEq.id_comp _))⟩

/-- A co-pairing of two contents. -/
theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SC S T r c₁) (h₂ : SC S T r c₂) : SC S T r (Term.either c₁ c₂) := by
  obtain ⟨D₁, a₁, g₁, ha₁, hg₁, he₁⟩ := h₁
  obtain ⟨D₂, a₂, g₂, ha₂, hg₂, he₂⟩ := h₂
  refine ⟨D₁ ⊕' D₂, sumF a₁ a₂, Term.either g₁ g₂, IsLift.sumF ha₁ ha₂, hg₁.either hg₂, ?_⟩
  calc Term.either c₁ c₂
      ≡ₜ Term.either (a₁ ⨟ (g₁ ⨟ shiftContent S T)) (a₂ ⨟ (g₂ ⨟ shiftContent S T)) :=
        Term.either_congr he₁ he₂
    _ ≡ₜ (sumF a₁ a₂ ⨟ Term.either (g₁ ⨟ shiftContent S T) (g₂ ⨟ shiftContent S T)) :=
        PEq.symm (Term.sumF_either _ _ _ _)
    _ ≡ₜ (sumF a₁ a₂ ⨟ (Term.either g₁ g₂ ⨟ shiftContent S T)) :=
        PEq.compR _ (PEq.symm (Term.either_comp _ _ _))

end SC

/-! ### The basic non-empty content -/

/-- The content of a non-empty component, as an `SC`: a letter of `S` preceded by a factor
that is erased, an inner normal form, and a letter of `T` followed by a factor that is
erased. -/
theorem SC.inner_junk {W X M Y V : Ty} {x : Term X S} {m : Term M ((T ⊗ S)⋆)} {y : Term Y T}
    (hx : IsDrop x) (hrx : rank x ≤ r) (hy : IsDrop y) (hry : rank y ≤ r)
    (hm : IsShiftInnerForm S T r m) :
    SC S T r (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙
      ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))) :=
  ⟨(W ⊗ X) ⊗ (M ⊗ (Y ⊗ V)), Term.id ((W ⊗ X) ⊗ (M ⊗ (Y ⊗ V))), _,
    IsLift.id _, IsShiftExchangeShape.inner hx hrx hy hry hm,
    (PEq.symm (content_inner x m y)).trans (PEq.symm (PEq.id_comp _))⟩

/-! ### Erasing a factor -/

/-- Erasing a factor on the left of a concatenation. -/
theorem snd_fdot {W A₁ A₂ D : Ty} (c₁ : Term A₁ D⋆) (c₂ : Term A₂ D⋆) :
    (Term.snd W (A₁ ⊗ A₂) ⨟ (c₁ ⊙ c₂)) ≡ₜ
      (assocL W A₁ A₂ ⨟ ((Term.snd W A₁ ⨟ c₁) ⊙ c₂)) := by
  have hkey : (assocL W A₁ A₂ ⨟ prodF (Term.snd W A₁) (Term.id A₂)) ≡ₜ
      Term.snd W (A₁ ⊗ A₂) := by
    calc (assocL W A₁ A₂ ⨟ prodF (Term.snd W A₁) (Term.id A₂))
        ≡ₜ (assocL W A₁ A₂ ⨟ (assocR W A₁ A₂ ⨟ Term.snd W (A₁ ⊗ A₂))) :=
          PEq.compR _ (PEq.symm (Term.assocR_snd W A₁ A₂))
      _ ≡ₜ ((assocL W A₁ A₂ ⨟ assocR W A₁ A₂) ⨟ Term.snd W (A₁ ⊗ A₂)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (W ⊗ (A₁ ⊗ A₂)) ⨟ Term.snd W (A₁ ⊗ A₂)) :=
          PEq.compL _ (PEq.assocL_assocR _ _ _)
      _ ≡ₜ Term.snd W (A₁ ⊗ A₂) := PEq.id_comp _
  calc (Term.snd W (A₁ ⊗ A₂) ⨟ (c₁ ⊙ c₂))
      ≡ₜ ((assocL W A₁ A₂ ⨟ prodF (Term.snd W A₁) (Term.id A₂)) ⨟ (c₁ ⊙ c₂)) :=
        PEq.compL _ (PEq.symm hkey)
    _ ≡ₜ (assocL W A₁ A₂ ⨟ (prodF (Term.snd W A₁) (Term.id A₂) ⨟ (c₁ ⊙ c₂))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL W A₁ A₂ ⨟ ((Term.snd W A₁ ⨟ c₁) ⊙ (Term.id A₂ ⨟ c₂))) :=
        PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (assocL W A₁ A₂ ⨟ ((Term.snd W A₁ ⨟ c₁) ⊙ c₂)) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (PEq.id_comp _))

/-- Erasing a factor on the right of a concatenation. -/
theorem fst_fdot {V A₁ A₂ D : Ty} (c₁ : Term A₁ D⋆) (c₂ : Term A₂ D⋆) :
    (Term.fst (A₁ ⊗ A₂) V ⨟ (c₁ ⊙ c₂)) ≡ₜ
      (assocR A₁ A₂ V ⨟ (c₁ ⊙ (Term.fst A₂ V ⨟ c₂))) := by
  have hkey : (assocR A₁ A₂ V ⨟ prodF (Term.id A₁) (Term.fst A₂ V)) ≡ₜ
      Term.fst (A₁ ⊗ A₂) V := by
    calc (assocR A₁ A₂ V ⨟ prodF (Term.id A₁) (Term.fst A₂ V))
        ≡ₜ (assocR A₁ A₂ V ⨟ (assocL A₁ A₂ V ⨟ Term.fst (A₁ ⊗ A₂) V)) :=
          PEq.compR _ (PEq.symm (Term.assocL_fst A₁ A₂ V))
      _ ≡ₜ ((assocR A₁ A₂ V ⨟ assocL A₁ A₂ V) ⨟ Term.fst (A₁ ⊗ A₂) V) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id ((A₁ ⊗ A₂) ⊗ V) ⨟ Term.fst (A₁ ⊗ A₂) V) :=
          PEq.compL _ (PEq.assocR_assocL _ _ _)
      _ ≡ₜ Term.fst (A₁ ⊗ A₂) V := PEq.id_comp _
  calc (Term.fst (A₁ ⊗ A₂) V ⨟ (c₁ ⊙ c₂))
      ≡ₜ ((assocR A₁ A₂ V ⨟ prodF (Term.id A₁) (Term.fst A₂ V)) ⨟ (c₁ ⊙ c₂)) :=
        PEq.compL _ (PEq.symm hkey)
    _ ≡ₜ (assocR A₁ A₂ V ⨟ (prodF (Term.id A₁) (Term.fst A₂ V) ⨟ (c₁ ⊙ c₂))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (assocR A₁ A₂ V ⨟ ((Term.id A₁ ⨟ c₁) ⊙ (Term.fst A₂ V ⨟ c₂))) :=
        PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (assocR A₁ A₂ V ⨟ (c₁ ⊙ (Term.fst A₂ V ⨟ c₂))) :=
        PEq.compR _ (fdot_congr (PEq.id_comp _) (PEq.refl _))

/-- Erasing a factor before a co-pairing. -/
theorem snd_either {W A₁ A₂ B : Ty} (c₁ : Term A₁ B) (c₂ : Term A₂ B) :
    (Term.snd W (A₁ ⊕' A₂) ⨟ Term.either c₁ c₂) ≡ₜ
      (distR W A₁ A₂ ⨟ Term.either (Term.snd W A₁ ⨟ c₁) (Term.snd W A₂ ⨟ c₂)) := by
  calc (Term.snd W (A₁ ⊕' A₂) ⨟ Term.either c₁ c₂)
      ≡ₜ ((distR W A₁ A₂ ⨟ sumF (Term.snd W A₁) (Term.snd W A₂)) ⨟ Term.either c₁ c₂) :=
        PEq.compL _ (PEq.symm (Term.distR_snd W A₁ A₂))
    _ ≡ₜ (distR W A₁ A₂ ⨟ (sumF (Term.snd W A₁) (Term.snd W A₂) ⨟ Term.either c₁ c₂)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distR W A₁ A₂ ⨟ Term.either (Term.snd W A₁ ⨟ c₁) (Term.snd W A₂ ⨟ c₂)) :=
        PEq.compR _ (Term.sumF_either _ _ _ _)

/-- Erasing a factor after a co-pairing. -/
theorem fst_either {V A₁ A₂ B : Ty} (c₁ : Term A₁ B) (c₂ : Term A₂ B) :
    (Term.fst (A₁ ⊕' A₂) V ⨟ Term.either c₁ c₂) ≡ₜ
      (distL A₁ A₂ V ⨟ Term.either (Term.fst A₁ V ⨟ c₁) (Term.fst A₂ V ⨟ c₂)) := by
  calc (Term.fst (A₁ ⊕' A₂) V ⨟ Term.either c₁ c₂)
      ≡ₜ ((distL A₁ A₂ V ⨟ sumF (Term.fst A₁ V) (Term.fst A₂ V)) ⨟ Term.either c₁ c₂) :=
        PEq.compL _ (PEq.symm (distL_fst A₁ A₂ V))
    _ ≡ₜ (distL A₁ A₂ V ⨟ (sumF (Term.fst A₁ V) (Term.fst A₂ V) ⨟ Term.either c₁ c₂)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distL A₁ A₂ V ⨟ Term.either (Term.fst A₁ V ⨟ c₁) (Term.fst A₂ V ⨟ c₂)) :=
        PEq.compR _ (Term.sumF_either _ _ _ _)

/-- Erasing a factor that carries no letter of the conclusion, on the left. -/
theorem IsShiftExchangeShape.sc_snd (W : Ty) : {D : Ty} → {g : Term D (shiftCod S T)} →
    IsShiftExchangeShape S T r g → SC S T r (Term.snd W D ⨟ (g ⨟ shiftContent S T))
  | _, _, .empty A => by
      refine SC.congr ?_ (SC.empty S T r (W ⊗ A))
      calc (Term.snd W A ⨟ ((toUnit A ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟
            shiftContent S T))
          ≡ₜ (Term.snd W A ⨟ (toUnit A ⨟ nilT (S ⊕' T))) :=
            PEq.compR _ (content_empty S T A)
        _ ≡ₜ ((Term.snd W A ⨟ toUnit A) ⨟ nilT (S ⊕' T)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (toUnit (W ⊗ A) ⨟ nilT (S ⊕' T)) :=
            PEq.compL _ (PEq.unit_unique _ _)
  | _, _, @IsShiftExchangeShape.inner _ _ _ W' X M Y V x y m hx hrx hy hry hm => by
      set u : Term (W' ⊗ X) ((S ⊕' T)⋆) := (Term.snd W' X ⨟ x) ⨟ sLetter S T with hu
      set w : Term (M ⊗ (Y ⊗ V)) ((S ⊕' T)⋆) :=
        (m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T) with hw
      have hju : (Term.snd W (W' ⊗ X) ⨟ u) ≡ₜ
          (assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) := by
        calc (Term.snd W (W' ⊗ X) ⨟ ((Term.snd W' X ⨟ x) ⨟ sLetter S T))
            ≡ₜ ((Term.snd W (W' ⊗ X) ⨟ (Term.snd W' X ⨟ x)) ⨟ sLetter S T) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (((Term.snd W (W' ⊗ X) ⨟ Term.snd W' X) ⨟ x) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (((assocL W W' X ⨟ Term.snd (W ⊗ W') X) ⨟ x) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.compL _ (snd_snd_assocL W W' X))
          _ ≡ₜ ((assocL W W' X ⨟ (Term.snd (W ⊗ W') X ⨟ x)) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ (assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) :=
              PEq.comp_assoc _ _ _
      refine SC.congr ?_ (SC.lift_comp
        (IsLift.comp (IsLift.assocL W (W' ⊗ X) (M ⊗ (Y ⊗ V)))
          (IsLift.prodF (IsLift.assocL W W' X) (IsLift.id (M ⊗ (Y ⊗ V)))))
        (SC.inner_junk (W := W ⊗ W') (V := V) hx hrx hy hry hm))
      calc (Term.snd W ((W' ⊗ X) ⊗ (M ⊗ (Y ⊗ V))) ⨟
            ((prodF (Term.snd W' X ⨟ x) (prodF m (Term.fst Y V ⨟ y)) ⨟
              Term.inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T))
          ≡ₜ (Term.snd W ((W' ⊗ X) ⊗ (M ⊗ (Y ⊗ V))) ⨟ (u ⊙ w)) :=
            PEq.compR _ (content_inner x m y)
        _ ≡ₜ (assocL W (W' ⊗ X) (M ⊗ (Y ⊗ V)) ⨟ ((Term.snd W (W' ⊗ X) ⨟ u) ⊙ w)) :=
            snd_fdot _ _
        _ ≡ₜ (assocL W (W' ⊗ X) (M ⊗ (Y ⊗ V)) ⨟
              ((assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) ⊙ w)) :=
            PEq.compR _ (fdot_congr hju (PEq.refl _))
        _ ≡ₜ (assocL W (W' ⊗ X) (M ⊗ (Y ⊗ V)) ⨟
              (prodF (assocL W W' X) (Term.id (M ⊗ (Y ⊗ V))) ⨟
                (((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T) ⊙ w))) :=
            PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
              (fdot_congr (PEq.refl _) (PEq.id_comp _))))
        _ ≡ₜ ((assocL W (W' ⊗ X) (M ⊗ (Y ⊗ V)) ⨟
              prodF (assocL W W' X) (Term.id (M ⊗ (Y ⊗ V)))) ⨟
                (((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T) ⊙ w)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
  | _, _, .either h₁ h₂ => by
      refine SC.congr ?_ (SC.lift_comp (IsLift.distR W _ _)
        (SC.either (h₁.sc_snd W) (h₂.sc_snd W)))
      calc (Term.snd W _ ⨟ (Term.either _ _ ⨟ shiftContent S T))
          ≡ₜ (Term.snd W _ ⨟ Term.either (_ ⨟ shiftContent S T) (_ ⨟ shiftContent S T)) :=
            PEq.compR _ (Term.either_comp _ _ _)
        _ ≡ₜ _ := snd_either _ _

/-- Coherence between the first projection and the associator: two successive first
projections are the right associator followed by one. -/
theorem fst_fst_assocR (A B C : Ty) :
    (Term.fst (A ⊗ B) C ⨟ Term.fst A B) ≡ₜ (assocR A B C ⨟ Term.fst A (B ⊗ C)) := by
  have key : (assocL A B C ⨟ (Term.fst (A ⊗ B) C ⨟ Term.fst A B)) ≡ₜ Term.fst A (B ⊗ C) := by
    calc (assocL A B C ⨟ (Term.fst (A ⊗ B) C ⨟ Term.fst A B))
        ≡ₜ ((assocL A B C ⨟ Term.fst (A ⊗ B) C) ⨟ Term.fst A B) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id A) (Term.fst B C) ⨟ Term.fst A B) :=
          PEq.compL _ (Term.assocL_fst A B C)
      _ ≡ₜ (Term.fst A (B ⊗ C) ⨟ Term.id A) := PEq.nat_fst _ _
      _ ≡ₜ Term.fst A (B ⊗ C) := PEq.comp_id _
  calc (Term.fst (A ⊗ B) C ⨟ Term.fst A B)
      ≡ₜ (Term.id ((A ⊗ B) ⊗ C) ⨟ (Term.fst (A ⊗ B) C ⨟ Term.fst A B)) :=
        PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocR A B C ⨟ assocL A B C) ⨟ (Term.fst (A ⊗ B) C ⨟ Term.fst A B)) :=
        PEq.compL _ (PEq.symm (PEq.assocR_assocL A B C))
    _ ≡ₜ (assocR A B C ⨟ (assocL A B C ⨟ (Term.fst (A ⊗ B) C ⨟ Term.fst A B))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (assocR A B C ⨟ Term.fst A (B ⊗ C)) := PEq.compR _ key

/-- Erasing a factor that carries no letter of the conclusion, on the right. -/
theorem IsShiftExchangeShape.sc_fst (V : Ty) : {D : Ty} → {g : Term D (shiftCod S T)} →
    IsShiftExchangeShape S T r g → SC S T r (Term.fst D V ⨟ (g ⨟ shiftContent S T))
  | _, _, .empty A => by
      refine SC.congr ?_ (SC.empty S T r (A ⊗ V))
      calc (Term.fst A V ⨟ ((toUnit A ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟
            shiftContent S T))
          ≡ₜ (Term.fst A V ⨟ (toUnit A ⨟ nilT (S ⊕' T))) :=
            PEq.compR _ (content_empty S T A)
        _ ≡ₜ ((Term.fst A V ⨟ toUnit A) ⨟ nilT (S ⊕' T)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (toUnit (A ⊗ V) ⨟ nilT (S ⊕' T)) := PEq.compL _ (PEq.unit_unique _ _)
  | _, _, @IsShiftExchangeShape.inner _ _ _ W X M Y V' x y m hx hrx hy hry hm => by
      set u : Term (W ⊗ X) ((S ⊕' T)⋆) := (Term.snd W X ⨟ x) ⨟ sLetter S T with hu
      set mc : Term M ((S ⊕' T)⋆) := m ⨟ pairContentTS S T with hmc
      have hjy : (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)) ≡ₜ
          (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)) := by
        calc (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T))
            ≡ₜ ((Term.fst (Y ⊗ V') V ⨟ (Term.fst Y V' ⨟ y)) ⨟ tLetter S T) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (((Term.fst (Y ⊗ V') V ⨟ Term.fst Y V') ⨟ y) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (((assocR Y V' V ⨟ Term.fst Y (V' ⊗ V)) ⨟ y) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.compL _ (fst_fst_assocR Y V' V))
          _ ≡ₜ ((assocR Y V' V ⨟ (Term.fst Y (V' ⊗ V) ⨟ y)) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)) :=
              PEq.comp_assoc _ _ _
      have hmid : (Term.fst (M ⊗ (Y ⊗ V')) V ⨟
            (mc ⊙ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T))) ≡ₜ
          ((assocR M (Y ⊗ V') V ⨟ prodF (Term.id M) (assocR Y V' V)) ⨟
            (mc ⊙ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T))) := by
        calc (Term.fst (M ⊗ (Y ⊗ V')) V ⨟ (mc ⊙ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)))
            ≡ₜ (assocR M (Y ⊗ V') V ⨟
                (mc ⊙ (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)))) :=
              fst_fdot _ _
          _ ≡ₜ (assocR M (Y ⊗ V') V ⨟
                (mc ⊙ (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)))) :=
              PEq.compR _ (fdot_congr (PEq.refl _) hjy)
          _ ≡ₜ (assocR M (Y ⊗ V') V ⨟ (prodF (Term.id M) (assocR Y V' V) ⨟
                (mc ⊙ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)))) :=
              PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
                (fdot_congr (PEq.id_comp _) (PEq.refl _))))
          _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
      refine SC.congr ?_ (SC.lift_comp
        (IsLift.comp (IsLift.assocR (W ⊗ X) (M ⊗ (Y ⊗ V')) V)
          (IsLift.prodF (IsLift.id (W ⊗ X))
            (IsLift.comp (IsLift.assocR M (Y ⊗ V') V)
              (IsLift.prodF (IsLift.id M) (IsLift.assocR Y V' V)))))
        (SC.inner_junk (W := W) (V := V' ⊗ V) hx hrx hy hry hm))
      calc (Term.fst ((W ⊗ X) ⊗ (M ⊗ (Y ⊗ V'))) V ⨟
            ((prodF (Term.snd W X ⨟ x) (prodF m (Term.fst Y V' ⨟ y)) ⨟
              Term.inr Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T))
          ≡ₜ (Term.fst ((W ⊗ X) ⊗ (M ⊗ (Y ⊗ V'))) V ⨟
              (u ⊙ (mc ⊙ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)))) :=
            PEq.compR _ (content_inner x m y)
        _ ≡ₜ (assocR (W ⊗ X) (M ⊗ (Y ⊗ V')) V ⨟
              (u ⊙ (Term.fst (M ⊗ (Y ⊗ V')) V ⨟
                (mc ⊙ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T))))) := fst_fdot _ _
        _ ≡ₜ (assocR (W ⊗ X) (M ⊗ (Y ⊗ V')) V ⨟
              (u ⊙ ((assocR M (Y ⊗ V') V ⨟ prodF (Term.id M) (assocR Y V' V)) ⨟
                (mc ⊙ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T))))) :=
            PEq.compR _ (fdot_congr (PEq.refl _) hmid)
        _ ≡ₜ (assocR (W ⊗ X) (M ⊗ (Y ⊗ V')) V ⨟
              (prodF (Term.id (W ⊗ X))
                  (assocR M (Y ⊗ V') V ⨟ prodF (Term.id M) (assocR Y V' V)) ⨟
                (u ⊙ (mc ⊙ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T))))) :=
            PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
              (fdot_congr (PEq.id_comp _) (PEq.refl _))))
        _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  | _, _, .either h₁ h₂ => by
      refine SC.congr ?_ (SC.lift_comp (IsLift.distL _ _ V)
        (SC.either (h₁.sc_fst V) (h₂.sc_fst V)))
      calc (Term.fst _ V ⨟ (Term.either _ _ ⨟ shiftContent S T))
          ≡ₜ (Term.fst _ V ⨟ Term.either (_ ⨟ shiftContent S T) (_ ⨟ shiftContent S T)) :=
            PEq.compR _ (Term.either_comp _ _ _)
        _ ≡ₜ _ := fst_either _ _

/-- Erasing, on the left, a factor that carries no letter of the conclusion. -/
theorem SC.snd_comp (W : Ty) {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SC S T r c) :
    SC S T r (Term.snd W A ⨟ c) := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := h
  refine SC.congr ?_ (SC.lift_comp (IsLift.prodF (IsLift.id W) ha) (hg.sc_snd W))
  calc (Term.snd W A ⨟ c)
      ≡ₜ (Term.snd W A ⨟ (alpha ⨟ (g ⨟ shiftContent S T))) := PEq.compR _ he
    _ ≡ₜ ((Term.snd W A ⨟ alpha) ⨟ (g ⨟ shiftContent S T)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (Term.id W) alpha ⨟ Term.snd W D) ⨟ (g ⨟ shiftContent S T)) :=
        PEq.compL _ (PEq.symm (PEq.nat_snd _ _))
    _ ≡ₜ (prodF (Term.id W) alpha ⨟ (Term.snd W D ⨟ (g ⨟ shiftContent S T))) :=
        PEq.comp_assoc _ _ _

/-- Erasing, on the right, a factor that carries no letter of the conclusion. -/
theorem SC.fst_comp (V : Ty) {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SC S T r c) :
    SC S T r (Term.fst A V ⨟ c) := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := h
  refine SC.congr ?_ (SC.lift_comp (IsLift.prodF ha (IsLift.id V)) (hg.sc_fst V))
  calc (Term.fst A V ⨟ c)
      ≡ₜ (Term.fst A V ⨟ (alpha ⨟ (g ⨟ shiftContent S T))) := PEq.compR _ he
    _ ≡ₜ ((Term.fst A V ⨟ alpha) ⨟ (g ⨟ shiftContent S T)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF alpha (Term.id V) ⨟ Term.fst D V) ⨟ (g ⨟ shiftContent S T)) :=
        PEq.compL _ (PEq.symm (PEq.nat_fst _ _))
    _ ≡ₜ (prodF alpha (Term.id V) ⨟ (Term.fst D V ⨟ (g ⨟ shiftContent S T))) :=
        PEq.comp_assoc _ _ _

/-! ### A single pair -/

/-- The content of a single pair of letters, produced by two separate drops. -/
theorem SC.pair {X Y : Ty} {x : Term X S} {y : Term Y T} (hx : IsDrop x) (hrx : rank x ≤ r)
    (hy : IsDrop y) (hry : rank y ≤ r) : SC S T r ((x ⨟ sLetter S T) ⊙ (y ⨟ tLetter S T)) := by
  have hbase := SC.inner_junk (S := S) (T := T) (r := r) (W := Ty.unit) (V := Ty.unit)
    (m := nilT (T ⊗ S)) hx hrx hy hry IsShiftInnerForm.nil
  refine SC.congr ?_ (SC.lift_comp
    (IsLift.prodF (IsLift.unitL X)
      (IsLift.comp (IsLift.unitR Y) (IsLift.unitL (Y ⊗ Ty.unit)))) hbase)
  have hleft : (Term.unitL X ⨟ ((Term.snd Ty.unit X ⨟ x) ⨟ sLetter S T)) ≡ₜ
      (x ⨟ sLetter S T) := by
    calc (Term.unitL X ⨟ ((Term.snd Ty.unit X ⨟ x) ⨟ sLetter S T))
        ≡ₜ (((Term.unitL X ⨟ Term.snd Ty.unit X) ⨟ x) ⨟ sLetter S T) :=
          PEq.symm ((PEq.compL _ (PEq.comp_assoc _ _ _)).trans (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id X ⨟ x) ⨟ sLetter S T) :=
          PEq.compL _ (PEq.compL _ (PEq.unitL_snd X))
      _ ≡ₜ (x ⨟ sLetter S T) := PEq.compL _ (PEq.id_comp _)
  have hright : ((Term.unitR Y ⨟ Term.unitL (Y ⊗ Ty.unit)) ⨟
        ((nilT (T ⊗ S) ⨟ pairContentTS S T) ⊙
          ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T))) ≡ₜ (y ⨟ tLetter S T) := by
    have hnil : ((nilT (T ⊗ S) ⨟ pairContentTS S T) ⊙
          ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) ≡ₜ
        (Term.snd Ty.unit (Y ⊗ Ty.unit) ⨟ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) := by
      calc ((nilT (T ⊗ S) ⨟ pairContentTS S T) ⊙
            ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T))
          ≡ₜ (nilT (S ⊕' T) ⊙ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) :=
            fdot_congr (homT_nil _) (PEq.refl _)
        _ ≡ₜ _ := fdot_nil_left _
    calc ((Term.unitR Y ⨟ Term.unitL (Y ⊗ Ty.unit)) ⨟
          ((nilT (T ⊗ S) ⨟ pairContentTS S T) ⊙
            ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)))
        ≡ₜ ((Term.unitR Y ⨟ Term.unitL (Y ⊗ Ty.unit)) ⨟
            (Term.snd Ty.unit (Y ⊗ Ty.unit) ⨟ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T))) :=
          PEq.compR _ hnil
      _ ≡ₜ (((Term.unitR Y ⨟ Term.unitL (Y ⊗ Ty.unit)) ⨟
            Term.snd Ty.unit (Y ⊗ Ty.unit)) ⨟ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((Term.unitR Y ⨟ (Term.unitL (Y ⊗ Ty.unit) ⨟
            Term.snd Ty.unit (Y ⊗ Ty.unit))) ⨟ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) :=
          PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((Term.unitR Y ⨟ Term.id (Y ⊗ Ty.unit)) ⨟
            ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) :=
          PEq.compL _ (PEq.compR _ (PEq.unitL_snd (Y ⊗ Ty.unit)))
      _ ≡ₜ (Term.unitR Y ⨟ ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)) :=
          PEq.compL _ (PEq.comp_id _)
      _ ≡ₜ (((Term.unitR Y ⨟ Term.fst Y Ty.unit) ⨟ y) ⨟ tLetter S T) :=
          PEq.symm ((PEq.compL _ (PEq.comp_assoc _ _ _)).trans (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id Y ⨟ y) ⨟ tLetter S T) := PEq.compL _ (PEq.compL _ (PEq.unitR_fst Y))
      _ ≡ₜ (y ⨟ tLetter S T) := PEq.compL _ (PEq.id_comp _)
  calc ((x ⨟ sLetter S T) ⊙ (y ⨟ tLetter S T))
      ≡ₜ ((Term.unitL X ⨟ ((Term.snd Ty.unit X ⨟ x) ⨟ sLetter S T)) ⊙
          ((Term.unitR Y ⨟ Term.unitL (Y ⊗ Ty.unit)) ⨟
            ((nilT (T ⊗ S) ⨟ pairContentTS S T) ⊙
              ((Term.fst Y Ty.unit ⨟ y) ⨟ tLetter S T)))) :=
        fdot_congr (PEq.symm hleft) (PEq.symm hright)
    _ ≡ₜ _ := PEq.symm (fdot_precomp _ _ _ _)

/-- The content of a normal form with a product codomain `S × T`, read as a pair of
letters. -/
theorem SC.of_normalProd : {A : Ty} → {g : Term A (S ⊗ T)} → IsNormalProdLe r g →
    SC S T r (g ⨟ (sLetter S T ⊙ tLetter S T))
  | _, _, .prodF hx hy hrx hry =>
      SC.congr (fdot_precomp _ _ _ _) (SC.pair hx hrx hy hry)
  | _, _, .either h₁ h₂ =>
      SC.congr (Term.either_comp _ _ _)
        (SC.either (SC.of_normalProd h₁) (SC.of_normalProd h₂))

/-! ### Equality of contents up to a lift

The rearrangements that the induction performs are all of the following shape: two contents
of different types compute the same word, and the two types are related by a lift.  The
relation is transitive and compatible with concatenation, which makes the rearrangements
short to write. -/

/-- Two contents are equal **up to a lift** if the first is provably equal to a lift followed
by the second. -/
def LiftEq {A A' D : Ty} (c : Term A D⋆) (c' : Term A' D⋆) : Prop :=
  ∃ rho : Term A A', IsLift rho ∧ c ≡ₜ (rho ⨟ c')

namespace LiftEq

variable {D : Ty}

theorem of_peq {A : Ty} {c c' : Term A D⋆} (h : c ≡ₜ c') : LiftEq c c' :=
  ⟨Term.id A, IsLift.id A, h.trans (PEq.symm (PEq.id_comp _))⟩

theorem refl {A : Ty} (c : Term A D⋆) : LiftEq c c := of_peq (PEq.refl c)

theorem trans {A₁ A₂ A₃ : Ty} {c₁ : Term A₁ D⋆} {c₂ : Term A₂ D⋆} {c₃ : Term A₃ D⋆}
    (h₁ : LiftEq c₁ c₂) (h₂ : LiftEq c₂ c₃) : LiftEq c₁ c₃ := by
  obtain ⟨rho₁, hr₁, he₁⟩ := h₁
  obtain ⟨rho₂, hr₂, he₂⟩ := h₂
  exact ⟨rho₁ ⨟ rho₂, IsLift.comp hr₁ hr₂,
    (he₁.trans (PEq.compR _ he₂)).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

/-- Replacing a content by a provably equal one. -/
theorem congr_left {A A' : Ty} {c c₀ : Term A D⋆} {c' : Term A' D⋆} (h : c ≡ₜ c₀)
    (h' : LiftEq c₀ c') : LiftEq c c' :=
  (of_peq h).trans h'

/-- Concatenation is compatible with equality up to a lift. -/
theorem fdot {A₁ A₂ A₁' A₂' : Ty} {c₁ : Term A₁ D⋆} {c₂ : Term A₂ D⋆} {c₁' : Term A₁' D⋆}
    {c₂' : Term A₂' D⋆} (h₁ : LiftEq c₁ c₁') (h₂ : LiftEq c₂ c₂') :
    LiftEq (c₁ ⊙ c₂) (c₁' ⊙ c₂') := by
  obtain ⟨rho₁, hr₁, he₁⟩ := h₁
  obtain ⟨rho₂, hr₂, he₂⟩ := h₂
  exact ⟨prodF rho₁ rho₂, IsLift.prodF hr₁ hr₂,
    (fdot_congr he₁ he₂).trans (PEq.symm (fdot_precomp _ _ _ _))⟩

/-- Re-associating a concatenation, to the right. -/
theorem assoc {A₁ A₂ A₃ : Ty} (c₁ : Term A₁ D⋆) (c₂ : Term A₂ D⋆) (c₃ : Term A₃ D⋆) :
    LiftEq ((c₁ ⊙ c₂) ⊙ c₃) (c₁ ⊙ (c₂ ⊙ c₃)) :=
  ⟨assocR A₁ A₂ A₃, IsLift.assocR _ _ _, fdot_assoc _ _ _⟩

/-- Re-associating a concatenation, to the left. -/
theorem assoc' {A₁ A₂ A₃ : Ty} (c₁ : Term A₁ D⋆) (c₂ : Term A₂ D⋆) (c₃ : Term A₃ D⋆) :
    LiftEq (c₁ ⊙ (c₂ ⊙ c₃)) ((c₁ ⊙ c₂) ⊙ c₃) :=
  ⟨assocL A₁ A₂ A₃, IsLift.assocL _ _ _, fdot_assoc' _ _ _⟩

end LiftEq

/-- Transporting `SC` along an equality of contents up to a lift. -/
theorem SC.of_liftEq {A A' : Ty} {c : Term A ((S ⊕' T)⋆)} {c' : Term A' ((S ⊕' T)⋆)}
    (h : LiftEq c c') (hc : SC S T r c') : SC S T r c :=
  let ⟨_, hr, he⟩ := h
  SC.congr he (SC.lift_comp hr hc)

/-! ### Merging the erased factors of two neighbouring letters -/

/-- The rebracketing that merges the factor erased after a letter of `T` with the factor
erased before a letter of `S`. -/
def mergeJunk (Y V W X : Ty) : Term ((Y ⊗ V) ⊗ (W ⊗ X)) ((Y ⊗ (V ⊗ W)) ⊗ X) :=
  (assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (assocL V W X)) ⨟ assocL Y (V ⊗ W) X

theorem isLift_mergeJunk (Y V W X : Ty) : IsLift (mergeJunk Y V W X) :=
  IsLift.comp (IsLift.comp (IsLift.assocR _ _ _)
    (IsLift.prodF (IsLift.id _) (IsLift.assocL _ _ _))) (IsLift.assocL _ _ _)

theorem mergeJunk_proj (Y V W X : Ty) :
    (mergeJunk Y V W X ⨟ prodF (Term.fst Y (V ⊗ W)) (Term.id X)) ≡ₜ
      prodF (Term.fst Y V) (Term.snd W X) := by
  have h1 : (assocL Y (V ⊗ W) X ⨟ prodF (Term.fst Y (V ⊗ W)) (Term.id X)) ≡ₜ
      prodF (Term.id Y) (Term.snd (V ⊗ W) X) := Term.assocL_fst_snd Y (V ⊗ W) X
  have h2 : (assocL V W X ⨟ Term.snd (V ⊗ W) X) ≡ₜ (Term.snd V (W ⊗ X) ⨟ Term.snd W X) :=
    PEq.symm (snd_snd_assocL V W X)
  have h3 : (assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (Term.snd V (W ⊗ X))) ≡ₜ
      prodF (Term.fst Y V) (Term.id (W ⊗ X)) := Term.assocR_snd_fst Y V (W ⊗ X)
  calc (mergeJunk Y V W X ⨟ prodF (Term.fst Y (V ⊗ W)) (Term.id X))
      ≡ₜ ((assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (assocL V W X)) ⨟
          (assocL Y (V ⊗ W) X ⨟ prodF (Term.fst Y (V ⊗ W)) (Term.id X))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (assocL V W X)) ⨟
          prodF (Term.id Y) (Term.snd (V ⊗ W) X)) := PEq.compR _ h1
    _ ≡ₜ (assocR Y V (W ⊗ X) ⨟ (prodF (Term.id Y) (assocL V W X) ⨟
          prodF (Term.id Y) (Term.snd (V ⊗ W) X))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y ⨟ Term.id Y)
          (assocL V W X ⨟ Term.snd (V ⊗ W) X)) := PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (Term.snd V (W ⊗ X) ⨟ Term.snd W X)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) h2)
    _ ≡ₜ (assocR Y V (W ⊗ X) ⨟ (prodF (Term.id Y) (Term.snd V (W ⊗ X)) ⨟
          prodF (Term.id Y) (Term.snd W X))) :=
        PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))))
    _ ≡ₜ ((assocR Y V (W ⊗ X) ⨟ prodF (Term.id Y) (Term.snd V (W ⊗ X))) ⨟
          prodF (Term.id Y) (Term.snd W X)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.fst Y V) (Term.id (W ⊗ X)) ⨟ prodF (Term.id Y) (Term.snd W X)) :=
        PEq.compL _ h3
    _ ≡ₜ prodF (Term.fst Y V ⨟ Term.id Y) (Term.id (W ⊗ X) ⨟ Term.snd W X) :=
        PEq.prod_comp _ _ _ _
    _ ≡ₜ prodF (Term.fst Y V) (Term.snd W X) :=
        PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _)

/-- The two neighbouring letters of two consecutive non-empty components: the erased factors
between them may be merged, which is what turns them into a single pair. -/
theorem liftEq_mergeJunk {Y V W X D : Ty} (a : Term Y D⋆) (b : Term X D⋆) :
    LiftEq ((Term.fst Y V ⨟ a) ⊙ (Term.snd W X ⨟ b))
      ((Term.fst Y (V ⊗ W) ⨟ a) ⊙ b) := by
  refine ⟨mergeJunk Y V W X, isLift_mergeJunk Y V W X, ?_⟩
  calc ((Term.fst Y V ⨟ a) ⊙ (Term.snd W X ⨟ b))
      ≡ₜ (prodF (Term.fst Y V) (Term.snd W X) ⨟ (a ⊙ b)) :=
        PEq.symm (fdot_precomp _ _ _ _)
    _ ≡ₜ ((mergeJunk Y V W X ⨟ prodF (Term.fst Y (V ⊗ W)) (Term.id X)) ⨟ (a ⊙ b)) :=
        PEq.compL _ (PEq.symm (mergeJunk_proj Y V W X))
    _ ≡ₜ (mergeJunk Y V W X ⨟ (prodF (Term.fst Y (V ⊗ W)) (Term.id X) ⨟ (a ⊙ b))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (mergeJunk Y V W X ⨟ ((Term.fst Y (V ⊗ W) ⨟ a) ⊙ (Term.id X ⨟ b))) :=
        PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (mergeJunk Y V W X ⨟ ((Term.fst Y (V ⊗ W) ⨟ a) ⊙ b)) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (PEq.id_comp _))

/-! ### Concatenating two contents

The product node of the induction: the concatenation of two contents of the shape of the
conclusion is again of that shape.  The two non-empty components that meet at the
concatenation point become the two halves of one new leaf `[(fst × id); (y × x)]` of the
inner normal form: the letter of `T` that ends the first component and the letter of `S`
that starts the second one. -/

/-- The content of a shape is of the shape, trivially. -/
theorem IsShiftExchangeShape.sc {D : Ty} {g : Term D (shiftCod S T)}
    (hg : IsShiftExchangeShape S T r g) : SC S T r (g ⨟ shiftContent S T) :=
  ⟨D, Term.id D, g, IsLift.id D, hg, PEq.symm (PEq.id_comp _)⟩

/-- The concatenation of an arbitrary content of the shape of the conclusion with a
*non-empty* one.  The induction is on the first content; the case in which it is non-empty
too is the one that creates a new leaf of the inner normal form. -/
theorem SC.fdot_inner {W₂ X₂ M₂ Y₂ V₂ : Ty} {x₂ : Term X₂ S} {y₂ : Term Y₂ T}
    {m₂ : Term M₂ ((T ⊗ S)⋆)} (hx₂ : IsDrop x₂) (hrx₂ : rank x₂ ≤ r) (hy₂ : IsDrop y₂)
    (hry₂ : rank y₂ ≤ r) (hm₂ : IsShiftInnerForm S T r m₂) :
    {D₁ : Ty} → {g₁ : Term D₁ (shiftCod S T)} → IsShiftExchangeShape S T r g₁ →
      SC S T r ((g₁ ⨟ shiftContent S T) ⊙
        (((Term.snd W₂ X₂ ⨟ x₂) ⨟ sLetter S T) ⊙
          ((m₂ ⨟ pairContentTS S T) ⊙ ((Term.fst Y₂ V₂ ⨟ y₂) ⨟ tLetter S T))))
  | _, _, .empty A => by
      refine SC.congr ?_ (SC.snd_comp A (SC.inner_junk hx₂ hrx₂ hy₂ hry₂ hm₂))
      calc (((Term.toUnit A ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T) ⊙
            _)
          ≡ₜ ((Term.toUnit A ⨟ nilT (S ⊕' T)) ⊙ _) :=
            fdot_congr (content_empty S T A) (PEq.refl _)
        _ ≡ₜ _ := prodF_nilconst_binconcat_left _
  | _, _, @IsShiftExchangeShape.inner _ _ _ W₁ X₁ M₁ Y₁ V₁ x₁ y₁ m₁ hx₁ hrx₁ hy₁ hry₁ hm₁ =>
      by
      set sx₁ : Term (W₁ ⊗ X₁) ((S ⊕' T)⋆) := (Term.snd W₁ X₁ ⨟ x₁) ⨟ sLetter S T with hsx₁
      set mc₁ : Term M₁ ((S ⊕' T)⋆) := m₁ ⨟ pairContentTS S T with hmc₁
      set ty₁ : Term (Y₁ ⊗ V₁) ((S ⊕' T)⋆) := (Term.fst Y₁ V₁ ⨟ y₁) ⨟ tLetter S T with hty₁
      set sx₂ : Term (W₂ ⊗ X₂) ((S ⊕' T)⋆) := (Term.snd W₂ X₂ ⨟ x₂) ⨟ sLetter S T with hsx₂
      set mc₂ : Term M₂ ((S ⊕' T)⋆) := m₂ ⨟ pairContentTS S T with hmc₂
      set ty₂ : Term (Y₂ ⊗ V₂) ((S ⊕' T)⋆) := (Term.fst Y₂ V₂ ⨟ y₂) ⨟ tLetter S T with hty₂
      -- the new leaf of the inner normal form
      set leaf : Term ((Y₁ ⊗ (V₁ ⊗ W₂)) ⊗ X₂) ((T ⊗ S)⋆) :=
        (prodF (Term.fst Y₁ (V₁ ⊗ W₂)) (Term.id X₂) ⨟ prodF y₁ x₂) ⨟ pureT (T ⊗ S) with hleaf
      have hrk : rank (prodF y₁ x₂) ≤ r := by
        have h : rank (prodF y₁ x₂) = max (rank y₁) (rank x₂) := rfl
        omega
      have hleafform : IsShiftInnerLeaf S T r leaf :=
        IsShiftInnerLeaf.sing (IsDrop.prodF hy₁ hx₂) hrk
      set L : Term ((Y₁ ⊗ (V₁ ⊗ W₂)) ⊗ X₂) ((S ⊕' T)⋆) :=
        ((Term.fst Y₁ (V₁ ⊗ W₂) ⨟ (y₁ ⨟ tLetter S T)) ⊙ (x₂ ⨟ sLetter S T)) with hL
      have hleafc : (leaf ⨟ pairContentTS S T) ≡ₜ L := by
        calc (((prodF (Term.fst Y₁ (V₁ ⊗ W₂)) (Term.id X₂) ⨟ prodF y₁ x₂) ⨟ pureT (T ⊗ S)) ⨟
              homT (tLetter S T ⊙ sLetter S T))
            ≡ₜ ((prodF (Term.fst Y₁ (V₁ ⊗ W₂)) (Term.id X₂) ⨟ prodF y₁ x₂) ⨟
                (pureT (T ⊗ S) ⨟ homT (tLetter S T ⊙ sLetter S T))) := PEq.comp_assoc _ _ _
          _ ≡ₜ ((prodF (Term.fst Y₁ (V₁ ⊗ W₂)) (Term.id X₂) ⨟ prodF y₁ x₂) ⨟
                (tLetter S T ⊙ sLetter S T)) := PEq.compR _ (homT_pure _)
          _ ≡ₜ (prodF (Term.fst Y₁ (V₁ ⊗ W₂) ⨟ y₁) (Term.id X₂ ⨟ x₂) ⨟
                (tLetter S T ⊙ sLetter S T)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ (((Term.fst Y₁ (V₁ ⊗ W₂) ⨟ y₁) ⨟ tLetter S T) ⊙
                ((Term.id X₂ ⨟ x₂) ⨟ sLetter S T)) := fdot_precomp _ _ _ _
          _ ≡ₜ ((Term.fst Y₁ (V₁ ⊗ W₂) ⨟ (y₁ ⨟ tLetter S T)) ⊙ (x₂ ⨟ sLetter S T)) :=
              fdot_congr (PEq.comp_assoc _ _ _) (PEq.compL _ (PEq.id_comp _))
      have hm : IsShiftInnerForm S T r (m₁ ⊙ (leaf ⊙ m₂)) :=
        hm₁.fdot ((IsShiftInnerForm.leaf hleafform).fdot hm₂)
      have hmc : ((m₁ ⊙ (leaf ⊙ m₂)) ⨟ pairContentTS S T) ≡ₜ (mc₁ ⊙ (L ⊙ mc₂)) := by
        calc ((m₁ ⊙ (leaf ⊙ m₂)) ⨟ homT (tLetter S T ⊙ sLetter S T))
            ≡ₜ ((m₁ ⨟ homT (tLetter S T ⊙ sLetter S T)) ⊙
                ((leaf ⊙ m₂) ⨟ homT (tLetter S T ⊙ sLetter S T))) := fdot_comp_homT _ _ _
          _ ≡ₜ (mc₁ ⊙ ((leaf ⨟ pairContentTS S T) ⊙ mc₂)) :=
              fdot_congr (PEq.refl _) (fdot_comp_homT _ _ _)
          _ ≡ₜ (mc₁ ⊙ (L ⊙ mc₂)) := fdot_congr (PEq.refl _) (fdot_congr hleafc (PEq.refl _))
      -- the target content, with the two components merged into one
      have htarget : SC S T r (sx₁ ⊙ ((mc₁ ⊙ (L ⊙ mc₂)) ⊙ ty₂)) :=
        SC.congr (fdot_congr (PEq.refl _) (fdot_congr (PEq.symm hmc) (PEq.refl _)))
          (SC.inner_junk hx₁ hrx₁ hy₂ hry₂ hm)
      -- the rearrangement
      have hmerge : LiftEq (ty₁ ⊙ sx₂) L :=
        LiftEq.congr_left
          (fdot_congr (PEq.comp_assoc _ _ _) (PEq.comp_assoc _ _ _))
          (liftEq_mergeJunk (y₁ ⨟ tLetter S T) (x₂ ⨟ sLetter S T))
      have hX : LiftEq (ty₁ ⊙ (sx₂ ⊙ (mc₂ ⊙ ty₂))) ((L ⊙ mc₂) ⊙ ty₂) :=
        (LiftEq.assoc' ty₁ sx₂ (mc₂ ⊙ ty₂)).trans
          ((LiftEq.fdot hmerge (LiftEq.refl (mc₂ ⊙ ty₂))).trans
            (LiftEq.assoc' L mc₂ ty₂))
      have hinner : LiftEq ((mc₁ ⊙ ty₁) ⊙ (sx₂ ⊙ (mc₂ ⊙ ty₂)))
          ((mc₁ ⊙ (L ⊙ mc₂)) ⊙ ty₂) :=
        (LiftEq.assoc mc₁ ty₁ (sx₂ ⊙ (mc₂ ⊙ ty₂))).trans
          ((LiftEq.fdot (LiftEq.refl mc₁) hX).trans (LiftEq.assoc' mc₁ (L ⊙ mc₂) ty₂))
      have hall : LiftEq ((sx₁ ⊙ (mc₁ ⊙ ty₁)) ⊙ (sx₂ ⊙ (mc₂ ⊙ ty₂)))
          (sx₁ ⊙ ((mc₁ ⊙ (L ⊙ mc₂)) ⊙ ty₂)) :=
        (LiftEq.assoc sx₁ (mc₁ ⊙ ty₁) (sx₂ ⊙ (mc₂ ⊙ ty₂))).trans
          (LiftEq.fdot (LiftEq.refl sx₁) hinner)
      exact SC.congr (fdot_congr (content_inner x₁ m₁ y₁) (PEq.refl _))
        (SC.of_liftEq hall htarget)
  | _, _, .either h₁ h₂ => by
      refine SC.congr ?_ (SC.lift_comp (IsLift.distL _ _ _)
        (SC.either (SC.fdot_inner hx₂ hrx₂ hy₂ hry₂ hm₂ h₁)
          (SC.fdot_inner hx₂ hrx₂ hy₂ hry₂ hm₂ h₂)))
      calc ((Term.either _ _ ⨟ shiftContent S T) ⊙ _)
          ≡ₜ (Term.either (_ ⨟ shiftContent S T) (_ ⨟ shiftContent S T) ⊙ _) :=
            fdot_congr (Term.either_comp _ _ _) (PEq.refl _)
        _ ≡ₜ _ := fdot_either_distL _ _ _

/-- The concatenation of two contents of the shape of the conclusion.  The induction is on
the second one. -/
theorem SC.fdot_shape : {D₂ : Ty} → {g₂ : Term D₂ (shiftCod S T)} →
    IsShiftExchangeShape S T r g₂ → {D₁ : Ty} → {g₁ : Term D₁ (shiftCod S T)} →
    IsShiftExchangeShape S T r g₁ →
    SC S T r ((g₁ ⨟ shiftContent S T) ⊙ (g₂ ⨟ shiftContent S T))
  | _, _, .empty A, _, _, hg₁ => by
      refine SC.congr ?_ (SC.fst_comp A hg₁.sc)
      calc ((_ ⨟ shiftContent S T) ⊙
            ((Term.toUnit A ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟ shiftContent S T))
          ≡ₜ ((_ ⨟ shiftContent S T) ⊙ (Term.toUnit A ⨟ nilT (S ⊕' T))) :=
            fdot_congr (PEq.refl _) (content_empty S T A)
        _ ≡ₜ _ := prodF_nilconst_binconcat _
  | _, _, .inner hx hrx hy hry hm, _, _, hg₁ =>
      SC.congr (fdot_congr (PEq.refl _) (content_inner _ _ _))
        (SC.fdot_inner hx hrx hy hry hm hg₁)
  | _, _, .either h₁ h₂, _, _, hg₁ => by
      refine SC.congr ?_ (SC.lift_comp (IsLift.distR _ _ _)
        (SC.either (SC.fdot_shape h₁ hg₁) (SC.fdot_shape h₂ hg₁)))
      calc ((_ ⨟ shiftContent S T) ⊙ (Term.either _ _ ⨟ shiftContent S T))
          ≡ₜ ((_ ⨟ shiftContent S T) ⊙
              Term.either (_ ⨟ shiftContent S T) (_ ⨟ shiftContent S T)) :=
            fdot_congr (PEq.refl _) (Term.either_comp _ _ _)
        _ ≡ₜ _ := fdot_either_distR _ _ _

/-- **The product node**: the concatenation of two contents of the shape of the conclusion is
of that shape. -/
theorem SC.fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SC S T r c₁) (h₂ : SC S T r c₂) : SC S T r (c₁ ⊙ c₂) := by
  obtain ⟨D₁, a₁, g₁, ha₁, hg₁, he₁⟩ := h₁
  obtain ⟨D₂, a₂, g₂, ha₂, hg₂, he₂⟩ := h₂
  refine SC.congr ?_ (SC.lift_comp (IsLift.prodF ha₁ ha₂) (SC.fdot_shape hg₂ hg₁))
  calc (c₁ ⊙ c₂)
      ≡ₜ ((a₁ ⨟ (g₁ ⨟ shiftContent S T)) ⊙ (a₂ ⨟ (g₂ ⨟ shiftContent S T))) :=
        fdot_congr he₁ he₂
    _ ≡ₜ _ := PEq.symm (fdot_precomp _ _ _ _)

/-! ### The bridge with the statement about `shift` -/

/-- From a statement about contents to the statement about `shift`: the codomain of `shift`
is an injective type, so the content determines the term. -/
theorem ShiftExch_of_SC {A : Ty} {f : Term A ((S ⊗ T)⋆)}
    (h : SC S T r (f ⨟ pairContent S T)) : ShiftExch S T r f := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := h
  refine ⟨D, alpha, g, ha, hg, ?_⟩
  refine ((cancel (f ⨟ Term.shift S T) (alpha ⨟ g)).1 _ (shiftContent S T)
    (Term.shiftCod_injective S T)).2 ?_
  calc ((f ⨟ Term.shift S T) ⨟ shiftContent S T)
      ≡ₜ (f ⨟ (Term.shift S T ⨟ shiftContent S T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ pairContent S T) := PEq.compR _ (Term.shift_rebracketing S T)
    _ ≡ₜ (alpha ⨟ (g ⨟ shiftContent S T)) := he
    _ ≡ₜ ((alpha ⨟ g) ⨟ shiftContent S T) := PEq.symm (PEq.comp_assoc _ _ _)

/-- From the statement about `shift` to the statement about contents. -/
theorem SC_of_ShiftExch {A : Ty} {f : Term A ((S ⊗ T)⋆)} (h : ShiftExch S T r f) :
    SC S T r (f ⨟ pairContent S T) := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := h
  refine ⟨D, alpha, g, ha, hg, ?_⟩
  calc (f ⨟ pairContent S T)
      ≡ₜ (f ⨟ (Term.shift S T ⨟ shiftContent S T)) :=
        PEq.compR _ (PEq.symm (Term.shift_rebracketing S T))
    _ ≡ₜ ((f ⨟ Term.shift S T) ⨟ shiftContent S T) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((alpha ⨟ g) ⨟ shiftContent S T) := PEq.compL _ he
    _ ≡ₜ (alpha ⨟ (g ⨟ shiftContent S T)) := PEq.comp_assoc _ _ _

end Lax149335Proofs

bridge_export Lax149335Proofs
