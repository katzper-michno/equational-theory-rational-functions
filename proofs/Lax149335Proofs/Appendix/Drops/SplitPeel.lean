/-
Copyright (c) 2025.  Formalisation of *The equational theory of rational
string-to-string functions*.
-/
import Lax149335Proofs.Appendix.Drops.SplitCollect
import Mathlib.Tactic.Set

/-!
# Peeling the last block off a list

This file provides the *peeling* lift/drop pair used in the proof of the exchange lemma for
the atom `split` (Lemma 7.5).  A list over `V` is read as a list over `1 × V`, whose last
element is then split off by `shift`; the resulting term `Lax149335Proofs.Term.peelLift` is a lift,
with drop inverse `Lax149335Proofs.Term.peelDrop`.  Consequently every drop with codomain `V*`
factors, after a lift, through the co-domain of `shift 1 V`
(`Lax149335Proofs.peel_last`), which distinguishes the empty list from a list with a last element.

The last result of the file, `Lax149335Proofs.Term.peelDrop_zWord`, computes the content of a
peeled list of blocks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

namespace Term

/-- Composing a singleton with a homomorphic image. -/
theorem pure_homT_comp {A P B : Ty} (u : Term A P) (k : Term P (B⋆)) :
    ((u ⨟ pureT P) ⨟ homT k) ≡ₜ (u ⨟ k) :=
  (PEq.comp_assoc _ _ _).trans (PEq.compR _ (homT_pure k))

/-- The lift that peels the last element off a list: a list over `V` is read as a list over
`1 × V`, whose last element is then split off by `shift`. -/
def peelLift (V : Ty) : Term (V⋆) (shiftCod Ty.unit V) :=
  listF (unitL V) ⨟ shift Ty.unit V

/-- The drop that puts back the last element peeled off by `Lax149335Proofs.Term.peelLift`. -/
def peelDrop (V : Ty) : Term (shiftCod Ty.unit V) (V⋆) :=
  unshift Ty.unit V ⨟ listF (snd Ty.unit V)

theorem peelLift_peelDrop (V : Ty) : (peelLift V ⨟ peelDrop V) ≡ₜ Term.id (V⋆) := by
  calc ((listF (unitL V) ⨟ shift Ty.unit V) ⨟ (unshift Ty.unit V ⨟ listF (snd Ty.unit V)))
      ≡ₜ (listF (unitL V) ⨟ (shift Ty.unit V ⨟ (unshift Ty.unit V ⨟
          listF (snd Ty.unit V)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF (unitL V) ⨟ ((shift Ty.unit V ⨟ unshift Ty.unit V) ⨟
          listF (snd Ty.unit V))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (listF (unitL V) ⨟ (Term.id ((Ty.unit ⊗ V)⋆) ⨟ listF (snd Ty.unit V))) :=
        PEq.compR _ (PEq.compL _ (shift_unshift Ty.unit V))
    _ ≡ₜ (listF (unitL V) ⨟ listF (snd Ty.unit V)) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ listF (unitL V ⨟ snd Ty.unit V) := PEq.list_comp _ _
    _ ≡ₜ listF (Term.id V) := PEq.congr_listF (PEq.unitL_snd V)
    _ ≡ₜ Term.id (V⋆) := PEq.list_id V

/-- The content of a non-empty list of blocks, read through the co-domain of
`Lax149335Proofs.Term.peelLift`: the first blocks, followed by the last block. -/
def peelContentR (S T : Ty) :
    Term (Ty.unit ⊗ (((ZTy S T) ⊗ Ty.unit)⋆ ⊗ (ZTy S T))) ((S ⊕' T)⋆) :=
  snd Ty.unit (((ZTy S T) ⊗ Ty.unit)⋆ ⊗ (ZTy S T)) ⨟
    ((listF (fst (ZTy S T) Ty.unit) ⨟ zWord S T) ⊙ zBlock S T)

/-- The content of the co-domain of `Lax149335Proofs.Term.peelLift`, for a list of blocks: either
the empty word, or the content of the first blocks followed by the content of the last
block. -/
def peelContent (S T : Ty) : Term (shiftCod Ty.unit (ZTy S T)) ((S ⊕' T)⋆) :=
  either (nilT (S ⊕' T)) (peelContentR S T)

/-- Reading a list of blocks through the co-domain of `Lax149335Proofs.Term.peelLift`. -/
theorem peelDrop_zWord (S T : Ty) :
    (peelDrop (ZTy S T) ⨟ zWord S T) ≡ₜ peelContent S T := by
  set Z := ZTy S T with hZ
  set k : Term (Ty.unit ⊕' Z) ((S ⊕' T)⋆) := either (nilT (S ⊕' T)) (zBlock S T) with hk
  have hinl : (inl Ty.unit Z ⨟ k) ≡ₜ nilT (S ⊕' T) := inl_either _ _
  have hinr : (inr Ty.unit Z ⨟ k) ≡ₜ zBlock S T := inr_either _ _
  have h1 : (listF (snd Ty.unit Z) ⨟ zWord S T) ≡ₜ (pairContent Ty.unit Z ⨟ homT k) := by
    calc (listF (snd Ty.unit Z) ⨟ zWord S T)
        ≡ₜ homT (snd Ty.unit Z ⨟ zBlock S T) := PEq.symm (homT_precomp _ _)
      _ ≡ₜ homT (nilT (S ⊕' T) ⊙ zBlock S T) := homT_congr (PEq.symm (fdot_nil_left _))
      _ ≡ₜ homT (((inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k) ⊙
            ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k)) :=
          homT_congr (fdot_congr (PEq.symm ((pure_homT_comp _ _).trans hinl))
            (PEq.symm ((pure_homT_comp _ _).trans hinr)))
      _ ≡ₜ homT (((inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
            (inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k) :=
          homT_congr (PEq.symm (fdot_comp_homT _ _ _))
      _ ≡ₜ (pairContent Ty.unit Z ⨟ homT k) := PEq.symm (homT_comp _ _)
  have h2 : (shiftContent Ty.unit Z ⨟ homT k) ≡ₜ peelContent S T := by
    have hmid : (homT ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
          (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k) ≡ₜ
        (listF (fst Z Ty.unit) ⨟ zWord S T) := by
      calc (homT ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
              (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k)
          ≡ₜ homT (((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
              (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k) := homT_comp _ _
        _ ≡ₜ homT (((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k) ⊙
              ((inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k)) :=
            homT_congr (fdot_comp_homT _ _ _)
        _ ≡ₜ homT (zBlock S T ⊙ nilT (S ⊕' T)) :=
            homT_congr (fdot_congr ((pure_homT_comp _ _).trans hinr)
              ((pure_homT_comp _ _).trans hinl))
        _ ≡ₜ homT (fst Z Ty.unit ⨟ zBlock S T) := homT_congr (fdot_nil_right _)
        _ ≡ₜ (listF (fst Z Ty.unit) ⨟ zWord S T) := homT_precomp _ _
    calc (shiftContent Ty.unit Z ⨟ homT k)
        ≡ₜ either (nilT (Ty.unit ⊕' Z) ⨟ homT k)
            (((inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
              (homT ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
                (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⊙
                (inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)))) ⨟ homT k) :=
          either_comp _ _ _
      _ ≡ₜ either (nilT (S ⊕' T))
            (((inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k) ⊙
              ((homT ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
                (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⊙
                (inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k)) :=
          either_congr (homT_nil _) (fdot_comp_homT _ _ _)
      _ ≡ₜ either (nilT (S ⊕' T))
            (nilT (S ⊕' T) ⊙
              ((homT ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⊙
                (inl Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z))) ⨟ homT k) ⊙
                ((inr Ty.unit Z ⨟ pureT (Ty.unit ⊕' Z)) ⨟ homT k))) :=
          either_congr (PEq.refl _)
            (fdot_congr ((pure_homT_comp _ _).trans hinl) (fdot_comp_homT _ _ _))
      _ ≡ₜ either (nilT (S ⊕' T))
            (nilT (S ⊕' T) ⊙ ((listF (fst Z Ty.unit) ⨟ zWord S T) ⊙ zBlock S T)) :=
          either_congr (PEq.refl _)
            (fdot_congr (PEq.refl _)
              (fdot_congr hmid ((pure_homT_comp _ _).trans hinr)))
      _ ≡ₜ peelContent S T := either_congr (PEq.refl _) (fdot_nil_left _)
  calc (peelDrop Z ⨟ zWord S T)
      ≡ₜ (unshift Ty.unit Z ⨟ (listF (snd Ty.unit Z) ⨟ zWord S T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unshift Ty.unit Z ⨟ (pairContent Ty.unit Z ⨟ homT k)) := PEq.compR _ h1
    _ ≡ₜ ((unshift Ty.unit Z ⨟ pairContent Ty.unit Z) ⨟ homT k) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (shiftContent Ty.unit Z ⨟ homT k) :=
        PEq.compL _ (Term.unshift_pairContent Ty.unit Z)
    _ ≡ₜ peelContent S T := h2

end Term

/-- **Peeling the last block off a list of blocks.**  Every drop with codomain `V*` is, after
a lift, a drop into the co-domain of `Lax149335Proofs.Term.peelLift`, which distinguishes the empty
list from a list with a last element. -/
theorem peel_last {V Y : Ty} {y : Term Y (V⋆)} (hy : IsDrop y) :
    ∃ (E : Ty) (mu : Term Y E) (h : Term E (shiftCod Ty.unit V)),
      IsLift mu ∧ IsDrop h ∧ y ≡ₜ (mu ⨟ (h ⨟ Term.peelDrop V)) := by
  obtain ⟨E, mu, h, hmu, hh, he⟩ :=
    AdmitsExchange.comp (AdmitsExchange.listF (admitsExchange_unitL V))
      (admitsExchange_shift Ty.unit V) hy
  refine ⟨E, mu, h, hmu, hh, ?_⟩
  calc y
      ≡ₜ (y ⨟ Term.id (V⋆)) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (y ⨟ (Term.peelLift V ⨟ Term.peelDrop V)) :=
        PEq.compR _ (PEq.symm (Term.peelLift_peelDrop V))
    _ ≡ₜ ((y ⨟ Term.peelLift V) ⨟ Term.peelDrop V) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((mu ⨟ h) ⨟ Term.peelDrop V) := PEq.compL _ he
    _ ≡ₜ (mu ⨟ (h ⨟ Term.peelDrop V)) := PEq.comp_assoc _ _ _

end Lax149335Proofs

bridge_export Lax149335Proofs
