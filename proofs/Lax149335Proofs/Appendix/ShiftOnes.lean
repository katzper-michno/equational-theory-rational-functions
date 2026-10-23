import Lax149335Proofs.Preliminaries.HomCombinator
import Mathlib.Tactic.Set

/-!
# Shifting brackets and concatenation maps

Axiom 15 says that `shiftR` does not change the content of a list, i.e. that it commutes with
the two-parameter concatenation maps.  This file draws the consequences that are needed in the
appendix:

* the two-parameter concatenation maps composed with a homomorphism (`cmR_comp_homT`,
  `cmL_comp_homT`);
* the lemma "shift ones" of the appendix section on concatenation maps: bracketing a list
  `A*` as `1 × (A × 1)*` and as `(1 × A)* × 1` agree through `shiftL`;
* the corresponding statement for lists of pairs of strings, which is what the proof of
  Lemma 6.2 uses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Small facts -/

/-- The homomorphism extending `pure` is the identity (Axiom 12). -/
theorem homT_pureT (A : Ty) : homT (pureT A) ≡ₜ Term.id A⋆ := PEq.listF_pure_concat A

/-- The concatenation of the two identities is binary concatenation. -/
theorem fdot_id_id (B : Ty) : ((Term.id B⋆) ⊙ (Term.id B⋆)) ≡ₜ binconcat B :=
  (PEq.compL _ (PEq.prod_id B⋆ B⋆)).trans (PEq.id_comp _)

/-- Composing a left pairing with a product of two terms. -/
theorem pairL_prodF {A B C B' C' : Ty} (v : Value C) (f : Term A B)
    (g : Term C C') (h : Term B B') :
    (pairL v f ⨟ prodF g h) ≡ₜ pairL (v ⨟ g) (f ⨟ h) := by
  calc ((unitL A ⨟ prodF v f) ⨟ prodF g h) ≡ₜ (unitL A ⨟ (prodF v f ⨟ prodF g h)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL A ⨟ prodF (v ⨟ g) (f ⨟ h)) := PEq.compR _ (PEq.prod_comp _ _ _ _)

/-! ### The two concatenation maps of Axiom 15 -/

/-- The concatenation map of `X ⊗ (Y ⊗ X)*`. -/
abbrev cmR (X Y : Ty) : Term (X ⊗ (Y ⊗ X)⋆) (X ⊕' Y)⋆ :=
  TyF2.concatMap (.prod .p1 (.list (.prod .p2 .p1))) X Y

/-- The concatenation map of `(X ⊗ Y)* ⊗ X`. -/
abbrev cmL (X Y : Ty) : Term ((X ⊗ Y)⋆ ⊗ X) (X ⊕' Y)⋆ :=
  TyF2.concatMap (.prod (.list (.prod .p1 .p2)) .p1) X Y

/-- Axiom 15, read through the inverse of `shiftR`. -/
theorem shiftL_cm (X Y : Ty) : (shiftL X Y ⨟ cmL X Y) ≡ₜ cmR X Y := by
  calc (shiftL X Y ⨟ cmL X Y)
      ≡ₜ (shiftL X Y ⨟ (shiftR X Y ⨟ cmR X Y)) :=
        PEq.compR _ (PEq.symm (PEq.shiftR_content X Y))
    _ ≡ₜ ((shiftL X Y ⨟ shiftR X Y) ⨟ cmR X Y) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (X ⊗ (Y ⊗ X)⋆) ⨟ cmR X Y) := PEq.compL _ (PEq.shiftL_shiftR X Y)
    _ ≡ₜ cmR X Y := PEq.id_comp _

/-- Composing the first concatenation map with a homomorphism. -/
theorem cmR_comp_homT {X Y D : Ty} (d : Term (X ⊕' Y) D⋆) :
    (cmR X Y ⨟ homT d) ≡ₜ
      ((inl X Y ⨟ d) ⊙ homT ((inr X Y ⨟ d) ⊙ (inl X Y ⨟ d))) := by
  have hm1 : ((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ≡ₜ (inl X Y ⨟ d) :=
    (PEq.comp_assoc _ _ _).trans (PEq.compR _ (homT_pure d))
  have hm2 : ((inr X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ≡ₜ (inr X Y ⨟ d) :=
    (PEq.comp_assoc _ _ _).trans (PEq.compR _ (homT_pure d))
  calc (((inl X Y ⨟ pureT (X ⊕' Y)) ⊙
          homT ((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))) ⨟ homT d)
      ≡ₜ (((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ⊙
          (homT ((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y))) ⨟ homT d)) :=
        fdot_comp_homT _ _ d
    _ ≡ₜ ((inl X Y ⨟ d) ⊙
          homT (((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y))) ⨟ homT d)) :=
        fdot_congr hm1 (homT_comp _ _)
    _ ≡ₜ ((inl X Y ⨟ d) ⊙
          homT (((inr X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ⊙
            ((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d))) :=
        fdot_congr (PEq.refl _) (homT_congr (fdot_comp_homT _ _ d))
    _ ≡ₜ ((inl X Y ⨟ d) ⊙ homT ((inr X Y ⨟ d) ⊙ (inl X Y ⨟ d))) :=
        fdot_congr (PEq.refl _) (homT_congr (fdot_congr hm2 hm1))

/-- Composing the second concatenation map with a homomorphism. -/
theorem cmL_comp_homT {X Y D : Ty} (d : Term (X ⊕' Y) D⋆) :
    (cmL X Y ⨟ homT d) ≡ₜ
      (homT ((inl X Y ⨟ d) ⊙ (inr X Y ⨟ d)) ⊙ (inl X Y ⨟ d)) := by
  have hm1 : ((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ≡ₜ (inl X Y ⨟ d) :=
    (PEq.comp_assoc _ _ _).trans (PEq.compR _ (homT_pure d))
  have hm2 : ((inr X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ≡ₜ (inr X Y ⨟ d) :=
    (PEq.comp_assoc _ _ _).trans (PEq.compR _ (homT_pure d))
  calc ((homT ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y))) ⊙
          (inl X Y ⨟ pureT (X ⊕' Y))) ⨟ homT d)
      ≡ₜ ((homT ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y))) ⨟ homT d) ⊙
          ((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d)) := fdot_comp_homT _ _ d
    _ ≡ₜ (homT (((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y))) ⨟ homT d) ⊙
          (inl X Y ⨟ d)) := fdot_congr (homT_comp _ _) hm1
    _ ≡ₜ (homT (((inl X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d) ⊙
            ((inr X Y ⨟ pureT (X ⊕' Y)) ⨟ homT d)) ⊙ (inl X Y ⨟ d)) :=
        fdot_congr (homT_congr (fdot_comp_homT _ _ d)) (PEq.refl _)
    _ ≡ₜ (homT ((inl X Y ⨟ d) ⊙ (inr X Y ⨟ d)) ⊙ (inl X Y ⨟ d)) :=
        fdot_congr (homT_congr (fdot_congr hm1 hm2)) (PEq.refl _)

/-! ### The lemma "shift ones" -/

/-- Erasing the unit components of a list over `1 + A`. -/
def dropUnit (A : Ty) : Term (Ty.unit ⊕' A) A⋆ := either (nilT A) (pureT A)

/-- The first concatenation map, with the unit components erased. -/
theorem cmR_dropUnit (A : Ty) :
    (cmR Ty.unit A ⨟ homT (dropUnit A)) ≡ₜ
      (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)) := by
  have hl : (inl Ty.unit A ⨟ dropUnit A) ≡ₜ nilT A := inl_either _ _
  have hr : (inr Ty.unit A ⨟ dropUnit A) ≡ₜ pureT A := inr_either _ _
  have hinner : homT ((inr Ty.unit A ⨟ dropUnit A) ⊙ (inl Ty.unit A ⨟ dropUnit A)) ≡ₜ
      listF (fst A Ty.unit) := by
    calc homT ((inr Ty.unit A ⨟ dropUnit A) ⊙ (inl Ty.unit A ⨟ dropUnit A))
        ≡ₜ homT (pureT A ⊙ nilT A) := homT_congr (fdot_congr hr hl)
      _ ≡ₜ homT (fst A Ty.unit ⨟ pureT A) := homT_congr (fdot_nil_right (pureT A))
      _ ≡ₜ (listF (fst A Ty.unit) ⨟ homT (pureT A)) := homT_precomp _ _
      _ ≡ₜ (listF (fst A Ty.unit) ⨟ Term.id A⋆) := PEq.compR _ (homT_pureT A)
      _ ≡ₜ listF (fst A Ty.unit) := PEq.comp_id _
  calc (cmR Ty.unit A ⨟ homT (dropUnit A))
      ≡ₜ ((inl Ty.unit A ⨟ dropUnit A) ⊙
          homT ((inr Ty.unit A ⨟ dropUnit A) ⊙ (inl Ty.unit A ⨟ dropUnit A))) :=
        cmR_comp_homT _
    _ ≡ₜ (nilT A ⊙ listF (fst A Ty.unit)) := fdot_congr hl hinner
    _ ≡ₜ (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)) := fdot_nil_left _

/-- The second concatenation map, with the unit components erased. -/
theorem cmL_dropUnit (A : Ty) :
    (cmL Ty.unit A ⨟ homT (dropUnit A)) ≡ₜ
      (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)) := by
  have hl : (inl Ty.unit A ⨟ dropUnit A) ≡ₜ nilT A := inl_either _ _
  have hr : (inr Ty.unit A ⨟ dropUnit A) ≡ₜ pureT A := inr_either _ _
  have hinner : homT ((inl Ty.unit A ⨟ dropUnit A) ⊙ (inr Ty.unit A ⨟ dropUnit A)) ≡ₜ
      listF (snd Ty.unit A) := by
    calc homT ((inl Ty.unit A ⨟ dropUnit A) ⊙ (inr Ty.unit A ⨟ dropUnit A))
        ≡ₜ homT (nilT A ⊙ pureT A) := homT_congr (fdot_congr hl hr)
      _ ≡ₜ homT (snd Ty.unit A ⨟ pureT A) := homT_congr (fdot_nil_left (pureT A))
      _ ≡ₜ (listF (snd Ty.unit A) ⨟ homT (pureT A)) := homT_precomp _ _
      _ ≡ₜ (listF (snd Ty.unit A) ⨟ Term.id A⋆) := PEq.compR _ (homT_pureT A)
      _ ≡ₜ listF (snd Ty.unit A) := PEq.comp_id _
  calc (cmL Ty.unit A ⨟ homT (dropUnit A))
      ≡ₜ (homT ((inl Ty.unit A ⨟ dropUnit A) ⊙ (inr Ty.unit A ⨟ dropUnit A)) ⊙
          (inl Ty.unit A ⨟ dropUnit A)) := cmL_comp_homT _
    _ ≡ₜ (listF (snd Ty.unit A) ⊙ nilT A) := fdot_congr hinner hl
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)) := fdot_nil_right _

/-- Bracketing a list as `1 × (A × 1)*`. -/
def packR (A : Ty) : Term A⋆ (Ty.unit ⊗ (A ⊗ Ty.unit)⋆) :=
  listF (unitR A) ⨟ unitL ((A ⊗ Ty.unit)⋆)

/-- Bracketing a list as `(1 × A)* × 1`. -/
def packL (A : Ty) : Term A⋆ ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit) :=
  listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)

/-- The concatenation map of `(1 × A)* × 1` has `packL` as a one-sided inverse, and is
therefore provably injective. -/
theorem packL_injective (A : Ty) :
    ProvablyInjective (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)) := by
  refine ⟨packL A, ?_⟩
  calc ((fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)) ⨟
          (listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)))
      ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ (listF (snd Ty.unit A) ⨟
          (listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ ((listF (snd Ty.unit A) ⨟ listF (unitL A)) ⨟
          unitR ((Ty.unit ⊗ A)⋆))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ (listF (snd Ty.unit A ⨟ unitL A) ⨟
          unitR ((Ty.unit ⊗ A)⋆))) := PEq.compR _ (PEq.compL _ (PEq.list_comp _ _))
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ (listF (Term.id (Ty.unit ⊗ A)) ⨟
          unitR ((Ty.unit ⊗ A)⋆))) :=
        PEq.compR _ (PEq.compL _ (PEq.congr_listF (PEq.snd_unitL A)))
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ (Term.id ((Ty.unit ⊗ A)⋆) ⨟
          unitR ((Ty.unit ⊗ A)⋆))) := PEq.compR _ (PEq.compL _ (PEq.list_id _))
    _ ≡ₜ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ unitR ((Ty.unit ⊗ A)⋆)) :=
        PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit) := PEq.fst_unitR _

/-- **"Shift ones"** (appendix, concatenation maps): the two ways of decorating a list with
units agree through `shiftL`. -/
theorem shift_ones (A : Ty) : (packR A ⨟ shiftL Ty.unit A) ≡ₜ packL A := by
  refine ((cancel _ _).1 _ _ (packL_injective A)).2 ?_
  have hL : ((packR A ⨟ shiftL Ty.unit A) ⨟
      (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A))) ≡ₜ Term.id A⋆ := by
    have hstep : (shiftL Ty.unit A ⨟
        (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A))) ≡ₜ
        (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)) := by
      calc (shiftL Ty.unit A ⨟ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))
          ≡ₜ (shiftL Ty.unit A ⨟ (cmL Ty.unit A ⨟ homT (dropUnit A))) :=
            PEq.compR _ (PEq.symm (cmL_dropUnit A))
        _ ≡ₜ ((shiftL Ty.unit A ⨟ cmL Ty.unit A) ⨟ homT (dropUnit A)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (cmR Ty.unit A ⨟ homT (dropUnit A)) := PEq.compL _ (shiftL_cm Ty.unit A)
        _ ≡ₜ (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)) := cmR_dropUnit A
    calc ((packR A ⨟ shiftL Ty.unit A) ⨟
            (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))
        ≡ₜ (packR A ⨟ (shiftL Ty.unit A ⨟
            (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (packR A ⨟ (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit))) :=
          PEq.compR _ hstep
      _ ≡ₜ ((listF (unitR A) ⨟ unitL ((A ⊗ Ty.unit)⋆)) ⨟
            (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit))) := PEq.refl _
      _ ≡ₜ (listF (unitR A) ⨟ ((unitL ((A ⊗ Ty.unit)⋆) ⨟ snd Ty.unit ((A ⊗ Ty.unit)⋆)) ⨟
            listF (fst A Ty.unit))) := by
            calc ((listF (unitR A) ⨟ unitL ((A ⊗ Ty.unit)⋆)) ⨟
                    (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)))
                ≡ₜ (listF (unitR A) ⨟ (unitL ((A ⊗ Ty.unit)⋆) ⨟
                      (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit)))) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (listF (unitR A) ⨟ (Term.id ((A ⊗ Ty.unit)⋆) ⨟ listF (fst A Ty.unit))) :=
          PEq.compR _ (PEq.compL _ (PEq.unitL_snd _))
      _ ≡ₜ (listF (unitR A) ⨟ listF (fst A Ty.unit)) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ listF (unitR A ⨟ fst A Ty.unit) := PEq.list_comp _ _
      _ ≡ₜ listF (Term.id A) := PEq.congr_listF (PEq.unitR_fst A)
      _ ≡ₜ Term.id A⋆ := PEq.list_id A
  have hR : (packL A ⨟ (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A))) ≡ₜ
      Term.id A⋆ := by
    calc ((listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)) ⨟
            (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))
        ≡ₜ (listF (unitL A) ⨟ ((unitR ((Ty.unit ⊗ A)⋆) ⨟ fst ((Ty.unit ⊗ A)⋆) Ty.unit) ⨟
            listF (snd Ty.unit A))) := by
          calc ((listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)) ⨟
                  (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))
              ≡ₜ (listF (unitL A) ⨟ (unitR ((Ty.unit ⊗ A)⋆) ⨟
                    (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (listF (unitL A) ⨟ (Term.id ((Ty.unit ⊗ A)⋆) ⨟ listF (snd Ty.unit A))) :=
          PEq.compR _ (PEq.compL _ (PEq.unitR_fst _))
      _ ≡ₜ (listF (unitL A) ⨟ listF (snd Ty.unit A)) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ listF (unitL A ⨟ snd Ty.unit A) := PEq.list_comp _ _
      _ ≡ₜ listF (Term.id A) := PEq.congr_listF (PEq.unitL_snd A)
      _ ≡ₜ Term.id A⋆ := PEq.list_id A
  exact hL.trans (PEq.symm hR)

/-! ### The same statement for lists of pairs of strings -/

/-- The generalised concatenation map `B* ⊗ (B* ⊗ B*)* → B*`. -/
def gconcR (B : Ty) : Term (B⋆ ⊗ (B⋆ ⊗ B⋆)⋆) B⋆ := (Term.id B⋆) ⊙ homT (binconcat B)

/-- The generalised concatenation map `(B* ⊗ B*)* ⊗ B* → B*`. -/
def gconcL (B : Ty) : Term ((B⋆ ⊗ B⋆)⋆ ⊗ B⋆) B⋆ := homT (binconcat B) ⊙ (Term.id B⋆)

/-- `shiftL` commutes with the generalised concatenation maps. -/
theorem shiftL_gconc (B : Ty) : (shiftL B⋆ B⋆ ⨟ gconcL B) ≡ₜ gconcR B := by
  set d : Term (B⋆ ⊕' B⋆) B⋆ := either (Term.id B⋆) (Term.id B⋆) with hd
  have hl : (inl B⋆ B⋆ ⨟ d) ≡ₜ Term.id B⋆ := inl_either _ _
  have hr : (inr B⋆ B⋆ ⨟ d) ≡ₜ Term.id B⋆ := inr_either _ _
  have hR : (cmR B⋆ B⋆ ⨟ homT d) ≡ₜ gconcR B := by
    calc (cmR B⋆ B⋆ ⨟ homT d)
        ≡ₜ ((inl B⋆ B⋆ ⨟ d) ⊙ homT ((inr B⋆ B⋆ ⨟ d) ⊙ (inl B⋆ B⋆ ⨟ d))) := cmR_comp_homT d
      _ ≡ₜ ((Term.id B⋆) ⊙ homT ((Term.id B⋆) ⊙ (Term.id B⋆))) :=
          fdot_congr hl (homT_congr (fdot_congr hr hl))
      _ ≡ₜ ((Term.id B⋆) ⊙ homT (binconcat B)) :=
          fdot_congr (PEq.refl _) (homT_congr (fdot_id_id B))
  have hL : (cmL B⋆ B⋆ ⨟ homT d) ≡ₜ gconcL B := by
    calc (cmL B⋆ B⋆ ⨟ homT d)
        ≡ₜ (homT ((inl B⋆ B⋆ ⨟ d) ⊙ (inr B⋆ B⋆ ⨟ d)) ⊙ (inl B⋆ B⋆ ⨟ d)) := cmL_comp_homT d
      _ ≡ₜ (homT ((Term.id B⋆) ⊙ (Term.id B⋆)) ⊙ (Term.id B⋆)) :=
          fdot_congr (homT_congr (fdot_congr hl hr)) hl
      _ ≡ₜ (homT (binconcat B) ⊙ (Term.id B⋆)) :=
          fdot_congr (homT_congr (fdot_id_id B)) (PEq.refl _)
  calc (shiftL B⋆ B⋆ ⨟ gconcL B)
      ≡ₜ (shiftL B⋆ B⋆ ⨟ (cmL B⋆ B⋆ ⨟ homT d)) := PEq.compR _ (PEq.symm hL)
    _ ≡ₜ ((shiftL B⋆ B⋆ ⨟ cmL B⋆ B⋆) ⨟ homT d) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (cmR B⋆ B⋆ ⨟ homT d) := PEq.compL _ (shiftL_cm B⋆ B⋆)
    _ ≡ₜ gconcR B := hR

/-! ### The symmetric variant of splitting (appendix, concatenation maps) -/

/-- The symmetric variant of `split`: `(A+B)* → (A* × B)* × A*`. -/
def splitLT (A B : Ty) : Term ((A ⊕' B)⋆) ((A⋆ ⊗ B)⋆ ⊗ A⋆) := split A B ⨟ shiftL A⋆ B

/-- The concatenation map of `(A* × B)* × A*`. -/
def cmSplitL (A B : Ty) : Term ((A⋆ ⊗ B)⋆ ⊗ A⋆) ((A ⊕' B)⋆) :=
  homT (homT (inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) ⊙
    homT (inl A B ⨟ pureT (A ⊕' B))

/-- The inverse of the symmetric variant of splitting is the concatenation map. -/
theorem shiftR_unsplit (A B : Ty) :
    (shiftR A⋆ B ⨟ unsplit A B) ≡ₜ cmSplitL A B := by
  set d : Term (A⋆ ⊕' B) ((A ⊕' B)⋆) :=
    either (homT (inl A B ⨟ pureT (A ⊕' B))) (inr A B ⨟ pureT (A ⊕' B)) with hd
  have hl : (inl A⋆ B ⨟ d) ≡ₜ homT (inl A B ⨟ pureT (A ⊕' B)) := inl_either _ _
  have hr : (inr A⋆ B ⨟ d) ≡ₜ (inr A B ⨟ pureT (A ⊕' B)) := inr_either _ _
  have hR : (cmR A⋆ B ⨟ homT d) ≡ₜ unsplit A B := by
    calc (cmR A⋆ B ⨟ homT d)
        ≡ₜ ((inl A⋆ B ⨟ d) ⊙ homT ((inr A⋆ B ⨟ d) ⊙ (inl A⋆ B ⨟ d))) := cmR_comp_homT d
      _ ≡ₜ (homT (inl A B ⨟ pureT (A ⊕' B)) ⊙
            homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ homT (inl A B ⨟ pureT (A ⊕' B)))) :=
          fdot_congr hl (homT_congr (fdot_congr hr hl))
  have hL : (cmL A⋆ B ⨟ homT d) ≡ₜ cmSplitL A B := by
    calc (cmL A⋆ B ⨟ homT d)
        ≡ₜ (homT ((inl A⋆ B ⨟ d) ⊙ (inr A⋆ B ⨟ d)) ⊙ (inl A⋆ B ⨟ d)) := cmL_comp_homT d
      _ ≡ₜ (homT (homT (inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) ⊙
            homT (inl A B ⨟ pureT (A ⊕' B))) := fdot_congr (homT_congr (fdot_congr hl hr)) hl
  calc (shiftR A⋆ B ⨟ unsplit A B)
      ≡ₜ (shiftR A⋆ B ⨟ (cmR A⋆ B ⨟ homT d)) := PEq.compR _ (PEq.symm hR)
    _ ≡ₜ ((shiftR A⋆ B ⨟ cmR A⋆ B) ⨟ homT d) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (cmL A⋆ B ⨟ homT d) := PEq.compL _ (PEq.shiftR_content A⋆ B)
    _ ≡ₜ cmSplitL A B := hL

/-- **Appendix (concatenation maps).**  The symmetric variant of splitting is a provable
isomorphism, and its inverse is the concatenation map. -/
theorem splitLT_iso (A B : Ty) :
    (splitLT A B ⨟ cmSplitL A B) ≡ₜ Term.id ((A ⊕' B)⋆) ∧
      (cmSplitL A B ⨟ splitLT A B) ≡ₜ Term.id ((A⋆ ⊗ B)⋆ ⊗ A⋆) := by
  constructor
  · calc ((split A B ⨟ shiftL A⋆ B) ⨟ cmSplitL A B)
        ≡ₜ ((split A B ⨟ shiftL A⋆ B) ⨟ (shiftR A⋆ B ⨟ unsplit A B)) :=
          PEq.compR _ (PEq.symm (shiftR_unsplit A B))
      _ ≡ₜ (split A B ⨟ (shiftL A⋆ B ⨟ (shiftR A⋆ B ⨟ unsplit A B))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (split A B ⨟ ((shiftL A⋆ B ⨟ shiftR A⋆ B) ⨟ unsplit A B)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (split A B ⨟ (Term.id (A⋆ ⊗ (B ⊗ A⋆)⋆) ⨟ unsplit A B)) :=
          PEq.compR _ (PEq.compL _ (PEq.shiftL_shiftR A⋆ B))
      _ ≡ₜ (split A B ⨟ unsplit A B) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id ((A ⊕' B)⋆) := PEq.split_unsplit A B
  · calc (cmSplitL A B ⨟ (split A B ⨟ shiftL A⋆ B))
        ≡ₜ ((shiftR A⋆ B ⨟ unsplit A B) ⨟ (split A B ⨟ shiftL A⋆ B)) :=
          PEq.compL _ (PEq.symm (shiftR_unsplit A B))
      _ ≡ₜ (shiftR A⋆ B ⨟ (unsplit A B ⨟ (split A B ⨟ shiftL A⋆ B))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (shiftR A⋆ B ⨟ ((unsplit A B ⨟ split A B) ⨟ shiftL A⋆ B)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (shiftR A⋆ B ⨟ (Term.id (A⋆ ⊗ (B ⊗ A⋆)⋆) ⨟ shiftL A⋆ B)) :=
          PEq.compR _ (PEq.compL _ (PEq.unsplit_split A B))
      _ ≡ₜ (shiftR A⋆ B ⨟ shiftL A⋆ B) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id ((A⋆ ⊗ B)⋆ ⊗ A⋆) := PEq.shiftR_shiftL A⋆ B

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
