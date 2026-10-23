import Lax149335Proofs.Appendix.Groups.Unprefixing
import Lax149335Proofs.Appendix.ConjugacyRule.Soundness
import Lax149335Proofs.Appendix.Bundles.Composition
import Lax149335Proofs.Appendix.Bundles.Injectivity

/-!
# The bundle lemma for bundles of size two (appendix, *Proof of Lemma 6.7*)

This file follows the appendix proof of the bundle lemma (Lemma 6.7) in the case `k = 2`,
which is the case the appendix treats.

The **injectivity half** is proved in full: the concatenation map `(A × A)* × A^{<2} ↣ A*`
is provably injective (`cmap_injective`, `bundle_two_injective`).  Its proof follows the
appendix: the commuting diagram relating the constant and the cyclic annotation through the
group prefix multiplication (`cyc_unpref`, `cmap_annot_pref`) and the provable injectivity of
the cyclic annotation (`cyc_injective`).

The **surjectivity half** is *not* proved here.  The argument that the original appendix gives
for it has a gap: it claims that the one-sided inverse produced by the injectivity half
preserves the content of the list, whereas that inverse inverts `pure : A → A*` by a head
term, which does not.  The revised appendix closes the gap by postulating the missing half as
Axiom 16, the window axiom, and the surjectivity half is derived from it in
`Lax149335Proofs.Appendix.Bundles.Window`.

The last section of this file feeds the injectivity half into the bundles-of-bundles
construction of `Lax149335Proofs.Appendix.Bundles.Injectivity`, which gives, unconditionally,
provable injectivity of the concatenation map for arbitrarily large bundle sizes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace BundleTwo

/-- The two-letter alphabet, which carries the cyclic group of order two. -/
abbrev G2 : Ty := Ty.finAlph 1

/-- The cyclic group of order two, carried by the two-letter alphabet. -/
def Z2 : Group ⟦G2⟧ where
  mul x y := match x, y with
    | .inl _, y => y
    | x, .inl _ => x
    | .inr _, .inr _ => .inl ()
  one := .inl ()
  inv x := x
  mul_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  one_mul := by intro x; cases x <;> rfl
  mul_one := by intro x; cases x <;> rfl
  inv_mul_cancel := by intro x; cases x <;> rfl

/-- The group identity `g⁰`. -/
def e2 : ⟦G2⟧ := Sum.inl ()

/-- The generator `g¹`. -/
def g2 : ⟦G2⟧ := Sum.inr ()

/-- The type `A × G` of letters annotated by the group. -/
abbrev PT (A : Ty) : Ty := A ⊗ G2

/-- Annotating a letter with the group element `g`. -/
def ann (A : Ty) (g : ⟦G2⟧) : Term A (PT A) := pairR (Term.id A) (constFin g)

/-- Annotating a letter with `g`, as a one-element list. -/
def annS (A : Ty) (g : ⟦G2⟧) : Term A ((PT A)⋆) := ann A g ⨟ pureT (PT A)

/-- The *constant annotation*: every letter of a list is annotated with the generator. -/
def constAnn (A : Ty) : Term A⋆ ((PT A)⋆) := listF (ann A g2)

/-- The shape of the bundles of size two: a list of pairs, followed by at most one letter. -/
def F2 : TyF := .prod (.list (.prod .param .param)) (.sum .unit .param)

/-- The concatenation map `(A × A)* × A^{<2} ↣ A*`. -/
def cmap (A : Ty) : Term (F2.app A) A⋆ := TyF.concatMap F2 A

/-- The *cyclic annotation* followed by the concatenation map: a pair `(a,b)` is sent to the
two-element list `[(a,g¹),(b,g⁰)]`, and the tail letter to `[(a,g¹)]`. -/
def cyc (A : Ty) : Term (F2.app A) ((PT A)⋆) :=
  homT (annS A g2 ⊙ annS A e2) ⊙ either (nilT (PT A)) (annS A g2)

/-! ### The two copies of `A` inside `A × G` -/

/-- The identification of `A + A` with `A × G`. -/
def iotaS (A : Ty) : Term (A ⊕' A) (PT A) := either (ann A g2) (ann A e2)

/-- Its inverse. -/
def iotaSinv (A : Ty) : Term (PT A) (A ⊕' A) :=
  caseR (fun g => match g with | .inl _ => inr A A | .inr _ => inl A A)

theorem iotaS_iso (A : Ty) : ProvableIso (iotaS A) := by
  refine ⟨iotaSinv A, ?_, ?_⟩
  · calc (iotaS A ⨟ iotaSinv A)
        ≡ₜ either (ann A g2 ⨟ iotaSinv A) (ann A e2 ⨟ iotaSinv A) := either_comp _ _ _
      _ ≡ₜ either (Term.id A ⨟ inl A A) (Term.id A ⨟ inr A A) :=
          either_congr (pairR_caseR _ _ g2) (pairR_caseR _ _ e2)
      _ ≡ₜ either (inl A A) (inr A A) := either_congr (PEq.id_comp _) (PEq.id_comp _)
      _ ≡ₜ Term.id (A ⊕' A) := either_inl_inr A A
  · refine caseR_ext _ _ (fun g => ?_)
    have hstep : (pairR (Term.id A) (constFin g) ⨟ (iotaSinv A ⨟ iotaS A)) ≡ₜ
        ((pairR (Term.id A) (constFin g) ⨟ iotaSinv A) ⨟ iotaS A) :=
      PEq.symm (PEq.comp_assoc _ _ _)
    refine hstep.trans (PEq.trans ?_ (PEq.symm (PEq.comp_id _)))
    match g with
    | .inl () =>
        exact (PEq.compL _ (pairR_caseR _ _ e2)).trans
          ((PEq.compL _ (PEq.id_comp _)).trans (inr_either _ _))
    | .inr () =>
        exact (PEq.compL _ (pairR_caseR _ _ g2)).trans
          ((PEq.compL _ (PEq.id_comp _)).trans (inl_either _ _))

/-! ### Provable injectivity of the cyclic annotation -/

theorem cyc_eq (A : Ty) :
    cyc A ≡ₜ (TyF2.concatMap (.prod (.list (.prod .p1 .p2)) (.sum .unit .p1)) A A ⨟
      listF (iotaS A)) := by
  have hp₁ : ((inl A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A)) ≡ₜ annS A g2 := by
    calc ((inl A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A))
        ≡ₜ (inl A A ⨟ (pureT (A ⊕' A) ⨟ listF (iotaS A))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inl A A ⨟ (iotaS A ⨟ pureT (PT A))) :=
          PEq.compR _ (PEq.symm (pureT_natural _))
      _ ≡ₜ ((inl A A ⨟ iotaS A) ⨟ pureT (PT A)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ annS A g2 := PEq.compL _ (inl_either _ _)
  have hp₂ : ((inr A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A)) ≡ₜ annS A e2 := by
    calc ((inr A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A))
        ≡ₜ (inr A A ⨟ (pureT (A ⊕' A) ⨟ listF (iotaS A))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr A A ⨟ (iotaS A ⨟ pureT (PT A))) :=
          PEq.compR _ (PEq.symm (pureT_natural _))
      _ ≡ₜ ((inr A A ⨟ iotaS A) ⨟ pureT (PT A)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ annS A e2 := PEq.compL _ (inr_either _ _)
  refine PEq.symm ?_
  calc ((homT ((inl A A ⨟ pureT (A ⊕' A)) ⊙ (inr A A ⨟ pureT (A ⊕' A))) ⊙
          either (nilT (A ⊕' A)) (inl A A ⨟ pureT (A ⊕' A))) ⨟ listF (iotaS A))
      ≡ₜ ((homT ((inl A A ⨟ pureT (A ⊕' A)) ⊙ (inr A A ⨟ pureT (A ⊕' A))) ⨟
            listF (iotaS A)) ⊙
          ((either (nilT (A ⊕' A)) (inl A A ⨟ pureT (A ⊕' A))) ⨟ listF (iotaS A))) :=
        fdot_comp_listF _ _ _
    _ ≡ₜ cyc A := by
        refine fdot_congr ?_ ?_
        · calc (homT ((inl A A ⨟ pureT (A ⊕' A)) ⊙ (inr A A ⨟ pureT (A ⊕' A))) ⨟
                  listF (iotaS A))
              ≡ₜ homT (((inl A A ⨟ pureT (A ⊕' A)) ⊙ (inr A A ⨟ pureT (A ⊕' A))) ⨟
                  listF (iotaS A)) := homT_comp_listF _ _
            _ ≡ₜ homT (((inl A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A)) ⊙
                  ((inr A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A))) :=
                homT_congr (fdot_comp_listF _ _ _)
            _ ≡ₜ homT (annS A g2 ⊙ annS A e2) := homT_congr (fdot_congr hp₁ hp₂)
        · calc ((either (nilT (A ⊕' A)) (inl A A ⨟ pureT (A ⊕' A))) ⨟ listF (iotaS A))
              ≡ₜ either (nilT (A ⊕' A) ⨟ listF (iotaS A))
                  ((inl A A ⨟ pureT (A ⊕' A)) ⨟ listF (iotaS A)) := either_comp _ _ _
            _ ≡ₜ either (nilT (PT A)) (annS A g2) :=
                either_congr (nilT_natural _) hp₁

theorem cyc_injective (A : Ty) : ProvablyInjective (cyc A) := by
  obtain ⟨u, hu, _⟩ := iotaS_iso A
  exact ProvablyInjective.of_peq (cyc_eq A) (ProvablyInjective.comp
    (Term.cyclic_annotation_injective A A) (ProvablyInjective.listF ⟨u, hu⟩))

/-! ### Two computations of scans

Unprefixing is the scan `shiftL`, run from the group identity over the list of pairs
annotated by their own group element (`Lax149335Proofs.Term.unpref_eq_scan`).  The lists that occur
in the diagram of the appendix are the empty list and one-element lists, so only two
computations of scans are needed. -/

/-- **Scanning the empty list.**  The empty list is left unchanged and the carry is kept. -/
theorem scanL_nilT {X Y : Ty} (v : Value X) :
    scanL X Y v (nilT (Y ⊗ X)) ≡ₜ pairR (nilT (X ⊗ Y)) v := by
  refine scanL_eq_pairR v v _ _ ?_
  have hu : (Term.toUnit Ty.unit ⨟ nilT (X ⊕' Y)) ≡ₜ nilT (X ⊕' Y) :=
    (PEq.compL _ (PEq.unit_unique _ (Term.id Ty.unit))).trans (PEq.id_comp _)
  calc dotL (inlV v Y) (nilT (Y ⊗ X) ⨟ cListYX X Y)
      ≡ₜ dotL (inlV v Y) (Term.toUnit Ty.unit ⨟ nilT (X ⊕' Y)) :=
        dotL_congr (PEq.refl _) ((homT_nil _).trans (PEq.symm hu))
    _ ≡ₜ (Term.toUnit Ty.unit ⨟ inlV v Y) := dotL_nilconst _ _ _
    _ ≡ₜ dotR (Term.toUnit Ty.unit ⨟ nilT (X ⊕' Y)) (inlV v Y) :=
        PEq.symm (dotR_nilconst _ _ _)
    _ ≡ₜ dotR (nilT (X ⊗ Y) ⨟ cListXY X Y) (inlV v Y) :=
        dotR_congr (hu.trans (PEq.symm (homT_nil _))) (PEq.refl _)

/-- **Scanning a one-element list.**  The single pair `(y, x)` is replaced by the pair
`(v, y)` of the incoming carry with `y`, and the new carry is `x`. -/
theorem scanL_one {X Y D : Ty} (v : Value X) (y : Term D Y) (x : Value X) :
    scanL X Y v (pairR y x ⨟ pureT (Y ⊗ X)) ≡ₜ pairR (pairL v y ⨟ pureT (X ⊗ Y)) x := by
  refine scanL_eq_pairR v x _ _ ?_
  have hin : ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y) ≡ₜ
      dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y) := by
    calc ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y)
        ≡ₜ (pairR y x ⨟ (pureT (Y ⊗ X) ⨟ cListYX X Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pairR y x ⨟ ((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))) :=
          PEq.compR _ (homT_pure _)
      _ ≡ₜ ((pairR y x ⨟ prodF (inr X Y ⨟ pureT (X ⊕' Y)) (inl X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (x ⨟ (inl X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.compL _ (pairR_prodF _ _ _ _)
      _ ≡ₜ dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y) :=
          PEq.compL _ (pairR_congr (PEq.refl _) (PEq.symm (PEq.comp_assoc _ _ _)))
  have hout : ((pairL v y ⨟ pureT (X ⊗ Y)) ⨟ cListXY X Y) ≡ₜ
      dotL (inlV v Y) (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) := by
    calc ((pairL v y ⨟ pureT (X ⊗ Y)) ⨟ cListXY X Y)
        ≡ₜ (pairL v y ⨟ (pureT (X ⊗ Y) ⨟ cListXY X Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pairL v y ⨟ ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y)))) :=
          PEq.compR _ (homT_pure _)
      _ ≡ₜ ((pairL v y ⨟ prodF (inl X Y ⨟ pureT (X ⊕' Y)) (inr X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairL (v ⨟ (inl X Y ⨟ pureT (X ⊕' Y))) (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.compL _ (pairL_prodF _ _ _ _)
      _ ≡ₜ dotL (inlV v Y) (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) :=
          PEq.compL _ (pairL_congr (PEq.symm (PEq.comp_assoc _ _ _)) (PEq.refl _))
  calc dotL (inlV v Y) ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y)
      ≡ₜ dotL (inlV v Y) (dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y)) :=
        dotL_congr (PEq.refl _) hin
    _ ≡ₜ dotR (dotL (inlV v Y) (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) (inlV x Y) :=
        PEq.symm (dotR_dotL _ _ _)
    _ ≡ₜ dotR ((pairL v y ⨟ pureT (X ⊗ Y)) ⨟ cListXY X Y) (inlV x Y) :=
        dotR_congr (PEq.symm hout) (PEq.refl _)

/-! ### Unprefixing the cyclic annotation -/

/-- The pair `(g, a)` produced by the annotation of a letter annotated by `g`. -/
def yA (A : Ty) (g : ⟦G2⟧) : Term A (G2 ⊗ A) := pairL (constFin g) (Term.id A)

/-- The annotation, in the sense of `Lax149335Proofs.Term.annot`, of a single annotated letter. -/
theorem annS_annot (A : Ty) (g : ⟦G2⟧) :
    (annS A g ⨟ Term.annot A 1) ≡ₜ
      (pairR (yA A g) (constFin g) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) := by
  have hsplit : annS A g ≡ₜ (unitR A ⨟ lastPair A g) := PEq.comp_assoc _ _ _
  have hy : (unitR A ⨟ yPart A g) ≡ₜ yA A g :=
    (comp_pairL _ _ _).trans (pairL_congr (PEq.refl _) (PEq.unitR_fst A))
  calc (annS A g ⨟ Term.annot A 1)
      ≡ₜ ((unitR A ⨟ lastPair A g) ⨟ Term.annot A 1) := PEq.compL _ hsplit
    _ ≡ₜ (unitR A ⨟ (lastPair A g ⨟ Term.annot A 1)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR A ⨟ (pairR (yPart A g) (constFin g) ⨟ pureT ((G2 ⊗ A) ⊗ G2))) :=
        PEq.compR _ (lastPair_annot A g)
    _ ≡ₜ ((unitR A ⨟ pairR (yPart A g) (constFin g)) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (pairR (unitR A ⨟ yPart A g) (constFin g) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) :=
        PEq.compL _ (comp_pairR _ _ _)
    _ ≡ₜ (pairR (yA A g) (constFin g) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) :=
        PEq.compL _ (pairR_congr hy (PEq.refl _))

/-- The division step of unprefixing, on a pair whose carry is `h` and whose group element
is `g`: the letter is re-annotated with `h⁻¹ g`. -/
theorem divide_pairL (A : Ty) (h g : ⟦G2⟧) :
    (pairL (constFin h) (yA A g) ⨟ gdiv A Z2) ≡ₜ ann A (letI := Z2; h⁻¹ * g) :=
  (pairL_caseL _ _ h).trans ((pairL_caseL _ _ g).trans (PEq.id_comp _))

/-- The post-processing of the scan on a one-element outcome. -/
theorem outBlock_gdiv (A : Ty) (h g : ⟦G2⟧) :
    ((pairL (constFin h) (yA A g) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⨟ listF (gdiv A Z2)) ≡ₜ
      annS A (letI := Z2; h⁻¹ * g) := by
  calc ((pairL (constFin h) (yA A g) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⨟ listF (gdiv A Z2))
      ≡ₜ (pairL (constFin h) (yA A g) ⨟ (pureT (G2 ⊗ (G2 ⊗ A)) ⨟ listF (gdiv A Z2))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (pairL (constFin h) (yA A g) ⨟ (gdiv A Z2 ⨟ pureT (PT A))) :=
        PEq.compR _ (PEq.symm (pureT_natural _))
    _ ≡ₜ ((pairL (constFin h) (yA A g) ⨟ gdiv A Z2) ⨟ pureT (PT A)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ annS A (letI := Z2; h⁻¹ * g) := PEq.compL _ (divide_pairL A h g)

/-- Unprefixing a single annotated letter re-annotates it with the same group element,
since the incoming carry is the group identity. -/
theorem annS_unpref (A : Ty) : (annS A g2 ⨟ unpref A Z2) ≡ₜ annS A g2 := by
  calc (annS A g2 ⨟ unpref A Z2)
      ≡ₜ (annS A g2 ⨟ (scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1) ⨟
          postUnpref A Z2)) := PEq.compR _ (unpref_eq_scan A Z2)
    _ ≡ₜ ((annS A g2 ⨟ scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1)) ⨟
          postUnpref A Z2) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2) (annS A g2 ⨟ Term.annot A 1) ⨟
          postUnpref A Z2) := PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2)
          (pairR (yA A g2) (constFin g2) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) ⨟ postUnpref A Z2) :=
        PEq.compL _ (scanL_congr _ (annS_annot A g2))
    _ ≡ₜ (pairR (pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) (constFin g2) ⨟
          postUnpref A Z2) := PEq.compL _ (scanL_one _ _ _)
    _ ≡ₜ ((pairR (pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) (constFin g2) ⨟
          fst ((G2 ⊗ (G2 ⊗ A))⋆) G2) ⨟ listF (gdiv A Z2)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⨟ listF (gdiv A Z2)) :=
        PEq.compL _ (pairR_fst _ _)
    _ ≡ₜ annS A g2 := outBlock_gdiv A e2 g2

/-- Unprefixing the empty list gives the empty list. -/
theorem nilT_unpref (A : Ty) : (nilT (PT A) ⨟ unpref A Z2) ≡ₜ nilT (PT A) := by
  calc (nilT (PT A) ⨟ unpref A Z2)
      ≡ₜ (nilT (PT A) ⨟ (scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1) ⨟
          postUnpref A Z2)) := PEq.compR _ (unpref_eq_scan A Z2)
    _ ≡ₜ ((nilT (PT A) ⨟ scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1)) ⨟
          postUnpref A Z2) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2) (nilT (PT A) ⨟ Term.annot A 1) ⨟
          postUnpref A Z2) := PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2) (nilT ((G2 ⊗ A) ⊗ G2)) ⨟ postUnpref A Z2) :=
        PEq.compL _ (scanL_congr _ (nilT_natural _))
    _ ≡ₜ (pairR (nilT (G2 ⊗ (G2 ⊗ A))) (constFin e2) ⨟ postUnpref A Z2) :=
        PEq.compL _ (scanL_nilT _)
    _ ≡ₜ ((pairR (nilT (G2 ⊗ (G2 ⊗ A))) (constFin e2) ⨟ fst ((G2 ⊗ (G2 ⊗ A))⋆) G2) ⨟
          listF (gdiv A Z2)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (nilT (G2 ⊗ (G2 ⊗ A)) ⨟ listF (gdiv A Z2)) := PEq.compL _ (pairR_fst _ _)
    _ ≡ₜ nilT (PT A) := nilT_natural _

/-- Unprefixing a cyclically annotated pair gives the constantly annotated pair. -/
theorem block_unpref (A : Ty) :
    ((annS A g2 ⊙ annS A e2) ⨟ unpref A Z2) ≡ₜ (annS A g2 ⊙ annS A g2) := by
  calc ((annS A g2 ⊙ annS A e2) ⨟ unpref A Z2)
      ≡ₜ ((annS A g2 ⊙ annS A e2) ⨟ (scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1) ⨟
          postUnpref A Z2)) := PEq.compR _ (unpref_eq_scan A Z2)
    _ ≡ₜ (((annS A g2 ⊙ annS A e2) ⨟
          scanL G2 (G2 ⊗ A) (constFin e2) (Term.annot A 1)) ⨟ postUnpref A Z2) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2) ((annS A g2 ⊙ annS A e2) ⨟ Term.annot A 1) ⨟
          postUnpref A Z2) := PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (scanL G2 (G2 ⊗ A) (constFin e2)
          ((pairR (yA A g2) (constFin g2) ⨟ pureT ((G2 ⊗ A) ⊗ G2)) ⊙
            (pairR (yA A e2) (constFin e2) ⨟ pureT ((G2 ⊗ A) ⊗ G2))) ⨟
          postUnpref A Z2) :=
        PEq.compL _ (scanL_congr _ ((fdot_comp_listF _ _ _).trans
          (fdot_congr (annS_annot A g2) (annS_annot A e2))))
    _ ≡ₜ (pairR ((pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⊙
            (pairL (constFin g2) (yA A e2) ⨟ pureT (G2 ⊗ (G2 ⊗ A)))) (constFin e2) ⨟
          postUnpref A Z2) :=
        PEq.compL _ (scanL_fdot _ _ _ _ _ _ _ (scanL_one _ _ _) (scanL_one _ _ _))
    _ ≡ₜ ((pairR ((pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⊙
            (pairL (constFin g2) (yA A e2) ⨟ pureT (G2 ⊗ (G2 ⊗ A)))) (constFin e2) ⨟
          fst ((G2 ⊗ (G2 ⊗ A))⋆) G2) ⨟ listF (gdiv A Z2)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⊙
            (pairL (constFin g2) (yA A e2) ⨟ pureT (G2 ⊗ (G2 ⊗ A)))) ⨟
          listF (gdiv A Z2)) := PEq.compL _ (pairR_fst _ _)
    _ ≡ₜ (((pairL (constFin e2) (yA A g2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⨟ listF (gdiv A Z2)) ⊙
          ((pairL (constFin g2) (yA A e2) ⨟ pureT (G2 ⊗ (G2 ⊗ A))) ⨟ listF (gdiv A Z2))) :=
        fdot_comp_listF _ _ _
    _ ≡ₜ (annS A g2 ⊙ annS A g2) :=
        fdot_congr (outBlock_gdiv A e2 g2) (outBlock_gdiv A g2 e2)

/-- Unprefixing the tail of a cyclic annotation leaves it unchanged. -/
theorem tail_unpref (A : Ty) :
    ((either (nilT (PT A)) (annS A g2)) ⨟ unpref A Z2) ≡ₜ
      either (nilT (PT A)) (annS A g2) :=
  (either_comp _ _ _).trans (either_congr (nilT_unpref A) (annS_unpref A))

/-! ### The cyclic annotation as a concatenation of blocks

Unprefixing is distributed over the concatenation map by
`Lax149335Proofs.Term.unpref_commutes_with_concat`, which applies to a concatenation whose blocks
all end with the group identity.  The blocks of the cyclic annotation are the two-element
lists `[(a,g¹),(b,g⁰)]`, which do end with the group identity, so the lemma applies. -/

/-- The tail component of the cyclic annotation. -/
def tailT (A : Ty) : Term (Ty.unit ⊕' A) ((PT A)⋆) := either (nilT (PT A)) (annS A g2)

/-- A block of the cyclic annotation, as an element of the type `T_{g⁰}` of the appendix:
the pair `(a,b)` is sent to the list `[(a,g¹)]` together with the last letter `b`. -/
def blkT (A : Ty) : Term (A ⊗ A) (TgTy A 1) := prodF (annS A g2) (unitR A)

/-- A block, injected by `ι_{g⁰}`, is the cyclically annotated pair. -/
theorem blkT_iotaG (A : Ty) : (blkT A ⨟ iotaG A e2) ≡ₜ (annS A g2 ⊙ annS A e2) := by
  calc (prodF (annS A g2) (unitR A) ⨟
        (prodF (Term.id ((PT A)⋆)) (prodF (Term.id A) (constFin e2)) ⨟ append (PT A)))
      ≡ₜ ((prodF (annS A g2) (unitR A) ⨟
          prodF (Term.id ((PT A)⋆)) (prodF (Term.id A) (constFin e2))) ⨟ append (PT A)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (annS A g2) (ann A e2) ⨟ append (PT A)) :=
        PEq.compL _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _)))
    _ ≡ₜ (prodF (annS A g2) (ann A e2) ⨟
          (prodF (Term.id ((PT A)⋆)) (pureT (PT A)) ⨟ binconcat (PT A))) :=
        PEq.compR _ (PEq.append_def _)
    _ ≡ₜ ((prodF (annS A g2) (ann A e2) ⨟
          prodF (Term.id ((PT A)⋆)) (pureT (PT A))) ⨟ binconcat (PT A)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (annS A g2 ⊙ annS A e2) :=
        PEq.compL _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _)))

/-- The cyclic annotation, written as the concatenation of a list of blocks and a tail. -/
theorem cyc_as_concat (A : Ty) :
    cyc A ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
      (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
        (concat (PT A) ⊙ Term.id ((PT A)⋆)))) := by
  refine PEq.symm ?_
  calc (prodF (listF (blkT A)) (tailT A) ⨟
        (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
          (concat (PT A) ⊙ Term.id ((PT A)⋆))))
      ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
          ((listF (iotaG A e2) ⨟ concat (PT A)) ⊙
            (Term.id ((PT A)⋆) ⨟ Term.id ((PT A)⋆)))) :=
        PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
          (homT (iotaG A e2) ⊙ Term.id ((PT A)⋆))) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (PEq.id_comp _))
    _ ≡ₜ ((listF (blkT A) ⨟ homT (iotaG A e2)) ⊙ (tailT A ⨟ Term.id ((PT A)⋆))) :=
        fdot_precomp _ _ _ _
    _ ≡ₜ (homT (blkT A ⨟ iotaG A e2) ⊙ tailT A) :=
        fdot_congr (PEq.symm (homT_precomp _ _)) (PEq.comp_id _)
    _ ≡ₜ cyc A := fdot_congr (homT_congr (blkT_iotaG A)) (PEq.refl _)

/-- The constant annotation of the concatenation map. -/
theorem cmap_constAnn (A : Ty) :
    (cmap A ⨟ constAnn A) ≡ₜ (homT (annS A g2 ⊙ annS A g2) ⊙ tailT A) := by
  have hpure : (pureT A ⨟ listF (ann A g2)) ≡ₜ annS A g2 := PEq.symm (pureT_natural _)
  calc ((homT (pureT A ⊙ pureT A) ⊙ either (nilT A) (pureT A)) ⨟ listF (ann A g2))
      ≡ₜ ((homT (pureT A ⊙ pureT A) ⨟ listF (ann A g2)) ⊙
          (either (nilT A) (pureT A) ⨟ listF (ann A g2))) := fdot_comp_listF _ _ _
    _ ≡ₜ (homT ((pureT A ⊙ pureT A) ⨟ listF (ann A g2)) ⊙
          either (nilT A ⨟ listF (ann A g2)) (pureT A ⨟ listF (ann A g2))) :=
        fdot_congr (homT_comp_listF _ _) (either_comp _ _ _)
    _ ≡ₜ (homT ((pureT A ⨟ listF (ann A g2)) ⊙ (pureT A ⨟ listF (ann A g2))) ⊙
          either (nilT (PT A)) (annS A g2)) :=
        fdot_congr (homT_congr (fdot_comp_listF _ _ _))
          (either_congr (nilT_natural _) hpure)
    _ ≡ₜ (homT (annS A g2 ⊙ annS A g2) ⊙ tailT A) :=
        fdot_congr (homT_congr (fdot_congr hpure hpure)) (PEq.refl _)

/-- **The diagram of the appendix commutes**: unprefixing the cyclic annotation gives the
constant annotation. -/
theorem cyc_unpref (A : Ty) : (cyc A ⨟ unpref A Z2) ≡ₜ (cmap A ⨟ constAnn A) := by
  have hblock : (blkT A ⨟ (iotaG A e2 ⨟ unpref A Z2)) ≡ₜ (annS A g2 ⊙ annS A g2) :=
    (PEq.symm (PEq.comp_assoc _ _ _)).trans
      ((PEq.compL _ (blkT_iotaG A)).trans (block_unpref A))
  calc (cyc A ⨟ unpref A Z2)
      ≡ₜ ((prodF (listF (blkT A)) (tailT A) ⨟
          (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
            (concat (PT A) ⊙ Term.id ((PT A)⋆)))) ⨟ unpref A Z2) :=
        PEq.compL _ (cyc_as_concat A)
    _ ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
          (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
            ((concat (PT A) ⊙ Term.id ((PT A)⋆)) ⨟ unpref A Z2))) :=
        (PEq.comp_assoc _ _ _).trans (PEq.compR _ (PEq.comp_assoc _ _ _))
    _ ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
          (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
            (prodF (listF (unpref A Z2)) (unpref A Z2) ⨟
              (concat (PT A) ⊙ Term.id ((PT A)⋆))))) :=
        PEq.compR _ (unpref_commutes_with_concat Z2)
    _ ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
          ((prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
            prodF (listF (unpref A Z2)) (unpref A Z2)) ⨟
              (concat (PT A) ⊙ Term.id ((PT A)⋆)))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (listF (blkT A)) (tailT A) ⨟
          (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
            prodF (listF (unpref A Z2)) (unpref A Z2))) ⨟
              (concat (PT A) ⊙ Term.id ((PT A)⋆))) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (listF (annS A g2 ⊙ annS A g2)) (tailT A) ⨟
          (concat (PT A) ⊙ Term.id ((PT A)⋆))) := by
        refine PEq.compL _ ?_
        calc (prodF (listF (blkT A)) (tailT A) ⨟
              (prodF (listF (iotaG A e2)) (Term.id ((PT A)⋆)) ⨟
                prodF (listF (unpref A Z2)) (unpref A Z2)))
            ≡ₜ (prodF (listF (blkT A)) (tailT A) ⨟
                prodF (listF (iotaG A e2) ⨟ listF (unpref A Z2))
                  (Term.id ((PT A)⋆) ⨟ unpref A Z2)) :=
              PEq.compR _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ prodF (listF (blkT A) ⨟ (listF (iotaG A e2) ⨟ listF (unpref A Z2)))
                (tailT A ⨟ (Term.id ((PT A)⋆) ⨟ unpref A Z2)) := PEq.prod_comp _ _ _ _
          _ ≡ₜ prodF (listF (blkT A) ⨟ listF (iotaG A e2 ⨟ unpref A Z2))
                (tailT A ⨟ unpref A Z2) :=
              PEq.congr_prodF (PEq.compR _ (PEq.list_comp _ _))
                (PEq.compR _ (PEq.id_comp _))
          _ ≡ₜ prodF (listF (blkT A ⨟ (iotaG A e2 ⨟ unpref A Z2))) (tailT A) :=
              PEq.congr_prodF (PEq.list_comp _ _) (tail_unpref A)
          _ ≡ₜ prodF (listF (annS A g2 ⊙ annS A g2)) (tailT A) :=
              PEq.congr_prodF (PEq.congr_listF hblock) (PEq.refl _)
    _ ≡ₜ ((listF (annS A g2 ⊙ annS A g2) ⨟ concat (PT A)) ⊙
          (tailT A ⨟ Term.id ((PT A)⋆))) := fdot_precomp _ _ _ _
    _ ≡ₜ (homT (annS A g2 ⊙ annS A g2) ⊙ tailT A) :=
        fdot_congr (PEq.refl _) (PEq.comp_id _)
    _ ≡ₜ (cmap A ⨟ constAnn A) := PEq.symm (cmap_constAnn A)

/-- The constant annotation followed by the group prefix multiplication is the cyclic
annotation. -/
theorem cmap_annot_pref (A : Ty) : ((cmap A ⨟ constAnn A) ⨟ pref A Z2) ≡ₜ cyc A := by
  calc ((cmap A ⨟ constAnn A) ⨟ pref A Z2)
      ≡ₜ ((cyc A ⨟ unpref A Z2) ⨟ pref A Z2) := PEq.compL _ (PEq.symm (cyc_unpref A))
    _ ≡ₜ (cyc A ⨟ (unpref A Z2 ⨟ pref A Z2)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (cyc A ⨟ Term.id ((PT A)⋆)) := PEq.compR _ (PEq.unpref_pref A Z2)
    _ ≡ₜ cyc A := PEq.comp_id _

/-- **Lemma 6.7 for the bundle size two, injectivity half.**  The concatenation map
`(A × A)* × A^{<2} ↣ A*` is provably injective: a one-sided inverse is obtained by
annotating every letter with the generator, multiplying the prefixes (which produces the
cyclic annotation), and inverting the cyclic annotation. -/
theorem cmap_injective (A : Ty) : ProvablyInjective (cmap A) := by
  obtain ⟨r, hr⟩ := cyc_injective A
  refine ⟨constAnn A ⨟ (pref A Z2 ⨟ r), ?_⟩
  calc (cmap A ⨟ (constAnn A ⨟ (pref A Z2 ⨟ r)))
      ≡ₜ (((cmap A ⨟ constAnn A) ⨟ pref A Z2) ⨟ r) :=
        (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (cyc A ⨟ r) := PEq.compL _ (cmap_annot_pref A)
    _ ≡ₜ Term.id (F2.app A) := hr

/-! ### Transfer to the shape used for bundles

The shape `TyF.bundle 1` used in `Lax149335Proofs.Appendix.Bundles.Composition` is
`(A × (A × 1))* × (1 + A × 1)`, which differs from `F2` by the unit factors; the two
concatenation maps are related by a content-preserving isomorphism. -/

/-- Dropping the trailing unit factor of `A¹` preserves contents. -/
theorem contIso_pow_one (A : Ty) : ContIso (pureT A ⊙ nilT A) (pureT A) := by
  refine ⟨fst A Ty.unit, ⟨unitR A, PEq.fst_unitR A, PEq.unitR_fst A⟩, ?_⟩
  have hnil : (unitR A ⨟ (pureT A ⊙ nilT A)) ≡ₜ pureT A :=
    (PEq.symm (PEq.comp_assoc _ _ _)).trans (dotR_nil (pureT A))
  calc (fst A Ty.unit ⨟ pureT A)
      ≡ₜ (fst A Ty.unit ⨟ (unitR A ⨟ (pureT A ⊙ nilT A))) :=
        PEq.compR _ (PEq.symm hnil)
    _ ≡ₜ ((fst A Ty.unit ⨟ unitR A) ⨟ (pureT A ⊙ nilT A)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (A ⊗ Ty.unit) ⨟ (pureT A ⊙ nilT A)) := PEq.compL _ (PEq.fst_unitR A)
    _ ≡ₜ (pureT A ⊙ nilT A) := PEq.id_comp _

/-- The concatenation map of the shape `TyF.bundle 1` and the concatenation map `cmap` are
related by a content-preserving isomorphism. -/
theorem contIso_bundle_two (A : Ty) :
    ContIso (TyF.concatMap (TyF.bundle 1) A) (cmap A) :=
  ContIso.prod
    (ContIso.list (ContIso.prod (ContIso.refl (pureT A)) (contIso_pow_one A)))
    (ContIso.sum (ContIso.refl (nilT A)) (contIso_pow_one A))

/-- **Lemma 6.7 for the bundle size two, injectivity half**, in the form used by
`Lax149335Proofs.BundleIso`: the concatenation map `(A²)* × A^{<2} ↣ A*` is provably injective. -/
theorem bundle_two_injective (A : Ty) :
    ProvablyInjective (TyF.concatMap (TyF.bundle 1) A) := by
  obtain ⟨h, ⟨h', hh', _⟩, he⟩ := contIso_bundle_two A
  exact ProvablyInjective.of_peq (PEq.symm he)
    (ProvablyInjective.comp ⟨h', hh'⟩ (cmap_injective A))

/-! ### Arbitrarily large bundles, injectivity half

Bundles of bundles compose for the injectivity half exactly as they do for the full bundle
lemma (`Lax149335Proofs.Appendix.Bundles.Injectivity`), so the injectivity half for the bundle
size two, which is proved above, gives the injectivity half for arbitrarily large bundle
sizes.  These statements do *not* depend on the surjectivity half, hence not on Axiom 16. -/

/-- The injectivity half of Lemma 6.7 for the bundle size two, in the packaged form. -/
theorem bundleInj_one : BundleInj 1 := bundle_two_injective

/-- **The injectivity half of Lemma 6.7 for all the bundle sizes `2ʲ⁺¹`.**  For every type
`A`, the concatenation map `(A^{2ʲ⁺¹})* × A^{<2ʲ⁺¹} ↣ A*` is provably injective. -/
theorem bundle_two_pow_injective (j : ℕ) : BundleInj (2 ^ (j + 1) - 1) :=
  BundleInj.two_pow bundleInj_one j

end BundleTwo

end Lax149335Proofs

bridge_export Lax149335Proofs
