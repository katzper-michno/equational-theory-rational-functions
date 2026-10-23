import Lax149335Proofs.Appendix.Groups.ProductConsolidation
import Lax149335Proofs.Appendix.Groups.PrefixExchange

/-!
# The star case of the consolidation claim (appendix, proof of the prefix exchange lemma)

This file proves `Lax149335Proofs.StarConsolidation`, the second of the two claims on which
`Lax149335Proofs.Appendix.Groups.PrefixExchange` reduces the prefix exchange lemma: the
*top-right face* of the star diagram of the appendix.

The claim asks for two aperiodic terms — `ap`, which annotates a block of a list of blocks
with the group label of its last letter, and `q`, which re-multiplies and concatenates the
blocks — such that unprefixing every block and concatenating is the same as annotating,
prefix-multiplying the annotations once, re-multiplying, concatenating and unprefixing once:

```
(T B)*  --(unspref)*--> (Σ B)**  --concat-->  (Σ B)*
   |                                             ^
 (ap)*                                        unspref
   v                                             |
(Σ (Σ B)*)*  --spref-->  T (Σ B)*  ----q---->   T B
```

The proof is the one of the appendix.  Its two ingredients are:

* the terms `Lax149335Proofs.Term.starRepair` (the appendix's `repair`, followed by "forget the
  outer label") and `Lax149335Proofs.Term.starQ` (the appendix's `postrepair`, followed by "multiply
  and concat").  `repair` makes the last letter of a block carry the outer label — inserting
  a letter built from a fixed value of `B` if the block is empty and the label is not the
  group identity, which is the *non-natural choice* the appendix has to make;
* the *isomorphism trick*: `spref` is a provable isomorphism, so `unspref ; starRepair*` is a
  one-sided inverse of `ap* ; spref`, and the claim follows from the two **aperiodic**
  identities `Lax149335Proofs.Term.starAnn_starRepair` and `Lax149335Proofs.star_square`, both of which are
  proved denotationally by Corollary 7.6 (`Lax149335Proofs.completeness_aperiodic`).

The denotational content is the combinatorial lemma `Lax149335Proofs.Term.star_main`: unprefixing
each repaired block separately, from the group identity, is the same as unprefixing once the
concatenation of the repaired blocks, each multiplied by the product of the labels of the
blocks strictly before it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Word-level unprefixing with an accumulator -/

/-- The word-level form of `unspref`, with an arbitrary initial accumulator: decode the
annotations, unprefix starting from `acc`, encode again. -/
noncomputable def unsprefWA (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (acc : ⟦Ty.finAlph n⟧) (v : List ⟦sigmaTy B n⟧) : List ⟦sigmaTy B n⟧ :=
  letI := G
  (unprefDen acc (v.map (sigmaDec B n).den)).map (sigmaEnc B n).den

theorem unsprefWA_append (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (acc : ⟦Ty.finAlph n⟧) (v₁ v₂ : List ⟦sigmaTy B n⟧) :
    unsprefWA B G acc (v₁ ++ v₂) =
      unsprefWA B G acc v₁ ++
        unsprefWA B G (lastAcc acc (v₁.map (sigmaDec B n).den)) v₂ := by
  letI := G
  simp [unsprefWA, unprefDen_append]

/-! ### The repaired block -/

/-- The *repair* operation of the appendix, at the level of words: the last letter of the
word is given the label `d`; if the word is empty, then it is left empty when `d` is the
group identity, and replaced by the one-letter word carrying the default value of `B` and the
label `d` otherwise. -/
noncomputable def repW (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) : List ⟦sigmaTy B n⟧ :=
  letI := G
  match w.getLast? with
  | none => if d = 1 then [] else [(injSigma B d).den ((Term.defaultValue B).den ())]
  | some z => w.dropLast ++ [(injSigma B d).den ((sigmaDec B n).den z).1]

theorem repW_nil (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧) :
    repW B G d [] =
      letI := G
      if d = 1 then [] else [(injSigma B d).den ((Term.defaultValue B).den ())] := rfl
theorem repW_concat (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d g : ⟦Ty.finAlph n⟧)
    (u : List ⟦sigmaTy B n⟧) (a : ⟦B⟧) :
    repW B G d (u ++ [(injSigma B g).den a]) = u ++ [(injSigma B d).den a] := by
  simp [repW]

/-- The accumulated group element of a repaired block is its label. -/
theorem lastAcc_repW (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) :
    letI := G
    lastAcc (1 : ⟦Ty.finAlph n⟧) ((repW B G d w).map (sigmaDec B n).den) = d := by
  letI := G
  rcases List.eq_nil_or_concat w with rfl | ⟨u, z, rfl⟩
  · by_cases h : d = 1 <;> simp [repW_nil, h]
  · obtain ⟨a, g, rfl⟩ := sigma_cases B z
    simp only [List.concat_eq_append]
    rw [repW_concat]
    simpa using lastAcc_append_singleton (1 : ⟦Ty.finAlph n⟧) (u.map (sigmaDec B n).den) a d

/-! ### Multiplying a whole block -/

theorem lastAcc_map_mul {α : Type} {H : Type} [Group H] (c : H) :
    ∀ (acc : H) (l : List (α × H)),
      lastAcc (c * acc) (l.map (fun p => (p.1, c * p.2))) = c * lastAcc acc l
  | _, [] => rfl
  | acc, (a, k) :: t => by
      simpa using lastAcc_map_mul c k t

theorem lastAcc_mul_repW (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (c d : ⟦Ty.finAlph n⟧) (w : List ⟦sigmaTy B n⟧) :
    letI := G
    lastAcc c
        ((((repW B G d w).map (sigmaMul B G c).den)).map (sigmaDec B n).den) = c * d := by
  letI := G
  have h := lastAcc_map_mul (α := ⟦B⟧) c (1 : ⟦Ty.finAlph n⟧)
    ((repW B G d w).map (sigmaDec B n).den)
  rw [mul_one] at h
  have h2 : lastAcc (1 : ⟦Ty.finAlph n⟧) ((repW B G d w).map (sigmaDec B n).den) = d :=
    lastAcc_repW B G d w
  refine Eq.trans ?_ (congrArg (fun x => c * x) h2)
  rw [dec_map_sigmaMul B G c]
  exact h

theorem unsprefWA_mul (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (c : ⟦Ty.finAlph n⟧)
    (v : List ⟦sigmaTy B n⟧) :
    unsprefWA B G c (v.map (sigmaMul B G c).den) = unsprefW B G v := by
  letI := G
  have hmul := unprefDen_map_mul (α := ⟦B⟧) c 1 (v.map (sigmaDec B n).den)
  rw [mul_one] at hmul
  simp only [unsprefWA, unsprefW, dec_map_sigmaMul B G c]
  exact congrArg (List.map (sigmaEnc B n).den) hmul

/-! ### The terms -/

/-- The annotation term `ap` of the claim: a block, presented in the type `T B` in which its
last letter is directly accessible, is annotated with the label of that last letter, or with
the group identity if it is empty. -/
def starAnn (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (tTy B n) (sigmaTy ((sigmaTy B n)⋆) n) :=
  either (nilT (sigmaTy B n) ⨟ injSigma ((sigmaTy B n)⋆) (letI := G; 1))
    (sigmaCase (fun g =>
      (prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B g ⨟ pureT (sigmaTy B n)) ⨟
        binconcat (sigmaTy B n)) ⨟ injSigma ((sigmaTy B n)⋆) g))

/-- The body of the appendix's `repair`, for a fixed label `d`: the last letter of the word
is relabelled by `d`; an empty word is left empty if `d` is the identity, and is replaced by
the one-letter word built from the default value of `B` otherwise. -/
def starRepairBody (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧) :
    Term ((sigmaTy B n)⋆) ((sigmaTy B n)⋆) :=
  toT B n ⨟
    either
      (letI := G;
        if d = 1 then nilT (sigmaTy B n)
        else Term.defaultValue B ⨟ (injSigma B d ⨟ pureT (sigmaTy B n)))
      (sigmaCase (fun _ =>
        prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B d ⨟ pureT (sigmaTy B n)) ⨟
          binconcat (sigmaTy B n)))

/-- The appendix's `repair`, followed by "forget the outer label": a one-sided inverse of
`starAnn`. -/
def starRepair (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (sigmaTy ((sigmaTy B n)⋆) n) (tTy B n) :=
  sigmaCase (fun d => starRepairBody B G d ⨟ toT B n)

/-- The body of the appendix's `postrepair`, followed by the multiplication of the whole
block: the block is repaired with the label `d` recovered from the two-letter window, and
then all its labels are multiplied on the left by `h * d⁻¹`, which is the product of the
labels of all the blocks strictly before it. -/
def starQBody (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d h : ⟦Ty.finAlph n⟧) :
    Term ((sigmaTy B n)⋆) ((sigmaTy B n)⋆) :=
  toT B n ⨟
    either
      (letI := G;
        if d = 1 then nilT (sigmaTy B n)
        else Term.defaultValue B ⨟ (injSigma B h ⨟ pureT (sigmaTy B n)))
      (sigmaCase (fun _ =>
        prodF (listF (sigmaMul B G (letI := G; h * d⁻¹)))
            (injSigma B h ⨟ pureT (sigmaTy B n)) ⨟
          binconcat (sigmaTy B n)))

/-- Duplicating the outer label of a letter into its payload, so that the label from before
the prefix multiplication can be recovered by a further unprefixing. -/
def starTag (B : Ty) (n : ℕ) :
    Term (sigmaTy ((sigmaTy B n)⋆) n) (sigmaTy (sigmaTy ((sigmaTy B n)⋆) n) n) :=
  sigmaCase (fun h =>
    injSigma ((sigmaTy B n)⋆) h ⨟ injSigma (sigmaTy ((sigmaTy B n)⋆) n) h)

/-- The case tree of `starQ`: the outer label `d` of the tagged and unprefixed letter and the
label `h` recorded in its payload determine the repair and the multiplication. -/
def starQLetter (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (sigmaTy (sigmaTy ((sigmaTy B n)⋆) n) n) ((sigmaTy B n)⋆) :=
  sigmaCase (fun d => sigmaCase (fun h => starQBody B G d h))

/-- The term `q` of the claim: the appendix's `postrepair` followed by "multiply and
concat". -/
def starQ (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (tTy ((sigmaTy B n)⋆) n) (tTy B n) :=
  fromT ((sigmaTy B n)⋆) n ⨟
    (listF (starTag B n) ⨟
      (toT (sigmaTy ((sigmaTy B n)⋆) n) n ⨟
        (unspref (sigmaTy ((sigmaTy B n)⋆) n) G ⨟
          (listF (starQLetter B G) ⨟ (concat (sigmaTy B n) ⨟ toT B n)))))

/-! ### Aperiodicity -/

@[simp] theorem usesPref_starAnn (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (starAnn B G) = false := by
  have hcase : usesPref (sigmaCase (fun g : ⟦Ty.finAlph n⟧ =>
      (prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B g ⨟ pureT (sigmaTy B n)) ⨟
        binconcat (sigmaTy B n)) ⨟ injSigma ((sigmaTy B n)⋆) g)) = false :=
    usesPref_sigmaCase _ (fun g => by
      simp [usesPref, usesPref_injSigma, pureT, binconcat])
  simp [starAnn, usesPref, usesPref_injSigma, nilT, hcase]

@[simp] theorem usesPref_starRepair (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (starRepair B G) = false := by
  refine usesPref_sigmaCase _ (fun d => ?_)
  have hbody : usesPref (starRepairBody B G d) = false := by
    have hemp : usesPref
        (letI := G;
          if d = 1 then nilT (sigmaTy B n)
          else Term.defaultValue B ⨟ (injSigma B d ⨟ pureT (sigmaTy B n))) = false := by
      letI := G
      by_cases h : d = 1
      · simp [h, nilT, usesPref]
      · simpa [h, usesPref, usesPref_injSigma, pureT, IsAperiodic] using aperiodic_defaultValue B
    have hcase : usesPref (sigmaCase (fun _ : ⟦Ty.finAlph n⟧ =>
        prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B d ⨟ pureT (sigmaTy B n)) ⨟
          binconcat (sigmaTy B n))) = false :=
      usesPref_sigmaCase _ (fun _ => by
        simp [usesPref, usesPref_injSigma, pureT, binconcat])
    simp [starRepairBody, usesPref, hemp, hcase]
  simp [usesPref, hbody]

@[simp] theorem usesPref_starQ (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (starQ B G) = false := by
  have hletter : usesPref (starQLetter B G) = false := by
    refine usesPref_sigmaCase _ (fun d => usesPref_sigmaCase _ (fun h => ?_))
    have hemp : usesPref
        (letI := G;
          if d = 1 then nilT (sigmaTy B n)
          else Term.defaultValue B ⨟ (injSigma B h ⨟ pureT (sigmaTy B n))) = false := by
      letI := G
      by_cases hd : d = 1
      · simp [hd, nilT, usesPref]
      · simpa [hd, usesPref, usesPref_injSigma, pureT, IsAperiodic] using aperiodic_defaultValue B
    have hcase : usesPref (sigmaCase (fun _ : ⟦Ty.finAlph n⟧ =>
        prodF (listF (sigmaMul B G (letI := G; h * d⁻¹)))
            (injSigma B h ⨟ pureT (sigmaTy B n)) ⨟
          binconcat (sigmaTy B n))) = false :=
      usesPref_sigmaCase _ (fun _ => by
        simp [usesPref, usesPref_injSigma, pureT, binconcat, usesPref_sigmaMul])
    simp [starQBody, usesPref, hemp, hcase]
  have htag : usesPref (starTag B n) = false :=
    usesPref_sigmaCase _ (fun h => by simp [usesPref, usesPref_injSigma])
  simp [starQ, usesPref, htag, hletter]

theorem isAperiodic_starAnn (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    IsAperiodic (starAnn B G) := usesPref_starAnn B G

theorem isAperiodic_starQ (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    IsAperiodic (starQ B G) := usesPref_starQ B G

/-! ### Denotations -/

theorem den_starAnn_inl (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (starAnn B G).den (Sum.inl ()) =
      (injSigma ((sigmaTy B n)⋆) (letI := G; 1)).den [] := rfl

theorem den_starAnn_inr (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (g : ⟦Ty.finAlph n⟧)
    (u : List ⟦sigmaTy B n⟧) (a : ⟦B⟧) :
    (starAnn B G).den (Sum.inr ((injSigma (((sigmaTy B n)⋆) ⊗ B) g).den (u, a))) =
      (injSigma ((sigmaTy B n)⋆) g).den (u ++ [(injSigma B g).den a]) := by
  show (sigmaCase (fun g =>
      (prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B g ⨟ pureT (sigmaTy B n)) ⨟
        binconcat (sigmaTy B n)) ⨟ injSigma ((sigmaTy B n)⋆) g)).den
    ((injSigma (((sigmaTy B n)⋆) ⊗ B) g).den (u, a)) = _
  rw [den_sigmaCase]
  simp

theorem den_starRepairBody (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) :
    (starRepairBody B G d).den w = repW B G d w := by
  letI := G
  rcases List.eq_nil_or_concat w with rfl | ⟨u, z, rfl⟩
  · show (either _ _).den ((toT B n).den ([] : List ⟦sigmaTy B n⟧)) = _
    rw [den_toT_nil]
    by_cases h : d = 1 <;> simp [repW_nil, h]
  · obtain ⟨a, g, rfl⟩ := sigma_cases B z
    simp only [List.concat_eq_append]
    show (either _ _).den ((toT B n).den (u ++ [(injSigma B g).den a])) = _
    rw [den_toT_append]
    show (sigmaCase (fun _ =>
      prodF (Term.id ((sigmaTy B n)⋆)) (injSigma B d ⨟ pureT (sigmaTy B n)) ⨟
        binconcat (sigmaTy B n))).den ((injSigma (((sigmaTy B n)⋆) ⊗ B) g).den (u, a)) = _
    rw [den_sigmaCase, repW_concat]
    simp

theorem den_starRepair (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) :
    (starRepair B G).den ((injSigma ((sigmaTy B n)⋆) d).den w) =
      (toT B n).den (repW B G d w) := by
  show (sigmaCase (fun d => starRepairBody B G d ⨟ toT B n)).den
    ((injSigma ((sigmaTy B n)⋆) d).den w) = _
  rw [den_sigmaCase]
  simp [den_starRepairBody]

theorem den_starQBody (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d h : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) :
    (starQBody B G d h).den w =
      (repW B G d w).map (sigmaMul B G (letI := G; h * d⁻¹)).den := by
  letI := G
  rcases List.eq_nil_or_concat w with rfl | ⟨u, z, rfl⟩
  · show (either _ _).den ((toT B n).den ([] : List ⟦sigmaTy B n⟧)) = _
    rw [den_toT_nil]
    by_cases hd : d = 1
    · simp [repW_nil, hd]
    · simp only [repW_nil, if_neg hd, den_either]
      show [(injSigma B h).den ((Term.defaultValue B).den ())] = _
      simp [den_sigmaMul]
  · obtain ⟨a, g, rfl⟩ := sigma_cases B z
    simp only [List.concat_eq_append]
    show (either _ _).den ((toT B n).den (u ++ [(injSigma B g).den a])) = _
    rw [den_toT_append]
    show (sigmaCase (fun _ =>
      prodF (listF (sigmaMul B G (h * d⁻¹))) (injSigma B h ⨟ pureT (sigmaTy B n)) ⨟
        binconcat (sigmaTy B n))).den ((injSigma (((sigmaTy B n)⋆) ⊗ B) g).den (u, a)) = _
    rw [den_sigmaCase, repW_concat]
    simp [den_sigmaMul]

theorem den_starQLetter (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (d h : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy B n⟧) :
    (starQLetter B G).den
        ((injSigma (sigmaTy ((sigmaTy B n)⋆) n) d).den
          ((injSigma ((sigmaTy B n)⋆) h).den w)) =
      (repW B G d w).map (sigmaMul B G (letI := G; h * d⁻¹)).den := by
  show (sigmaCase (fun d => sigmaCase (fun h => starQBody B G d h))).den _ = _
  rw [den_sigmaCase, den_sigmaCase, den_starQBody]

theorem den_starTag (B : Ty) {n : ℕ} (z : ⟦sigmaTy ((sigmaTy B n)⋆) n⟧) :
    (sigmaDec (sigmaTy ((sigmaTy B n)⋆) n) n).den ((starTag B n).den z) =
      (z, ((sigmaDec ((sigmaTy B n)⋆) n).den z).2) := by
  obtain ⟨w, h, rfl⟩ := sigma_cases ((sigmaTy B n)⋆) z
  show (sigmaDec (sigmaTy ((sigmaTy B n)⋆) n) n).den
    ((sigmaCase (fun h =>
      injSigma ((sigmaTy B n)⋆) h ⨟ injSigma (sigmaTy ((sigmaTy B n)⋆) n) h)).den
        ((injSigma ((sigmaTy B n)⋆) h).den w)) = _
  rw [den_sigmaCase]
  simp

/-- The letter step of the left-hand column: encode a letter, repair it, and unprefix the
repaired block. -/
@[simp] theorem den_unspref_starRepair_enc (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (p : List ⟦sigmaTy B n⟧ × ⟦Ty.finAlph n⟧) :
    (unspref B G).den ((starRepair B G).den ((sigmaEnc ((sigmaTy B n)⋆) n).den p)) =
      unsprefW B G (repW B G p.2 p.1) := by
  obtain ⟨w, d⟩ := p
  rw [den_sigmaEnc, den_starRepair, den_unspref, den_fromT_toT]

/-- The letter step of the right-hand column: encode a tagged and unprefixed letter and
apply the case tree of `starQ`. -/
@[simp] theorem den_starQLetter_enc (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (q : ⟦sigmaTy ((sigmaTy B n)⋆) n⟧ × ⟦Ty.finAlph n⟧) :
    (starQLetter B G).den ((sigmaEnc (sigmaTy ((sigmaTy B n)⋆) n) n).den q) =
      letI := G
      (repW B G q.2 ((sigmaDec ((sigmaTy B n)⋆) n).den q.1).1).map
        (sigmaMul B G (((sigmaDec ((sigmaTy B n)⋆) n).den q.1).2 * q.2⁻¹)).den := by
  obtain ⟨z, d⟩ := q
  obtain ⟨w, h, rfl⟩ := sigma_cases ((sigmaTy B n)⋆) z
  rw [den_sigmaEnc, den_starQLetter, den_sigmaDec_injSigma]

/-! ### The combinatorial heart of the claim -/

/-- Unprefixing each repaired block on its own, from the group identity, and concatenating,
is the same as concatenating the repaired blocks, each multiplied by the product of the
labels of the blocks strictly before it, and unprefixing the result once. -/
theorem star_main (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    ∀ (W : List ⟦sigmaTy ((sigmaTy B n)⋆) n⟧) (acc : ⟦Ty.finAlph n⟧),
      letI := G
      ((unprefDen acc (W.map (sigmaDec ((sigmaTy B n)⋆) n).den)).map
          (fun p => unsprefW B G (repW B G p.2 p.1))).flatten =
        unsprefWA B G acc
          ((unprefDen acc
              (W.map (fun z => (z, ((sigmaDec ((sigmaTy B n)⋆) n).den z).2)))).map
            (fun q =>
              (repW B G q.2 ((sigmaDec ((sigmaTy B n)⋆) n).den q.1).1).map
                (sigmaMul B G
                  (((sigmaDec ((sigmaTy B n)⋆) n).den q.1).2 * q.2⁻¹)).den)).flatten := by
  letI := G
  intro W
  induction W with
  | nil => intro acc; simp [unsprefWA]
  | cons z t ih =>
      intro acc
      obtain ⟨w, h, rfl⟩ := sigma_cases ((sigmaTy B n)⋆) z
      have hdec : (sigmaDec ((sigmaTy B n)⋆) n).den ((injSigma ((sigmaTy B n)⋆) h).den w) =
          (w, h) := den_sigmaDec_injSigma _ h w
      have hc : h * (acc⁻¹ * h)⁻¹ = acc := by group
      have hacc : acc * (acc⁻¹ * h) = h := by group
      simp only [List.map_cons, hdec, unprefDen_cons, List.map_cons, List.flatten_cons, hc]
      rw [unsprefWA_append, unsprefWA_mul, lastAcc_mul_repW, hacc, ih h]

end Term

/-! ### The two aperiodic identities -/

/-- The repair term is a one-sided inverse of the annotation term. -/
theorem Term.starAnn_starRepair (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (Term.starAnn B G ⨟ Term.starRepair B G) ≡ₜ Term.id (Term.tTy B n) := by
  letI := G
  refine completeness_aperiodic _ _ ?_ ?_ ?_
  · simp [IsAperiodic, Term.usesPref]
  · simp [IsAperiodic, Term.usesPref]
  · funext t
    simp only [Term.den_comp, Term.den_id]
    match t with
    | .inl () =>
        rw [Term.den_starAnn_inl, Term.den_starRepair]
        simp [Term.repW_nil]
    | .inr s =>
        obtain ⟨⟨u, a⟩, g, rfl⟩ := Term.sigma_cases (((Term.sigmaTy B n)⋆) ⊗ B) s
        rw [Term.den_starAnn_inr, Term.den_starRepair, Term.repW_concat,
          Term.den_toT_append]

/-- The square that the isomorphism trick reduces the claim to: it is aperiodic, and holds
denotationally by `Lax149335Proofs.Term.star_main`. -/
theorem star_square (B : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    ((Term.unspref ((Term.sigmaTy B n)⋆) G ⨟ Term.listF (Term.starRepair B G)) ⨟
        (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) ≡ₜ
      (Term.starQ B G ⨟ Term.unspref B G) := by
  letI := G
  refine completeness_aperiodic _ _ ?_ ?_ ?_
  · simp [IsAperiodic, Term.usesPref]
  · simp [IsAperiodic, Term.usesPref]
  · funext T
    set W := (Term.fromT ((Term.sigmaTy B n)⋆) n).den T with hWdef
    set V : List ⟦Term.sigmaTy B n⟧ :=
      ((unprefDen (1 : ⟦Ty.finAlph n⟧)
          (W.map (fun z => (z, ((Term.sigmaDec ((Term.sigmaTy B n)⋆) n).den z).2)))).map
        (fun q =>
          (Term.repW B G q.2 ((Term.sigmaDec ((Term.sigmaTy B n)⋆) n).den q.1).1).map
            (Term.sigmaMul B G
              (((Term.sigmaDec ((Term.sigmaTy B n)⋆) n).den q.1).2 *
                q.2⁻¹)).den)).flatten with hVdef
    have hU : (Term.unspref ((Term.sigmaTy B n)⋆) G).den T =
        (unprefDen (1 : ⟦Ty.finAlph n⟧)
            (W.map (Term.sigmaDec ((Term.sigmaTy B n)⋆) n).den)).map
          (Term.sigmaEnc ((Term.sigmaTy B n)⋆) n).den := by
      rw [Term.den_unspref]
      rfl
    have hL : ((Term.unspref ((Term.sigmaTy B n)⋆) G ⨟ Term.listF (Term.starRepair B G)) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))).den T =
        ((unprefDen (1 : ⟦Ty.finAlph n⟧)
            (W.map (Term.sigmaDec ((Term.sigmaTy B n)⋆) n).den)).map
          (fun p => Term.unsprefW B G (Term.repW B G p.2 p.1))).flatten := by
      simp only [Term.den_comp, Term.den_listF, Term.den_concat, hU, List.map_map,
        Function.comp_def, Term.den_unspref_starRepair_enc]
      rfl
    have hV : (Term.starQ B G).den T = (Term.toT B n).den V := by
      simp only [hVdef, Term.starQ, Term.den_comp, Term.den_listF, Term.den_concat,
        Term.den_unspref, Term.den_fromT_toT, Term.unsprefW, List.map_map,
        Function.comp_def, Term.den_starTag, Term.den_starQLetter_enc]
      rfl
    have hR : (Term.starQ B G ⨟ Term.unspref B G).den T =
        Term.unsprefWA B G (1 : ⟦Ty.finAlph n⟧) V := by
      rw [Term.den_comp, hV, Term.den_unspref, Term.den_fromT_toT]
      rfl
    rw [hL, hR, hVdef]
    exact Term.star_main B G W 1

/-! ### The claim -/

/-- **Claim (star consolidation)** (appendix, proof of the prefix exchange lemma, star case:
the top-right face of the diagram). -/
theorem starConsolidation {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) : StarConsolidation G := by
  intro B
  refine ⟨Term.starAnn B G, Term.starQ B G, Term.isAperiodic_starAnn B G,
    Term.isAperiodic_starQ B G, ?_⟩
  have hid : (Term.listF (Term.starAnn B G) ⨟ Term.listF (Term.starRepair B G)) ≡ₜ
      Term.id ((Term.tTy B n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (Term.starAnn_starRepair B G)).trans (PEq.list_id _))
  calc (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))
      ≡ₜ (Term.id ((Term.tTy B n)⋆) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) :=
        PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟ Term.listF (Term.starRepair B G)) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) :=
        PEq.compL _ (PEq.symm hid)
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟
          (Term.id ((Term.sigmaTy ((Term.sigmaTy B n)⋆) n)⋆) ⨟
            Term.listF (Term.starRepair B G))) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) :=
        PEq.compL _ (PEq.compR _ (PEq.symm (PEq.id_comp _)))
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟
          ((Term.spref ((Term.sigmaTy B n)⋆) G ⨟ Term.unspref ((Term.sigmaTy B n)⋆) G) ⨟
            Term.listF (Term.starRepair B G))) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) :=
        PEq.compL _ (PEq.compR _ (PEq.compL _
          (PEq.symm (Term.spref_unspref ((Term.sigmaTy B n)⋆) G))))
    _ ≡ₜ (((Term.listF (Term.starAnn B G) ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟
          (Term.unspref ((Term.sigmaTy B n)⋆) G ⨟ Term.listF (Term.starRepair B G))) ⨟
          (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n))) :=
        PEq.compL _ ((PEq.compR _ (PEq.comp_assoc _ _ _)).trans
          (PEq.symm (PEq.comp_assoc _ _ _)))
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟
          ((Term.unspref ((Term.sigmaTy B n)⋆) G ⨟ Term.listF (Term.starRepair B G)) ⨟
            (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n)))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟
          (Term.starQ B G ⨟ Term.unspref B G)) := PEq.compR _ (star_square B G)
    _ ≡ₜ (((Term.listF (Term.starAnn B G) ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟
          Term.starQ B G) ⨟ Term.unspref B G) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.listF (Term.starAnn B G) ⨟
          (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ Term.starQ B G)) ⨟ Term.unspref B G) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)

end Lax149335Proofs

bridge_export Lax149335Proofs
