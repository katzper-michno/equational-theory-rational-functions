import Lax149335Proofs.Appendix.Groups.SigmaSemantics
import Lax149335Proofs.Appendix.Groups.UnprefixingSemantics
import Mathlib.Tactic.Group

/-!
# The product case of the consolidation claim (appendix, proof of the group exchange lemma)

The appendix *claim* used in the induction of the last lemma of the completeness proof asks,
for the product case, for a term `δ : T A × T A → T A` making

```
(Σ A)* × (Σ A)*  --concat-->  (Σ A)*
      |                          |
 spref × spref                 spref
      v                          v
   T A × T A     ----δ---->     T A
```

commute provably.  This file constructs such a `δ` explicitly (`Lax149335Proofs.Term.consolProd`),
proves that it is aperiodic, computes its denotation, and proves the aperiodic form of the
claim, in which `spref` has been replaced by its inverse `unspref`
(`Lax149335Proofs.consolProd_unspref`); by Corollary 7.6 the aperiodic diagram only has to be
checked denotationally.

**A weakening of the paper's statement.**  The appendix asks for `δ` to be a *drop*.  The
construction below does not give one: `δ` has to inspect the group annotation of its first
argument, which sits inside a co-product *nested in a product*, and the prime drops of
Table 1 contain no distributivity of a co-product over a product (`distL` and `distR` are
prime *lifts*).  What is obtained is the weaker statement in which `δ` is an *aperiodic*
term, hence — by the lift-drop factorisation of Lemma 7.4 — provably equal to a lift followed
by a drop.  This is what the induction of the appendix actually needs, since a lift in front
of a drop can be absorbed into the grouplift of the factorisation being constructed.

The denotational content is the combinatorial fact that unprefixing distributes over
concatenation (`Lax149335Proofs.Term.unprefDen_append`), together with the fact that unprefixing a
list all of whose group annotations have been multiplied on the left by `g` is the same as
unprefixing the original list (`Lax149335Proofs.Term.unprefDen_map_mul`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Distributing a product over `Σ` on the left -/

/-- Distributing a product over the co-product `Σ`, with the co-product on the left. -/
def distSigmaL (Y X : Ty) : (n : ℕ) → Term ((sigmaTy Y n) ⊗ X) (sigmaTy (Y ⊗ X) n)
  | 0 => Term.id (Y ⊗ X)
  | (n + 1) => distL Y (sigmaTy Y n) X ⨟ sumF (Term.id (Y ⊗ X)) (distSigmaL Y X n)

@[simp] theorem usesPref_distSigmaL (Y X : Ty) : (n : ℕ) → usesPref (distSigmaL Y X n) = false
  | 0 => rfl
  | (n + 1) => by simp [distSigmaL, usesPref, usesPref_distSigmaL Y X n]

@[simp] theorem den_distSigmaL (Y X : Ty) : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) → (y : ⟦Y⟧) →
    (x : ⟦X⟧) →
    (distSigmaL Y X n).den ((injSigma Y g).den y, x) = (injSigma (Y ⊗ X) g).den (y, x)
  | 0, _, _, _ => rfl
  | (n + 1), .inl (), y, x => rfl
  | (n + 1), .inr g, y, x => by
      show (sumF (Term.id (Y ⊗ X)) (distSigmaL Y X n)).den
        ((distL Y (sigmaTy Y n) X).den (Sum.inr ((injSigma Y g).den y), x)) = _
      rw [den_distL_inr]
      show Sum.inr ((distSigmaL Y X n).den ((injSigma Y g).den y, x)) = _
      rw [den_distSigmaL Y X g y x]
      rfl

/-! ### Multiplying the annotation of a `Σ`-value -/

/-- Multiply the group annotation of a value of `Σ A` on the left by a fixed group element. -/
def sigmaMul (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (g : ⟦Ty.finAlph n⟧) :
    Term (sigmaTy A n) (sigmaTy A n) :=
  sigmaCase (fun k => injSigma A (letI := G; g * k))

@[simp] theorem usesPref_sigmaMul (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (g : ⟦Ty.finAlph n⟧) : usesPref (sigmaMul A G g) = false :=
  usesPref_sigmaCase _ (fun _ => usesPref_injSigma A _)

@[simp] theorem den_sigmaMul (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (g k : ⟦Ty.finAlph n⟧) (a : ⟦A⟧) :
    (sigmaMul A G g).den ((injSigma A k).den a) =
      (injSigma A (letI := G; g * k)).den a := by
  simp [sigmaMul]

/-! ### The denotations of `toT` and `fromT` -/

@[simp] theorem den_fromT_inl (A : Ty) (n : ℕ) :
    (fromT A n).den (Sum.inl ()) = ([] : List ⟦sigmaTy A n⟧) := rfl

@[simp] theorem den_fromT_inr (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy A n⟧) (a : ⟦A⟧) :
    (fromT A n).den (Sum.inr ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a))) =
      w ++ [(injSigma A g).den a] := by
  show snocDen ((sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n)).den
    (Sum.inr ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a)))) = _
  show snocDen (Sum.inr ((undistSigmaR ((sigmaTy A n)⋆) A n).den
    ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a)))) = _
  rw [den_undistSigmaR]
  rfl

theorem den_fromT_toT (A : Ty) (n : ℕ) (w : List ⟦sigmaTy A n⟧) :
    (fromT A n).den ((toT A n).den w) = w := by
  have h := congrFun (PEq.sound (toT_fromT A n)) w
  simpa using h

/-! ### The consolidation term for the product case -/

/-- The body of the consolidation term: given the group annotation `g` of the last letter of
the first argument, the last letter `a` and the preceding letters `w` of the first argument,
and the second argument `v`, the result is `w ++ [ι_g a] ++ g·v`. -/
def consolProdBody (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (g : ⟦Ty.finAlph n⟧) :
    Term (((((sigmaTy A n)⋆) ⊗ A)) ⊗ ((sigmaTy A n)⋆)) (tTy A n) :=
  prodF (prodF (Term.id ((sigmaTy A n)⋆)) (injSigma A g ⨟ pureT (sigmaTy A n)))
      (listF (sigmaMul A G g)) ⨟
    (prodF (binconcat (sigmaTy A n)) (Term.id ((sigmaTy A n)⋆)) ⨟
      (binconcat (sigmaTy A n) ⨟ toT A n))

/-- **The consolidation term, product case.**  `δ(x,y)` is the list obtained by concatenating
the list of `x` with the list of `y`, all of whose group annotations are multiplied on the
left by the last annotation of `x`. -/
def consolProd (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((tTy A n) ⊗ (tTy A n)) (tTy A n) :=
  prodF (Term.id (tTy A n)) (fromT A n) ⨟
    (distL Ty.unit (sigmaTy ((((sigmaTy A n)⋆) ⊗ A)) n) ((sigmaTy A n)⋆) ⨟
      either (snd Ty.unit ((sigmaTy A n)⋆) ⨟ toT A n)
        (distSigmaL ((((sigmaTy A n)⋆) ⊗ A)) ((sigmaTy A n)⋆) n ⨟
          sigmaCase (fun g => consolProdBody A G g)))

theorem isAperiodic_consolProd (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    IsAperiodic (consolProd A G) := by
  have hbody : ∀ g : ⟦Ty.finAlph n⟧, usesPref (consolProdBody A G g) = false := by
    intro g
    simp [consolProdBody, usesPref, usesPref_injSigma, pureT, binconcat]
  simp [IsAperiodic, consolProd, usesPref, either, usesPref_sigmaCase _ hbody]

/-! ### The denotation of the consolidation term -/

theorem den_consolProd_inl (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (y : ⟦tTy A n⟧) :
    (consolProd A G).den (Sum.inl (), y) = (toT A n).den ((fromT A n).den y) := rfl

theorem den_consolProd_inr (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (g : ⟦Ty.finAlph n⟧) (w : List ⟦sigmaTy A n⟧) (a : ⟦A⟧) (y : ⟦tTy A n⟧) :
    (consolProd A G).den
        (Sum.inr ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a)), y) =
      (toT A n).den ((w ++ [(injSigma A g).den a]) ++
        ((fromT A n).den y).map (sigmaMul A G g).den) := by
  show (either (snd Ty.unit ((sigmaTy A n)⋆) ⨟ toT A n)
      (distSigmaL ((((sigmaTy A n)⋆) ⊗ A)) ((sigmaTy A n)⋆) n ⨟
        sigmaCase (fun g => consolProdBody A G g))).den
    ((distL Ty.unit (sigmaTy ((((sigmaTy A n)⋆) ⊗ A)) n) ((sigmaTy A n)⋆)).den
      (Sum.inr ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a)), (fromT A n).den y)) = _
  rw [den_distL_inr, den_either]
  show (distSigmaL ((((sigmaTy A n)⋆) ⊗ A)) ((sigmaTy A n)⋆) n ⨟
      sigmaCase (fun g => consolProdBody A G g)).den
    ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a), (fromT A n).den y) = _
  rw [den_comp, den_distSigmaL, den_sigmaCase]
  simp [consolProdBody]

/-! ### Unprefixing a list whose annotations are multiplied by a fixed group element -/

theorem unprefDen_map_mul {α : Type} {G : Type} [Group G] (g : G) :
    ∀ (acc : G) (l : List (α × G)),
      unprefDen (g * acc) (l.map (fun p => (p.1, g * p.2))) = unprefDen acc l
  | _, [] => rfl
  | acc, (a, k) :: t => by
      have h1 : (g * acc)⁻¹ * (g * k) = acc⁻¹ * k := by group
      simp only [List.map_cons, unprefDen_cons, h1]
      rw [unprefDen_map_mul g k t]

/-! ### The denotation of `unspref` at the level of words -/

/-- The word-level form of `unspref`: decode the annotations, unprefix, encode again. -/
noncomputable def unsprefW (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (w : List ⟦sigmaTy A n⟧) : List ⟦sigmaTy A n⟧ :=
  letI := G
  (unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (sigmaDec A n).den)).map (sigmaEnc A n).den

theorem den_unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (t : ⟦tTy A n⟧) :
    (unspref A G).den t = unsprefW A G ((fromT A n).den t) := by
  letI := G
  simp [unspref, unsprefW, den_unpref_fun]

/-- Decoding a list whose annotations have been multiplied by `g` on the left. -/
theorem dec_map_sigmaMul (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (g : ⟦Ty.finAlph n⟧) :
    ∀ v : List ⟦sigmaTy A n⟧,
      (v.map (sigmaMul A G g).den).map (sigmaDec A n).den =
        (v.map (sigmaDec A n).den).map (fun p => (p.1, letI := G; g * p.2))
  | [] => rfl
  | z :: t => by
      obtain ⟨b, k, rfl⟩ := sigma_cases A z
      simp [dec_map_sigmaMul A G g t]

/-- The key computation: unprefixing the concatenation of a word `u` with a word `v` whose
annotations have all been multiplied on the left by the last annotation of `u` is the
concatenation of the unprefixings. -/
theorem unsprefW_append_mul (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (g : ⟦Ty.finAlph n⟧) (u v : List ⟦sigmaTy A n⟧)
    (hu : letI := G; lastAcc (1 : ⟦Ty.finAlph n⟧) (u.map (sigmaDec A n).den) = g) :
    unsprefW A G (u ++ v.map (sigmaMul A G g).den) =
      unsprefW A G u ++ unsprefW A G v := by
  letI := G
  have hmul := unprefDen_map_mul (α := ⟦A⟧) g 1 (v.map (sigmaDec A n).den)
  rw [mul_one] at hmul
  simp only [unsprefW, List.map_append, unprefDen_append, hu, List.map_append]
  rw [dec_map_sigmaMul A G g v]
  congr 1
  exact congrArg (List.map (sigmaEnc A n).den) hmul

/-- The last annotation of a word of the shape `w ++ [ι_g a]` is `g`. -/
theorem lastAcc_dec_append_singleton (A : Ty) {n : ℕ} (w : List ⟦sigmaTy A n⟧)
    (g acc : ⟦Ty.finAlph n⟧) (a : ⟦A⟧) :
    lastAcc acc (((w ++ [(injSigma A g).den a]).map (sigmaDec A n).den)) = g := by
  rw [List.map_append]
  simpa using lastAcc_append_singleton acc (w.map (sigmaDec A n).den) a g

end Term

/-! ### The claim -/

/-- The aperiodic form of the product case of the claim, for the explicit term. -/
theorem den_consolProd_unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (Term.consolProd A G ⨟ unspref A G).den =
      (prodF (unspref A G) (unspref A G) ⨟ binconcat (sigmaTy A n)).den := by
  funext p
  obtain ⟨x, y⟩ := p
  simp only [den_comp, den_prodF, den_binconcat]
  match x with
  | .inl () =>
      rw [Term.den_consolProd_inl, Term.den_unspref, Term.den_fromT_toT, Term.den_unspref,
        Term.den_unspref]
      simp [Term.unsprefW]
  | .inr s =>
      obtain ⟨⟨w, a⟩, g, rfl⟩ := Term.sigma_cases (((sigmaTy A n)⋆) ⊗ A) s
      rw [Term.den_consolProd_inr, Term.den_unspref, Term.den_fromT_toT, Term.den_unspref,
        Term.den_unspref, Term.den_fromT_inr]
      exact Term.unsprefW_append_mul A G g _ _
        (Term.lastAcc_dec_append_singleton A w g _ a)

/-- The aperiodic form of the product case of the claim, provably. -/
theorem consolProd_unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (Term.consolProd A G ⨟ unspref A G) ≡ₜ
      (prodF (unspref A G) (unspref A G) ⨟ binconcat (sigmaTy A n)) := by
  refine completeness_aperiodic _ _ ?_ ?_ (den_consolProd_unspref A G)
  · simp only [IsAperiodic, Term.usesPref, Bool.or_eq_false_iff]
    exact ⟨isAperiodic_consolProd A G, usesPref_unspref A G⟩
  · simp [IsAperiodic, Term.usesPref]

end Lax149335Proofs

bridge_export Lax149335Proofs
