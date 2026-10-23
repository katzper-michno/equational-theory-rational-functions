import Lax149335Proofs.Appendix.Bundles.BundleTwo
import Lax149335Proofs.SimpleCompleteness.BundleRetract

/-!
# The window axiom and the proof of the bundle lemma (appendix, *Proof of Lemma 6.7*)

This file completes the proof of the bundle lemma (Lemma 6.7) from Axiom 16, the window
axiom `Lax149335Proofs.PEq.window`, which says that the concatenation map of bundles of size two

`(2* × 2*)* × (1 + 2*) ↣ (2*)*`

over the type `2*` of binary strings is surjective.  It follows the last part of the
appendix:

* **Injective representation in a binary alphabet (Lemma 5.6).**  Every type has an
  injective aperiodic encoding into the type `2*` of binary strings
  (`Lax149335Proofs.exists_injective_binary_encoding`).  The construction encodes a type into
  strings over some finite alphabet `Ā` (Claim F.1), encodes each letter of `Ā` as a block
  of `2^i` bits, and concatenates the blocks (Claim F.2); the last step is provably injective
  because the concatenation map of a list of blocks of a fixed length is
  (`Lax149335Proofs.powList_concatMap_injective`), which is a consequence of the injectivity half
  of the bundle lemma proved in `Lax149335Proofs.Appendix.Bundles.BundleTwo`.
* **Surjectivity.**  Over binary strings, the injectivity half and the window axiom give the
  bundle lemma for the bundle size two (`Lax149335Proofs.bundle_two_iso_bin`); by naturality it
  transfers along retracts of the parameter, hence holds for every type
  (`Lax149335Proofs.BundleTwo.bundle_two_iso`).
* **Induction.**  Taking bundles of bundles (`Lax149335Proofs.BundleIso.mul`) the bundle lemma
  holds for all the bundle sizes `2^i`, in particular for arbitrarily large bundle sizes,
  which is the statement of Lemma 6.7 used in the proof of Lemma 6.1
  (`Lax149335Proofs.concatMap_bundle_iso_arbitrarily_large'`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Two elementary provable injectivities -/

/-- Every value is provably injective, since every term into the unit type is a retraction
of it. -/
theorem ProvablyInjective.of_value {A : Ty} (v : Value A) : ProvablyInjective v :=
  ⟨toUnit A, PEq.unit_unique _ _⟩

/-- The inverse of distributivity on the left is provably injective. -/
theorem ProvablyInjective.undistL (A B C : Ty) : ProvablyInjective (Term.undistL A B C) :=
  ⟨Term.distL A B C, PEq.undistL_distL A B C⟩

/-! ### Encoding a finite alphabet in blocks of bits -/

/-- **Every finite alphabet embeds provably injectively into a block of bits.**  The `n+1`
letters of `finAlph n` are encoded by `k` bits, for some `k`; the encoding of the `i`-th
letter is the `i`-th co-projection of `2^k`, viewed as an iterated left distribution. -/
theorem exists_finAlph_bits : (n : ℕ) →
    ∃ (k : ℕ) (e : Term (Ty.finAlph n) ((TyF.pow k).app (Ty.finAlph 1))),
      IsAperiodic e ∧ ProvablyInjective e
  | 0 => ⟨0, Term.id Ty.unit, rfl, ProvablyInjective.id _⟩
  | (n + 1) => by
      obtain ⟨k, e, hea, he⟩ := exists_finAlph_bits n
      refine ⟨k + 1,
        Term.sumF (Term.defaultValue (Ty.unit ⊗ (TyF.pow k).app (Ty.finAlph 1)))
            (e ⨟ Term.unitL ((TyF.pow k).app (Ty.finAlph 1))) ⨟
          Term.undistL Ty.unit Ty.unit ((TyF.pow k).app (Ty.finAlph 1)), ?_, ?_⟩
      · have hd := Term.aperiodic_defaultValue (Ty.unit ⊗ (TyF.pow k).app (Ty.finAlph 1))
        simp only [IsAperiodic] at hea hd ⊢
        simp [Term.usesPref, Term.undistL, Term.either, hea, hd]
      exact ProvablyInjective.comp
        (ProvablyInjective.sumF (ProvablyInjective.of_value _)
          (ProvablyInjective.comp he (ProvablyInjective.unitL _)))
        (ProvablyInjective.undistL Ty.unit Ty.unit _)

/-- A block of `k` entries embeds provably injectively into a block of `K` entries whenever
`k ≤ K`: the missing entries are filled with a default value. -/
theorem exists_pow_pad (A : Ty) : (K k : ℕ) → k ≤ K →
    ∃ p : Term ((TyF.pow k).app A) ((TyF.pow K).app A), IsAperiodic p ∧ ProvablyInjective p
  | 0, k, hk => by
      have : k = 0 := Nat.le_zero.1 hk
      subst this
      exact ⟨Term.id Ty.unit, rfl, ProvablyInjective.id _⟩
  | (K + 1), k, hk => by
      rcases Nat.eq_or_lt_of_le hk with h | h
      · subst h
        exact ⟨Term.id _, rfl, ProvablyInjective.id _⟩
      · obtain ⟨p, hpa, hp⟩ := exists_pow_pad A K k (by omega)
        refine ⟨p ⨟ Term.pairL (Term.defaultValue A) (Term.id ((TyF.pow K).app A)), ?_,
          ProvablyInjective.comp hp
            (ProvablyInjective.pairL _ _ (ProvablyInjective.id _))⟩
        have hd := Term.aperiodic_defaultValue A
        simp only [IsAperiodic] at hpa hd ⊢
        simp [Term.usesPref, Term.pairL, hpa, hd]

/-! ### The concatenation map of a list of blocks of a fixed length -/

/-- The value of `A^{<k+1}` given by the empty block. -/
def ltNilValue : (k : ℕ) → (A : Ty) → Value ((TyF.lt k).app A)
  | 0, _ => Term.id Ty.unit
  | (k + 1), A =>
      ltNilValue k A ⨟ Term.inl ((TyF.lt k).app A) ((TyF.pow (k + 1)).app A)

/-- The empty block is the empty list. -/
theorem ltNilValue_concatMap : (k : ℕ) → (A : Ty) →
    (ltNilValue k A ⨟ TyF.concatMap (TyF.lt k) A) ≡ₜ nilT A
  | 0, A => PEq.id_comp (nilT A)
  | (k + 1), A => by
      show ((ltNilValue k A ⨟ Term.inl _ _) ⨟
        either (TyF.concatMap (TyF.lt k) A) (TyF.concatMap (TyF.pow (k + 1)) A)) ≡ₜ nilT A
      calc ((ltNilValue k A ⨟ Term.inl _ _) ⨟
            either (TyF.concatMap (TyF.lt k) A) (TyF.concatMap (TyF.pow (k + 1)) A))
          ≡ₜ (ltNilValue k A ⨟ (Term.inl _ _ ⨟
              either (TyF.concatMap (TyF.lt k) A) (TyF.concatMap (TyF.pow (k + 1)) A))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (ltNilValue k A ⨟ TyF.concatMap (TyF.lt k) A) :=
            PEq.compR _ (Term.inl_either _ _)
        _ ≡ₜ nilT A := ltNilValue_concatMap k A

/-- **The concatenation map of a list of blocks of a fixed length is provably injective.**
It is the bundle concatenation map precomposed with the pairing with the empty remainder, so
the injectivity half of the bundle lemma applies. -/
theorem powList_concatMap_injective {k : ℕ} (h : BundleInj k) (A : Ty) :
    ProvablyInjective (TyF.concatMap (.list (TyF.pow (k + 1))) A) := by
  set L : Term ((TyF.pow (k + 1)).app A)⋆ A⋆ :=
    TyF.concatMap (.list (TyF.pow (k + 1))) A
  set s : Term ((TyF.pow (k + 1)).app A)⋆ ((TyF.bundle k).app A) :=
    Term.pairR (Term.id ((TyF.pow (k + 1)).app A)⋆) (ltNilValue k A)
  have hstep : (s ⨟ TyF.concatMap (TyF.bundle k) A) ≡ₜ L := by
    calc (s ⨟ TyF.concatMap (TyF.bundle k) A)
        ≡ₜ ((Term.pairR (Term.id _) (ltNilValue k A) ⨟
              Term.prodF L (TyF.concatMap (TyF.lt k) A)) ⨟ binconcat A) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.pairR (Term.id _ ⨟ L)
              (ltNilValue k A ⨟ TyF.concatMap (TyF.lt k) A) ⨟ binconcat A) :=
          PEq.compL _ (Term.pairR_prodF _ _ _ _)
      _ ≡ₜ (Term.pairR L (nilT A) ⨟ binconcat A) :=
          PEq.compL _ (Term.pairR_congr (PEq.id_comp _) (ltNilValue_concatMap k A))
      _ ≡ₜ L := Term.dotR_nil L
  exact ProvablyInjective.of_peq (PEq.symm hstep)
    (ProvablyInjective.comp
      (ProvablyInjective.pairR _ _ (ProvablyInjective.id _)) (h A))

/-! ### Injective representation in a binary alphabet -/

/-- Concatenation maps do not use the prefix multiplication of groups. -/
theorem TyF.concatMap_aperiodic : (F : TyF) → (A : Ty) → IsAperiodic (F.concatMap A)
  | .param, _ => rfl
  | .unit, _ => rfl
  | .prod F G, A => by
      have hF := TyF.concatMap_aperiodic F A
      have hG := TyF.concatMap_aperiodic G A
      simp only [IsAperiodic] at hF hG ⊢
      simp [TyF.concatMap, Term.fdot, Term.binconcat, Term.pureT, Term.prepend, Term.nilT,
        Term.usesPref, hF, hG]
  | .sum F G, A => by
      have hF := TyF.concatMap_aperiodic F A
      have hG := TyF.concatMap_aperiodic G A
      simp only [IsAperiodic] at hF hG ⊢
      simp [TyF.concatMap, Term.either, Term.usesPref, hF, hG]
  | .list F, A => by
      have hF := TyF.concatMap_aperiodic F A
      simp only [IsAperiodic] at hF ⊢
      simp [TyF.concatMap, Term.homT, Term.usesPref, hF]

/-- **Claim F.2.**  For every finite alphabet `N` there is an injective aperiodic term
`N* → (1 + 1)*`.  Each letter of `N` is encoded by a block of `2^i` bits, and the blocks are
concatenated; the concatenation is provably injective by
`Lax149335Proofs.powList_concatMap_injective`. -/
theorem exists_injective_binary_of_finAlph (n : ℕ) :
    ∃ t : Term (Ty.finAlph n)⋆ (Ty.finAlph 1)⋆, IsAperiodic t ∧ ProvablyInjective t := by
  obtain ⟨k, e, hea, he⟩ := exists_finAlph_bits n
  -- the block length is taken to be a power of two, so that the injectivity half of the
  -- bundle lemma is available for it
  obtain ⟨p, hpa, hp⟩ := exists_pow_pad (Ty.finAlph 1) (2 ^ (k + 1) - 1 + 1) k (by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega)
  refine ⟨Term.listF (e ⨟ p) ⨟
    TyF.concatMap (.list (TyF.pow (2 ^ (k + 1) - 1 + 1))) (Ty.finAlph 1), ?_, ?_⟩
  · have hc := TyF.concatMap_aperiodic (.list (TyF.pow (2 ^ (k + 1) - 1 + 1))) (Ty.finAlph 1)
    simp only [IsAperiodic] at hea hpa hc ⊢
    simp [Term.usesPref, hea, hpa, hc]
  exact ProvablyInjective.comp (ProvablyInjective.listF (ProvablyInjective.comp he hp))
    (powList_concatMap_injective (BundleTwo.bundle_two_pow_injective k) (Ty.finAlph 1))

/-- **Lemma 5.6.**  For every type `A` there is an injective aperiodic term
`enc_A : A → (1 + 1)*`.  As in the appendix, it is the composition of the encoding into
strings over a finite alphabet (Claim F.1, `Lax149335Proofs.exists_injective_encoding`) with the
encoding of a finite alphabet into binary strings (Claim F.2,
`Lax149335Proofs.exists_injective_binary_of_finAlph`). -/
theorem exists_injective_binary_encoding (A : Ty) :
    ∃ enc : Term A (Ty.finAlph 1)⋆, IsAperiodic enc ∧ ProvablyInjective enc := by
  obtain ⟨n, enc, hencA, henc⟩ := exists_injective_encoding A
  obtain ⟨t, hta, ht⟩ := exists_injective_binary_of_finAlph n
  refine ⟨enc ⨟ t, ?_, ProvablyInjective.comp henc ht⟩
  simp only [IsAperiodic] at hencA hta ⊢
  simp [Term.usesPref, hencA, hta]

/-! ### From the shape of the window axiom to the internal shape of bundles -/

/-- The rebracketing `(A × A)* × (1 + A) → (A × (A × 1))* × (1 + A × 1)` from the shape of the
window axiom (Definition H.5 and Axiom 16) to the shape `TyF.bundle 1` in which bundles of
size two are represented internally, where `A²` is `A × (A × 1)`. -/
def windowToBundle (A : Ty) : Term (TyF.window.app A) ((TyF.bundle 1).app A) :=
  Term.prodF (Term.listF (Term.prodF (Term.id A) (Term.unitR A)))
    (Term.sumF (Term.id Ty.unit) (Term.unitR A))

/-- `(id,1) ; (pure ⊙ []) ≡ pure`: appending the empty list to a singleton. -/
theorem unitR_pure_fdot_nil (A : Ty) :
    (Term.unitR A ⨟ (pureT A ⊙ nilT A)) ≡ₜ pureT A :=
  PEq.trans (PEq.symm (PEq.comp_assoc _ _ _)) (Term.dotR_nil (pureT A))

/-- **The rebracketing commutes with the two concatenation maps**, provably. -/
theorem windowToBundle_concatMap (A : Ty) :
    (windowToBundle A ⨟ TyF.concatMap (TyF.bundle 1) A) ≡ₜ TyF.concatMap TyF.window A := by
  -- the pairs: `(id × (id,1)) ; (pure ⊙ (pure ⊙ [])) ≡ pure ⊙ pure`
  have hpair : (Term.prodF (Term.id A) (Term.unitR A) ⨟ (pureT A ⊙ (pureT A ⊙ nilT A)))
      ≡ₜ (pureT A ⊙ pureT A) :=
    calc (Term.prodF (Term.id A) (Term.unitR A) ⨟
            (Term.prodF (pureT A) (pureT A ⊙ nilT A) ⨟ binconcat A))
        ≡ₜ ((Term.prodF (Term.id A) (Term.unitR A) ⨟
              Term.prodF (pureT A) (pureT A ⊙ nilT A)) ⨟ binconcat A) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.prodF (Term.id A ⨟ pureT A) (Term.unitR A ⨟ (pureT A ⊙ nilT A)) ⨟
              binconcat A) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (Term.prodF (pureT A) (pureT A) ⨟ binconcat A) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (unitR_pure_fdot_nil A))
  -- the list of pairs: `(id × (id,1))* ; hom (pure ⊙ (pure ⊙ [])) ≡ hom (pure ⊙ pure)`
  have hlist : (Term.listF (Term.prodF (Term.id A) (Term.unitR A)) ⨟
        homT (pureT A ⊙ (pureT A ⊙ nilT A))) ≡ₜ homT (pureT A ⊙ pureT A) :=
    calc (Term.listF (Term.prodF (Term.id A) (Term.unitR A)) ⨟
            (Term.listF (pureT A ⊙ (pureT A ⊙ nilT A)) ⨟ concat A))
        ≡ₜ ((Term.listF (Term.prodF (Term.id A) (Term.unitR A)) ⨟
              Term.listF (pureT A ⊙ (pureT A ⊙ nilT A))) ⨟ concat A) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.listF (Term.prodF (Term.id A) (Term.unitR A) ⨟
              (pureT A ⊙ (pureT A ⊙ nilT A))) ⨟ concat A) :=
          PEq.compL _ (PEq.list_comp _ _)
      _ ≡ₜ homT (pureT A ⊙ pureT A) := homT_congr hpair
  -- the remainder: `(id + (id,1)) ; either [] (pure ⊙ []) ≡ either [] pure`
  have hrest : (Term.sumF (Term.id Ty.unit) (Term.unitR A) ⨟
        either (nilT A) (pureT A ⊙ nilT A)) ≡ₜ either (nilT A) (pureT A) :=
    PEq.trans (Term.sumF_either _ _ _ _)
      (either_congr (PEq.id_comp _) (unitR_pure_fdot_nil A))
  calc (windowToBundle A ⨟
          (Term.prodF (homT (pureT A ⊙ (pureT A ⊙ nilT A))) (either (nilT A) (pureT A ⊙ nilT A)) ⨟
            binconcat A))
      ≡ₜ ((windowToBundle A ⨟
            Term.prodF (homT (pureT A ⊙ (pureT A ⊙ nilT A)))
              (either (nilT A) (pureT A ⊙ nilT A))) ⨟ binconcat A) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.prodF
            (Term.listF (Term.prodF (Term.id A) (Term.unitR A)) ⨟
              homT (pureT A ⊙ (pureT A ⊙ nilT A)))
            (Term.sumF (Term.id Ty.unit) (Term.unitR A) ⨟
              either (nilT A) (pureT A ⊙ nilT A)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.prodF (homT (pureT A ⊙ pureT A)) (either (nilT A) (pureT A)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.congr_prodF hlist hrest)

/-! ### The bundle lemma -/

/-- **The bundle lemma for the bundle size two over binary strings.**  The injectivity half
is `Lax149335Proofs.BundleTwo.bundleInj_one`, and the surjectivity half is Axiom 16: the bundle term
of Definition H.5, followed by the rebracketing into the internal shape of bundles, is a
one-sided inverse of the concatenation map.  The one-sided inverse coming from injectivity is
then provably equal to it, hence a two-sided inverse. -/
theorem bundle_two_iso_bin :
    ProvableIso (TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆) := by
  obtain ⟨f, hf⟩ := BundleTwo.bundleInj_one (Ty.finAlph 1)⋆
  refine ⟨f, hf, ?_⟩
  -- the bundle term of the window axiom, in the internal shape of bundles of size two
  have hwc : ((Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
        windowToBundle (Ty.finAlph 1)⋆) ⨟ TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆)
      ≡ₜ Term.id (((Ty.finAlph 1)⋆)⋆) :=
    calc ((Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
            windowToBundle (Ty.finAlph 1)⋆) ⨟ TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆)
        ≡ₜ (Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
            (windowToBundle (Ty.finAlph 1)⋆ ⨟ TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆)) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
            TyF.concatMap TyF.window (Ty.finAlph 1)⋆) :=
          PEq.compR _ (windowToBundle_concatMap _)
      _ ≡ₜ Term.id (((Ty.finAlph 1)⋆)⋆) := PEq.window
  have hfw : f ≡ₜ (Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
      windowToBundle (Ty.finAlph 1)⋆) :=
    calc f ≡ₜ (Term.id _ ⨟ f) := PEq.symm (PEq.id_comp f)
      _ ≡ₜ (((Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
              windowToBundle (Ty.finAlph 1)⋆) ⨟
            TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆) ⨟ f) := PEq.compL f (PEq.symm hwc)
      _ ≡ₜ ((Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
              windowToBundle (Ty.finAlph 1)⋆) ⨟
            (TyF.concatMap (TyF.bundle 1) (Ty.finAlph 1)⋆ ⨟ f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
              windowToBundle (Ty.finAlph 1)⋆) ⨟ Term.id _) := PEq.compR _ hf
      _ ≡ₜ (Term.bundle (Ty.finAlph 1)⋆ (nilT (Ty.finAlph 1)) ⨟
              windowToBundle (Ty.finAlph 1)⋆) := PEq.comp_id _
  exact PEq.trans (PEq.compL _ hfw) hwc

/-- **The bundle lemma for the bundle size two**, for every type: the concatenation map
`(A²)* × A^{<2} ↣ A*` is a provable isomorphism.  Every type is a retract of the binary
strings, and the concatenation map is natural, so the case of binary strings implies the
general one.  The binary encodings are those of Lemma 5.6, taken as the hypothesis
`h56`. -/
theorem BundleTwo.bundle_two_iso_of
    (h56 : type_of% @Lax149335.StringRepresentations.exists_injective_binary_encoding) :
    BundleIso 1 := by
  intro A
  obtain ⟨enc, -, dec, hdec⟩ := h56 A
  exact concatMap_provableIso_of_retract (TyF.bundle 1) enc dec hdec bundle_two_iso_bin

/-- **Lemma 6.7 (the bundle lemma).**  For arbitrarily large bundle sizes `k+1` — namely for
all the powers of two — and for every type `A`, the concatenation map

`(A^{k+1})* × A^{<k+1} ↣ A*`

is a provable isomorphism.  This is the form of the lemma that the proof of Lemma 6.1 uses.

The bundle sizes cannot all be reached by this argument: the window axiom provides the
bundle size two, and bundles of bundles multiply the bundle sizes.

Lemma 5.6 is taken as the hypothesis `h56`. -/
theorem concatMap_bundle_iso_arbitrarily_large'_of
    (h56 : type_of% @Lax149335.StringRepresentations.exists_injective_binary_encoding)
    (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∀ A : Ty,
      ProvableIso (TyF.concatMap (.prod (.list (TyF.pow (k + 1))) (TyF.lt k)) A) :=
  BundleIso.arbitrarily_large (BundleTwo.bundle_two_iso_of h56) N

/-- **Lemma 6.7 (the bundle lemma).** -/
theorem concatMap_bundle_iso_arbitrarily_large' (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∀ A : Ty,
      ProvableIso (TyF.concatMap (.prod (.list (TyF.pow (k + 1))) (TyF.lt k)) A) :=
  concatMap_bundle_iso_arbitrarily_large'_of exists_injective_binary_encoding N

end Lax149335Proofs

bridge_export Lax149335Proofs
