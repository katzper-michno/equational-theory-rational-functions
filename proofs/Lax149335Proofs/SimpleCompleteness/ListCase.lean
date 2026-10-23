import Lax149335Proofs.SimpleCompleteness.Blocks
import Lax149335Proofs.SimpleCompleteness.EmptySplitTree

/-!
# The list case of value extraction

The hardest case of the value extraction lemma is the one of a list input type `A₁*`, where
the two terms are homomorphisms `hom h` and `hom h'`.  After the empty summands of the input
type `A₁` have been separated (`Lax149335Proofs.JointCasesD.toSplitCopair`), the two terms are
homomorphisms of co-pairings `nilCase B E F` that erase the summand `E` and are matching
co-pairings of `k`-guarded terms with nonempty outputs on `N`.

Such a homomorphism is decomposed by *peeling*: the input list is split into a first run of
`k` blocks, a middle part, and a last run of `k` blocks.  The first run provides a value of
length at least `k` in front of the middle part, the last run one behind it, so the middle
part is equationally `k`-guarded.  The runs are peeled one block at a time by
`Lax149335Proofs.unpeelL` and `Lax149335Proofs.unpeelR`, and the two phases of the peeling are the two
theorems `Lax149335Proofs.leftPhase` and `Lax149335Proofs.rightPhase` of this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {B : Ty}

section Peel

variable {k D : ℕ} {E N : Ty}

/-- The right phase of the peeling: `k` blocks have already been accumulated on the left, and
`i` of the `k` blocks on the right. -/
theorem rightPhase (hE : E.listDepth ≤ D) (hN : N.listDepth ≤ D)
    {F F' : Term N B⋆} (hK : KCopair2 k B F F') :
    ∀ (fuel i : ℕ), k ≤ i + fuel →
      ∀ (W₁ : Ty), W₁.listDepth ≤ D + 1 → ∀ (a a' : Term W₁ B⋆),
        PrefixOK k B k a → PrefixOK k B k a' →
      ∀ (W₂ : Ty), W₂.listDepth ≤ D + 1 → ∀ (b b' : Term W₂ B⋆),
        SuffixOK k B i b → SuffixOK k B i b' →
        JointCasesD B (KGuardedPair k B) (D + 1)
          ((a ⊙ homT (nilCase B E F)) ⊙ b) ((a' ⊙ homT (nilCase B E F')) ⊙ b') := by
  have hSF : EqSimple B (homT (nilCase B E F)) :=
    EqSimple.hom (EqSimple.either (EqSimple.nilconst E B) hK.eqSimple_left)
  have hSF' : EqSimple B (homT (nilCase B E F')) :=
    EqSimple.hom (EqSimple.either (EqSimple.nilconst E B) hK.eqSimple_right)
  have hnilKG : ∀ X : Ty, KGuardedE k B (nilconst B X) := fun _ => Or.inl ⟨nilT B, PEq.refl _⟩
  intro fuel
  induction fuel with
  | zero =>
      intro i hki W₁ hW₁ a a' ha ha' W₂ hW₂ b b' hb hb'
      have hik : k ≤ i := by omega
      refine JointCasesD.leaf ?_ ⟨kguardedE_of_prefix_suffix ha hSF (SuffixOK.mono hik hb),
        kguardedE_of_prefix_suffix ha' hSF' (SuffixOK.mono hik hb')⟩
      simp only [Ty.listDepth, max_le_iff] at hW₁ hW₂ hE hN ⊢
      omega
  | succ fuel ih =>
      intro i hki W₁ hW₁ a a' ha ha' W₂ hW₂ b b' hb hb'
      by_cases hik : k ≤ i
      · refine JointCasesD.leaf ?_ ⟨kguardedE_of_prefix_suffix ha hSF (SuffixOK.mono hik hb),
          kguardedE_of_prefix_suffix ha' hSF' (SuffixOK.mono hik hb')⟩
        simp only [Ty.listDepth, max_le_iff] at hW₁ hW₂ hE hN ⊢
        omega
      refine JointCasesD.ctx_peel a a' b b' (provableIso_unpeelR E N)
        (unpeelR_homT F) (unpeelR_homT F') ?_ ?_
      · -- the list has no more blocks
        refine JointCasesD.leaf ?_
          ⟨KGuardedE.fdot (KGuardedE.fdot ha.1 (hnilKG _)) hb.1,
            KGuardedE.fdot (KGuardedE.fdot ha'.1 (hnilKG _)) hb'.1⟩
        simp only [Ty.listDepth, max_le_iff] at hW₁ hW₂ hE ⊢
        omega
      · -- one more block is peeled off on the right
        refine JointCasesD.transportIso (provableIso_rebr4 W₁ ((E ⊕' N)⋆) (N ⊗ E⋆) W₂)
          (rebr4_fdot a (homT (nilCase B E F)) (blockR B E F) b)
          (rebr4_fdot a' (homT (nilCase B E F')) (blockR B E F') b') ?_
        have jF : JointCasesD B (fun {Y} (T S : Term Y B⋆) => KGuarded k B T ∧
            KGuarded k B S ∧ NonemptyOutput T ∧ NonemptyOutput S) D F F' :=
          JointCasesD.mono_d hN (KCopair2.toJointCasesD hK)
        have jBR : JointCasesD B (fun {Y} (T S : Term Y B⋆) =>
            SuffixOK k B 1 T ∧ SuffixOK k B 1 S) (D + 1)
            (F ⊙ nilconst B E⋆) (F' ⊙ nilconst B E⋆) := by
          refine JointCasesD.fdot_right (nilconst B E⋆) (nilconst B E⋆)
            (fun {Y} T S hY hP => JointCasesD.leaf ?_
              ⟨suffixOK_fdot_nilconst (suffixOK_of_kguarded hP.1 hP.2.2.1),
                suffixOK_fdot_nilconst (suffixOK_of_kguarded hP.2.1 hP.2.2.2)⟩) jF
          simp only [Ty.listDepth, max_le_iff] at hE ⊢
          omega
        have jRB : JointCasesD B (fun {Y} (T S : Term Y B⋆) =>
            SuffixOK k B (i + 1) T ∧ SuffixOK k B (i + 1) S) (D + 1)
            ((F ⊙ nilconst B E⋆) ⊙ b) ((F' ⊙ nilconst B E⋆) ⊙ b') := by
          refine JointCasesD.fdot_right b b'
            (fun {Y} T S hY hP => JointCasesD.leaf ?_
              ⟨suffixOK_fdot hP.1 hb, suffixOK_fdot hP.2 hb'⟩) jBR
          simp only [Ty.listDepth, max_le_iff] at hW₂ hY ⊢
          omega
        refine JointCasesD.fdot_left (a ⊙ homT (nilCase B E F)) (a' ⊙ homT (nilCase B E F'))
          (fun {Y} T S hY hP => ih (i + 1) (by omega) W₁ hW₁ a a' ha ha' Y hY T S hP.1 hP.2)
          jRB

/-- The left phase of the peeling: `n` blocks have been accumulated on the left. -/
theorem leftPhase (hE : E.listDepth ≤ D) (hN : N.listDepth ≤ D)
    {F F' : Term N B⋆} (hK : KCopair2 k B F F') :
    ∀ (fuel n : ℕ), k ≤ n + fuel →
      ∀ (W₁ : Ty), W₁.listDepth ≤ D + 1 → ∀ (a a' : Term W₁ B⋆),
        PrefixOK k B n a → PrefixOK k B n a' →
        JointCasesD B (KGuardedPair k B) (D + 1)
          (a ⊙ homT (nilCase B E F)) (a' ⊙ homT (nilCase B E F')) := by
  have hnilKG : ∀ X : Ty, KGuardedE k B (nilconst B X) := fun _ => Or.inl ⟨nilT B, PEq.refl _⟩
  intro fuel
  induction fuel with
  | zero =>
      intro n hkn W₁ hW₁ a a' ha ha'
      have hnk : k ≤ n := by omega
      refine JointCasesD.transportIso (ProvableIso.fst_unit (W₁ ⊗ (E ⊕' N)⋆))
        (PEq.symm (Term.prodF_nilconst_binconcat (a ⊙ homT (nilCase B E F))))
        (PEq.symm (Term.prodF_nilconst_binconcat (a' ⊙ homT (nilCase B E F')))) ?_
      exact rightPhase hE hN hK k 0 (by omega) W₁ hW₁ a a'
        (PrefixOK.mono hnk ha) (PrefixOK.mono hnk ha') Ty.unit (by simp [Ty.listDepth])
        (nilconst B Ty.unit) (nilconst B Ty.unit)
        (suffixOK_nilconst k B Ty.unit) (suffixOK_nilconst k B Ty.unit)
  | succ fuel ih =>
      intro n hkn W₁ hW₁ a a' ha ha'
      by_cases hnk : k ≤ n
      · refine JointCasesD.transportIso (ProvableIso.fst_unit (W₁ ⊗ (E ⊕' N)⋆))
          (PEq.symm (Term.prodF_nilconst_binconcat (a ⊙ homT (nilCase B E F))))
          (PEq.symm (Term.prodF_nilconst_binconcat (a' ⊙ homT (nilCase B E F')))) ?_
        exact rightPhase hE hN hK k 0 (by omega) W₁ hW₁ a a'
          (PrefixOK.mono hnk ha) (PrefixOK.mono hnk ha') Ty.unit (by simp [Ty.listDepth])
          (nilconst B Ty.unit) (nilconst B Ty.unit)
          (suffixOK_nilconst k B Ty.unit) (suffixOK_nilconst k B Ty.unit)
      refine JointCasesD.ctx_peelL a a' (provableIso_unpeelL E N)
        (unpeelL_homT F) (unpeelL_homT F') ?_ ?_
      · -- the list has no more blocks
        refine JointCasesD.leaf ?_
          ⟨KGuardedE.fdot ha.1 (hnilKG _), KGuardedE.fdot ha'.1 (hnilKG _)⟩
        simp only [Ty.listDepth, max_le_iff] at hW₁ hE ⊢
        omega
      · -- one more block is peeled off on the left
        refine JointCasesD.transportIso (ProvableIso.assocR W₁ (E⋆ ⊗ N) ((E ⊕' N)⋆))
          (PEq.symm (Term.fdot_assoc a (blockL B E F) (homT (nilCase B E F))))
          (PEq.symm (Term.fdot_assoc a' (blockL B E F') (homT (nilCase B E F')))) ?_
        have jF : JointCasesD B (fun {Y} (T S : Term Y B⋆) => KGuarded k B T ∧
            KGuarded k B S ∧ NonemptyOutput T ∧ NonemptyOutput S) D F F' :=
          JointCasesD.mono_d hN (KCopair2.toJointCasesD hK)
        have jBL : JointCasesD B (fun {Y} (T S : Term Y B⋆) =>
            PrefixOK k B 1 T ∧ PrefixOK k B 1 S) (D + 1)
            (nilconst B E⋆ ⊙ F) (nilconst B E⋆ ⊙ F') := by
          refine JointCasesD.fdot_left (nilconst B E⋆) (nilconst B E⋆)
            (fun {Y} T S hY hP => JointCasesD.leaf ?_
              ⟨prefixOK_nilconst_fdot (prefixOK_of_kguarded hP.1 hP.2.2.1),
                prefixOK_nilconst_fdot (prefixOK_of_kguarded hP.2.1 hP.2.2.2)⟩) jF
          simp only [Ty.listDepth, max_le_iff] at hE ⊢
          omega
        have jAL : JointCasesD B (fun {Y} (T S : Term Y B⋆) =>
            PrefixOK k B (n + 1) T ∧ PrefixOK k B (n + 1) S) (D + 1)
            (a ⊙ (nilconst B E⋆ ⊙ F)) (a' ⊙ (nilconst B E⋆ ⊙ F')) := by
          refine JointCasesD.fdot_left a a'
            (fun {Y} T S hY hP => JointCasesD.leaf ?_
              ⟨prefixOK_fdot ha hP.1, prefixOK_fdot ha' hP.2⟩) jBL
          simp only [Ty.listDepth, max_le_iff] at hW₁ hY ⊢
          omega
        refine JointCasesD.fdot_right (homT (nilCase B E F)) (homT (nilCase B E F'))
          (fun {Y} T S hY hP => ih (n + 1) (by omega) Y hY T S hP.1 hP.2) jAL

/-- **The homomorphism of a co-pairing that erases one summand** decomposes jointly into
equationally `k`-guarded components of small list nesting depth. -/
theorem homT_nilCase_jointCases (hE : E.listDepth ≤ D) (hN : N.listDepth ≤ D)
    {F F' : Term N B⋆} (hK : KCopair2 k B F F') :
    JointCasesD B (KGuardedPair k B) (D + 1)
      (homT (nilCase B E F)) (homT (nilCase B E F')) := by
  refine JointCasesD.transportIso (ProvableIso.snd_unit ((E ⊕' N)⋆))
    (PEq.symm (Term.prodF_nilconst_binconcat_left (homT (nilCase B E F))))
    (PEq.symm (Term.prodF_nilconst_binconcat_left (homT (nilCase B E F')))) ?_
  exact leftPhase hE hN hK k 0 (by omega) Ty.unit (by simp [Ty.listDepth])
    (nilconst B Ty.unit) (nilconst B Ty.unit)
    (prefixOK_nilconst k B Ty.unit) (prefixOK_nilconst k B Ty.unit)

end Peel

/-- **The homomorphism of a matching pair of co-pairings of `k`-guarded terms with nonempty
outputs** decomposes jointly into equationally `k`-guarded components: this is the bundle
decomposition of the appendix. -/
theorem homT_copair_jointCases {k D : ℕ} (hk : 0 < k) {N : Ty} (hN : N.listDepth ≤ D)
    {F F' : Term N B⋆} (hK : KCopair2 k B F F') :
    JointCasesD B (KGuardedPair k B) (D + 1) (homT F) (homT F') := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine JointCasesD.transportIso (Term.concatMap_fixedShape_iso N m)
    (Term.TyF.concatMap_homT _ F) (Term.TyF.concatMap_homT _ F') ?_
  refine JointCasesD.mono_d ?_ (JointCasesD.of_jointCases (jointCases_fixedMap hK))
  exact le_trans (fixedShape_app_listDepth N m) (by omega)

/-- **The list case of value extraction.**  If two terms on a type `A₁` decompose jointly into
equationally `k`-guarded components of list nesting depth at most `D` and always produce
outputs of the same length, then their homomorphisms decompose jointly into equationally
`k`-guarded components of list nesting depth at most `D + 1`. -/
theorem homT_jointCases {k D : ℕ} (hk : 0 < k) {A₁ : Ty} {h h' : Term A₁ B⋆}
    (hj : JointCasesD B (fun {Y} (T S : Term Y B⋆) => KGuardedPair k B T S ∧
        ∀ x : ⟦Y⟧, (T.den x).length = (S.den x).length) D h h') :
    JointCasesD B (KGuardedPair k B) (D + 1) (homT h) (homT h') := by
  rcases JointCasesD.toSplitCopair hk hj with
    ⟨Z, rho, hrho, hZ, h1, h2⟩ | ⟨E, N, rho, hrho, hE, hN, F, F', hK, h1, h2⟩
  · -- both terms are the empty constant, and so are their homomorphisms
    refine JointCasesD.transportIso (ProvableIso.listF hrho)
      (PEq.symm (Term.homT_precomp rho h)) (PEq.symm (Term.homT_precomp rho h')) ?_
    refine JointCasesD.leaf ?_ ⟨?_, ?_⟩
    · simp only [Ty.listDepth]; omega
    · exact Or.inl ⟨nilT B, (Term.homT_congr (Term.comp_nilconst_of rho h1)).trans
        (Term.homT_nilconst Z B)⟩
    · exact Or.inl ⟨nilT B, (Term.homT_congr (Term.comp_nilconst_of rho h2)).trans
        (Term.homT_nilconst Z B)⟩
  · -- the input type splits into an empty part and a nonempty part
    refine JointCasesD.transportIso (ProvableIso.listF hrho)
      ((Term.homT_precomp rho h).symm.trans (Term.homT_congr h1))
      ((Term.homT_precomp rho h').symm.trans (Term.homT_congr h2)) ?_
    cases E with
    | none => exact homT_copair_jointCases hk hN hK
    | some E₀ =>
        simp only [optListDepthLe] at hE
        exact homT_nilCase_jointCases hE hN hK

end Lax149335Proofs

bridge_export Lax149335Proofs
