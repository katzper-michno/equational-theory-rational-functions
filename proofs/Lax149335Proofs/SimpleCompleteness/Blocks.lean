import Lax149335Proofs.SimpleCompleteness.PeelIso

/-!
# Products of guarded blocks

The proof of value extraction peels blocks off a list, accumulating a product of `k`-guarded
terms with nonempty outputs on the left and on the right of the remaining list.  Such a
product is not itself `k`-guarded before `k` blocks have been accumulated, but it does have a
constant prefix (respectively suffix) whose length grows with the number of blocks: this is
recorded by the two predicates `Lax149335Proofs.PrefixOK` and `Lax149335Proofs.SuffixOK` of this file.

The file also collects two combinators for joint decompositions that are used by the peeling:
splitting a co-product that occurs in the middle of a concatenation, and re-bracketing a
four-fold concatenation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {B : Ty}

/-! ### Prefixes and suffixes of products of guarded blocks -/

/-- A product of `j` `k`-guarded blocks with nonempty outputs: it is equationally
`k`-guarded, and it is either preceded by a value of length at least `k` or it is itself a
constant of length at least `min j k`. -/
def PrefixOK (k : ℕ) (B : Ty) (j : ℕ) {Y : Ty} (a : Term Y B⋆) : Prop :=
  KGuardedE k B a ∧
    ((∃ (u : Value B⋆) (H : Term Y B⋆), k ≤ valLength u ∧ EqSimple B H ∧
        a ≡ₜ Term.dotL u H) ∨
      (∃ v : Value B⋆, min j k ≤ valLength v ∧ a ≡ₜ (Term.toUnit Y ⨟ v)))

/-- The mirror image of `Lax149335Proofs.PrefixOK`. -/
def SuffixOK (k : ℕ) (B : Ty) (j : ℕ) {Y : Ty} (b : Term Y B⋆) : Prop :=
  KGuardedE k B b ∧
    ((∃ (v : Value B⋆) (H : Term Y B⋆), k ≤ valLength v ∧ EqSimple B H ∧
        b ≡ₜ Term.dotR H v) ∨
      (∃ w : Value B⋆, min j k ≤ valLength w ∧ b ≡ₜ (Term.toUnit Y ⨟ w)))

/-- The empty constant is an empty product of blocks. -/
theorem prefixOK_nilconst (k : ℕ) (B X : Ty) : PrefixOK k B 0 (nilconst B X) :=
  ⟨Or.inl ⟨Term.nilT B, PEq.refl _⟩, Or.inr ⟨Term.nilT B, by simp, PEq.refl _⟩⟩

/-- The empty constant is an empty product of blocks. -/
theorem suffixOK_nilconst (k : ℕ) (B X : Ty) : SuffixOK k B 0 (nilconst B X) :=
  ⟨Or.inl ⟨Term.nilT B, PEq.refl _⟩, Or.inr ⟨Term.nilT B, by simp, PEq.refl _⟩⟩

/-- The number of accumulated blocks can be decreased. -/
theorem PrefixOK.mono {k j j' : ℕ} {Y : Ty} {a : Term Y B⋆} (hj : j ≤ j')
    (ha : PrefixOK k B j' a) : PrefixOK k B j a := by
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with h | ⟨v, hv, hae⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, le_trans (min_le_min hj le_rfl) hv, hae⟩

/-- The number of accumulated blocks can be decreased. -/
theorem SuffixOK.mono {k j j' : ℕ} {Y : Ty} {b : Term Y B⋆} (hj : j ≤ j')
    (hb : SuffixOK k B j' b) : SuffixOK k B j b := by
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with h | ⟨w, hw, hbe⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, le_trans (min_le_min hj le_rfl) hw, hbe⟩

/-- A `k`-guarded term with nonempty outputs is a single block. -/
theorem prefixOK_of_kguarded {k : ℕ} {Y : Ty} {c : Term Y B⋆} (hc : KGuarded k B c)
    (hn : NonemptyOutput c) : PrefixOK k B 1 c := by
  refine ⟨KGuardedE.of_kguarded hc, ?_⟩
  rcases hc with ⟨v, rfl⟩ | ⟨u, v, hh, hs, hu, hv, rfl⟩
  · refine Or.inr ⟨v, ?_, PEq.refl _⟩
    have hpos : 1 ≤ valLength v := by
      have hne := hn (Ty.someElem Y)
      simp only [Term.den_comp, valLength] at hne ⊢
      rcases hd : v.den () with _ | ⟨a, l⟩
      · exact absurd (by simp [hd]) hne
      · simp
    omega
  · exact Or.inl ⟨u, Term.dotR hh v, le_of_eq hu.symm,
      EqSimple.dotR v (EqSimple.of_isSimple hs), Term.dotR_dotL u hh v⟩

/-- A `k`-guarded term with nonempty outputs is a single block. -/
theorem suffixOK_of_kguarded {k : ℕ} {Y : Ty} {c : Term Y B⋆} (hc : KGuarded k B c)
    (hn : NonemptyOutput c) : SuffixOK k B 1 c := by
  refine ⟨KGuardedE.of_kguarded hc, ?_⟩
  rcases hc with ⟨v, rfl⟩ | ⟨u, v, hh, hs, hu, hv, rfl⟩
  · refine Or.inr ⟨v, ?_, PEq.refl _⟩
    have hpos : 1 ≤ valLength v := by
      have hne := hn (Ty.someElem Y)
      simp only [Term.den_comp, valLength] at hne ⊢
      rcases hd : v.den () with _ | ⟨a, l⟩
      · exact absurd (by simp [hd]) hne
      · simp
    omega
  · exact Or.inl ⟨v, Term.dotL u hh, le_of_eq hv.symm,
      EqSimple.dotL u (EqSimple.of_isSimple hs), PEq.refl _⟩

/-- Concatenating a block on the right of a product of blocks. -/
theorem prefixOK_fdot {k j : ℕ} {Y Z : Ty} {a : Term Y B⋆} {c : Term Z B⋆}
    (ha : PrefixOK k B j a) (hc : PrefixOK k B 1 c) : PrefixOK k B (j + 1) (a ⊙ c) := by
  obtain ⟨hKa, ha'⟩ := ha
  obtain ⟨hKc, hc'⟩ := hc
  refine ⟨KGuardedE.fdot hKa hKc, ?_⟩
  rcases ha' with ⟨u, H, hu, hH, hae⟩ | ⟨v, hv, hae⟩
  · -- the accumulated product already starts with a long value
    refine Or.inl ⟨u, H ⊙ c, hu, EqSimple.fdot hH hKc.eqSimple, ?_⟩
    exact (Term.fdot_congr hae (PEq.refl _)).trans (Term.dotL_fdot u H c)
  · -- the accumulated product is a constant
    rcases hc' with ⟨u', H', hu', hH', hce⟩ | ⟨w, hw, hce⟩
    · refine Or.inl ⟨Term.dotL v u', Term.snd Y Z ⨟ H', by rw [valLength_dotL]; omega,
        hH'.comp_snd, ?_⟩
      calc (a ⊙ c) ≡ₜ ((Term.toUnit Y ⨟ v) ⊙ c) := Term.fdot_congr hae (PEq.refl _)
        _ ≡ₜ Term.dotL v (Term.snd Y Z ⨟ c) := Term.nilconst_fdot v c
        _ ≡ₜ Term.dotL v (Term.snd Y Z ⨟ Term.dotL u' H') :=
            Term.dotL_congr (PEq.refl _) (PEq.compR _ hce)
        _ ≡ₜ Term.dotL v (Term.dotL u' (Term.snd Y Z ⨟ H')) :=
            Term.dotL_congr (PEq.refl _) (Term.comp_dotL _ _ _)
        _ ≡ₜ Term.dotL (Term.dotL v u') (Term.snd Y Z ⨟ H') := Term.dotL_dotL _ _ _
    · refine Or.inr ⟨Term.dotL v w, ?_, ?_⟩
      · rw [valLength_dotL]
        omega
      · calc (a ⊙ c) ≡ₜ ((Term.toUnit Y ⨟ v) ⊙ c) := Term.fdot_congr hae (PEq.refl _)
          _ ≡ₜ Term.dotL v (Term.snd Y Z ⨟ c) := Term.nilconst_fdot v c
          _ ≡ₜ Term.dotL v (Term.snd Y Z ⨟ (Term.toUnit Z ⨟ w)) :=
              Term.dotL_congr (PEq.refl _) (PEq.compR _ hce)
          _ ≡ₜ Term.dotL v (Term.toUnit (Y ⊗ Z) ⨟ w) :=
              Term.dotL_congr (PEq.refl _)
                ((PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _)))
          _ ≡ₜ (Term.toUnit (Y ⊗ Z) ⨟ Term.dotL v w) := PEq.symm (Term.comp_dotL _ _ _)

/-- Concatenating a block on the left of a product of blocks. -/
theorem suffixOK_fdot {k j : ℕ} {Y Z : Ty} {c : Term Y B⋆} {b : Term Z B⋆}
    (hc : SuffixOK k B 1 c) (hb : SuffixOK k B j b) : SuffixOK k B (j + 1) (c ⊙ b) := by
  obtain ⟨hKc, hc'⟩ := hc
  obtain ⟨hKb, hb'⟩ := hb
  refine ⟨KGuardedE.fdot hKc hKb, ?_⟩
  rcases hb' with ⟨v, H, hv, hH, hbe⟩ | ⟨w, hw, hbe⟩
  · refine Or.inl ⟨v, c ⊙ H, hv, EqSimple.fdot hKc.eqSimple hH, ?_⟩
    exact (Term.fdot_congr (PEq.refl _) hbe).trans (Term.dotR_fdot c H v)
  · rcases hc' with ⟨v', H', hv', hH', hce⟩ | ⟨w', hw', hce⟩
    · refine Or.inl ⟨Term.dotL v' w, Term.fst Y Z ⨟ H', by rw [valLength_dotL]; omega,
        hH'.comp_fst, ?_⟩
      calc (c ⊙ b) ≡ₜ (c ⊙ (Term.toUnit Z ⨟ w)) := Term.fdot_congr (PEq.refl _) hbe
        _ ≡ₜ Term.dotR (Term.fst Y Z ⨟ c) w := Term.fdot_nilconst c w
        _ ≡ₜ Term.dotR (Term.fst Y Z ⨟ Term.dotR H' v') w :=
            Term.dotR_congr (PEq.compR _ hce) (PEq.refl _)
        _ ≡ₜ Term.dotR (Term.dotR (Term.fst Y Z ⨟ H') v') w :=
            Term.dotR_congr (Term.comp_dotR _ _ _) (PEq.refl _)
        _ ≡ₜ Term.dotR (Term.fst Y Z ⨟ H') (Term.dotL v' w) := Term.dotR_dotR _ _ _
    · refine Or.inr ⟨Term.dotL w' w, ?_, ?_⟩
      · rw [valLength_dotL]
        omega
      · calc (c ⊙ b) ≡ₜ (c ⊙ (Term.toUnit Z ⨟ w)) := Term.fdot_congr (PEq.refl _) hbe
          _ ≡ₜ Term.dotR (Term.fst Y Z ⨟ c) w := Term.fdot_nilconst c w
          _ ≡ₜ Term.dotR (Term.fst Y Z ⨟ (Term.toUnit Y ⨟ w')) w :=
              Term.dotR_congr (PEq.compR _ hce) (PEq.refl _)
          _ ≡ₜ Term.dotR (Term.toUnit (Y ⊗ Z) ⨟ w') w :=
              Term.dotR_congr ((PEq.symm (PEq.comp_assoc _ _ _)).trans
                (PEq.compL _ (PEq.unit_unique _ _))) (PEq.refl _)
          _ ≡ₜ (Term.toUnit (Y ⊗ Z) ⨟ Term.dotL w' w) :=
              (PEq.symm (Term.comp_dotR _ _ _)).trans
                (PEq.compR _ (PEq.symm (Term.dotL_eq_dotR w' w)))

/-- Prefixing the empty constant does not change the prefix of a product of blocks. -/
theorem prefixOK_nilconst_fdot {k j : ℕ} {X Y : Ty} {c : Term Y B⋆}
    (hc : PrefixOK k B j c) : PrefixOK k B j (nilconst B X ⊙ c) := by
  obtain ⟨hK, hc'⟩ := hc
  have hsnd : (nilconst B X ⊙ c) ≡ₜ (Term.snd X Y ⨟ c) := Term.prodF_nilconst_binconcat_left c
  refine ⟨KGuardedE.fdot (Or.inl ⟨Term.nilT B, PEq.refl _⟩) hK, ?_⟩
  rcases hc' with ⟨u, H, hu, hH, hce⟩ | ⟨v, hv, hce⟩
  · refine Or.inl ⟨u, Term.snd X Y ⨟ H, hu, hH.comp_snd, ?_⟩
    calc (nilconst B X ⊙ c) ≡ₜ (Term.snd X Y ⨟ c) := hsnd
      _ ≡ₜ (Term.snd X Y ⨟ Term.dotL u H) := PEq.compR _ hce
      _ ≡ₜ Term.dotL u (Term.snd X Y ⨟ H) := Term.comp_dotL _ _ _
  · refine Or.inr ⟨v, hv, ?_⟩
    calc (nilconst B X ⊙ c) ≡ₜ (Term.snd X Y ⨟ c) := hsnd
      _ ≡ₜ (Term.snd X Y ⨟ (Term.toUnit Y ⨟ v)) := PEq.compR _ hce
      _ ≡ₜ (Term.toUnit (X ⊗ Y) ⨟ v) :=
          (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- Appending the empty constant does not change the suffix of a product of blocks. -/
theorem suffixOK_fdot_nilconst {k j : ℕ} {X Y : Ty} {c : Term Y B⋆}
    (hc : SuffixOK k B j c) : SuffixOK k B j (c ⊙ nilconst B X) := by
  obtain ⟨hK, hc'⟩ := hc
  have hfst : (c ⊙ nilconst B X) ≡ₜ (Term.fst Y X ⨟ c) := Term.prodF_nilconst_binconcat c
  refine ⟨KGuardedE.fdot hK (Or.inl ⟨Term.nilT B, PEq.refl _⟩), ?_⟩
  rcases hc' with ⟨v, H, hv, hH, hce⟩ | ⟨w, hw, hce⟩
  · refine Or.inl ⟨v, Term.fst Y X ⨟ H, hv, hH.comp_fst, ?_⟩
    calc (c ⊙ nilconst B X) ≡ₜ (Term.fst Y X ⨟ c) := hfst
      _ ≡ₜ (Term.fst Y X ⨟ Term.dotR H v) := PEq.compR _ hce
      _ ≡ₜ Term.dotR (Term.fst Y X ⨟ H) v := Term.comp_dotR _ _ _
  · refine Or.inr ⟨w, hw, ?_⟩
    calc (c ⊙ nilconst B X) ≡ₜ (Term.fst Y X ⨟ c) := hfst
      _ ≡ₜ (Term.fst Y X ⨟ (Term.toUnit Y ⨟ w)) := PEq.compR _ hce
      _ ≡ₜ (Term.toUnit (Y ⊗ X) ⨟ w) :=
          (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- After `k` blocks, the product is preceded by a value of length at least `k`. -/
theorem PrefixOK.toLong {k : ℕ} {Y : Ty} {a : Term Y B⋆} (ha : PrefixOK k B k a) :
    ∃ (u : Value B⋆) (H : Term Y B⋆), k ≤ valLength u ∧ EqSimple B H ∧ a ≡ₜ Term.dotL u H := by
  rcases ha.2 with h | ⟨v, hv, hae⟩
  · exact h
  · refine ⟨v, nilconst B Y, by simpa using hv, EqSimple.nilconst Y B, ?_⟩
    exact hae.trans (PEq.symm (Term.dotL_nilconst Y B v))

/-- After `k` blocks, the product is followed by a value of length at least `k`. -/
theorem SuffixOK.toLong {k : ℕ} {Y : Ty} {b : Term Y B⋆} (hb : SuffixOK k B k b) :
    ∃ (v : Value B⋆) (H : Term Y B⋆), k ≤ valLength v ∧ EqSimple B H ∧ b ≡ₜ Term.dotR H v := by
  rcases hb.2 with h | ⟨w, hw, hbe⟩
  · exact h
  · refine ⟨w, nilconst B Y, by simpa using hw, EqSimple.nilconst Y B, ?_⟩
    exact hbe.trans (PEq.symm (Term.dotR_nilconst Y B w))

/-- **A guarded term from a long prefix and a long suffix.** -/
theorem kguardedE_of_prefix_suffix {k : ℕ} {W₁ Y W₂ : Ty} {a : Term W₁ B⋆} {X : Term Y B⋆}
    {b : Term W₂ B⋆} (ha : PrefixOK k B k a) (hX : EqSimple B X) (hb : SuffixOK k B k b) :
    KGuardedE k B ((a ⊙ X) ⊙ b) := by
  obtain ⟨u, H, hu, hH, hae⟩ := ha.toLong
  obtain ⟨v, H', hv, hH', hbe⟩ := hb.toLong
  refine Or.inr ⟨u, v, (H ⊙ X) ⊙ H', EqSimple.fdot (EqSimple.fdot hH hX) hH', hu, hv, ?_⟩
  calc ((a ⊙ X) ⊙ b) ≡ₜ ((Term.dotL u H ⊙ X) ⊙ Term.dotR H' v) :=
        Term.fdot_congr (Term.fdot_congr hae (PEq.refl _)) hbe
    _ ≡ₜ (Term.dotL u (H ⊙ X) ⊙ Term.dotR H' v) :=
        Term.fdot_congr (Term.dotL_fdot u H X) (PEq.refl _)
    _ ≡ₜ Term.dotL u ((H ⊙ X) ⊙ Term.dotR H' v) := Term.dotL_fdot _ _ _
    _ ≡ₜ Term.dotL u (Term.dotR ((H ⊙ X) ⊙ H') v) :=
        Term.dotL_congr (PEq.refl _) (Term.dotR_fdot _ _ _)
    _ ≡ₜ Term.dotR (Term.dotL u ((H ⊙ X) ⊙ H')) v := PEq.symm (Term.dotR_dotL _ _ _)

/-! ### Two combinators for joint decompositions -/

/-- Re-bracketing a four-fold concatenation. -/
def rebr4 (W₁ Y₁ Y₂ W₂ : Ty) :
    Term ((W₁ ⊗ Y₁) ⊗ (Y₂ ⊗ W₂)) ((W₁ ⊗ (Y₁ ⊗ Y₂)) ⊗ W₂) :=
  Term.assocR W₁ Y₁ (Y₂ ⊗ W₂) ⨟
    (Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟ Term.assocL W₁ (Y₁ ⊗ Y₂) W₂)

theorem provableIso_rebr4 (W₁ Y₁ Y₂ W₂ : Ty) : ProvableIso (rebr4 W₁ Y₁ Y₂ W₂) :=
  ProvableIso.comp (ProvableIso.assocR _ _ _)
    (ProvableIso.comp (ProvableIso.prodF (ProvableIso.id _) (ProvableIso.assocL _ _ _))
      (ProvableIso.assocL _ _ _))

theorem rebr4_fdot {W₁ Y₁ Y₂ W₂ : Ty} (a : Term W₁ B⋆) (x : Term Y₁ B⋆) (y : Term Y₂ B⋆)
    (b : Term W₂ B⋆) :
    (rebr4 W₁ Y₁ Y₂ W₂ ⨟ ((a ⊙ (x ⊙ y)) ⊙ b)) ≡ₜ ((a ⊙ x) ⊙ (y ⊙ b)) := by
  have hL : ((a ⊙ (x ⊙ y)) ⊙ b) ≡ₜ
      (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟
        (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b))))) := by
    calc ((a ⊙ (x ⊙ y)) ⊙ b)
        ≡ₜ (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟ (a ⊙ ((x ⊙ y) ⊙ b))) := Term.fdot_assoc a (x ⊙ y) b
      _ ≡ₜ (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟ (a ⊙ (Term.assocR Y₁ Y₂ W₂ ⨟ (x ⊙ (y ⊙ b))))) :=
          PEq.compR _ (Term.fdot_congr (PEq.refl _) (Term.fdot_assoc x y b))
      _ ≡ₜ _ := PEq.compR _ (PEq.symm (Term.fdot_comp_right a (Term.assocR Y₁ Y₂ W₂) _))
  have hR : ((a ⊙ x) ⊙ (y ⊙ b)) ≡ₜ
      (Term.assocR W₁ Y₁ (Y₂ ⊗ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b)))) := Term.fdot_assoc a x (y ⊙ b)
  calc (rebr4 W₁ Y₁ Y₂ W₂ ⨟ ((a ⊙ (x ⊙ y)) ⊙ b))
      ≡ₜ (rebr4 W₁ Y₁ Y₂ W₂ ⨟ (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟
          (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b)))))) :=
        PEq.compR _ hL
    _ ≡ₜ (Term.assocR W₁ Y₁ (Y₂ ⊗ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b)))) := by
        have hcancel :
            ((Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟ Term.assocL W₁ (Y₁ ⊗ Y₂) W₂) ⨟
              (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟
                (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟
                  (a ⊙ (x ⊙ (y ⊙ b)))))) ≡ₜ (a ⊙ (x ⊙ (y ⊙ b))) := by
          calc ((Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟ Term.assocL W₁ (Y₁ ⊗ Y₂) W₂) ⨟
                (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟
                  (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b))))))
              ≡ₜ (Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟
                  (Term.assocL W₁ (Y₁ ⊗ Y₂) W₂ ⨟ (Term.assocR W₁ (Y₁ ⊗ Y₂) W₂ ⨟
                    (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟
                      (a ⊙ (x ⊙ (y ⊙ b))))))) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟
                  ((Term.assocL W₁ (Y₁ ⊗ Y₂) W₂ ⨟ Term.assocR W₁ (Y₁ ⊗ Y₂) W₂) ⨟
                    (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟
                      (a ⊙ (x ⊙ (y ⊙ b)))))) :=
                PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
            _ ≡ₜ (Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟
                  (Term.id _ ⨟ (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟
                    (a ⊙ (x ⊙ (y ⊙ b)))))) :=
                PEq.compR _ (PEq.compL _ (PEq.assocL_assocR _ _ _))
            _ ≡ₜ (Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟
                  (Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂) ⨟
                    (a ⊙ (x ⊙ (y ⊙ b))))) := PEq.compR _ (PEq.id_comp _)
            _ ≡ₜ ((Term.prodF (Term.id W₁) (Term.assocL Y₁ Y₂ W₂) ⨟
                  Term.prodF (Term.id W₁) (Term.assocR Y₁ Y₂ W₂)) ⨟
                    (a ⊙ (x ⊙ (y ⊙ b)))) := PEq.symm (PEq.comp_assoc _ _ _)
            _ ≡ₜ (Term.prodF (Term.id W₁ ⨟ Term.id W₁)
                  (Term.assocL Y₁ Y₂ W₂ ⨟ Term.assocR Y₁ Y₂ W₂) ⨟ (a ⊙ (x ⊙ (y ⊙ b)))) :=
                PEq.compL _ (PEq.prod_comp _ _ _ _)
            _ ≡ₜ (Term.prodF (Term.id W₁) (Term.id (Y₁ ⊗ (Y₂ ⊗ W₂))) ⨟
                  (a ⊙ (x ⊙ (y ⊙ b)))) :=
                PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.assocL_assocR _ _ _))
            _ ≡ₜ (Term.id (W₁ ⊗ (Y₁ ⊗ (Y₂ ⊗ W₂))) ⨟ (a ⊙ (x ⊙ (y ⊙ b)))) :=
                PEq.compL _ (PEq.prod_id _ _)
            _ ≡ₜ _ := PEq.id_comp _
        exact (PEq.comp_assoc _ _ _).trans (PEq.compR _ hcancel)
    _ ≡ₜ ((a ⊙ x) ⊙ (y ⊙ b)) := PEq.symm hR

namespace JointCasesD

/-- **Splitting a co-product inside a concatenation.**  If the middle factor of a three-fold
concatenation becomes a co-pairing after a provable isomorphism, then a joint decomposition
of the two cases yields a joint decomposition of the whole concatenation. -/
theorem ctx_peel {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ}
    {W₁ W₂ Y Y₁ Y₂ : Ty} (a a' : Term W₁ B⋆) (b b' : Term W₂ B⋆)
    {T S : Term Y B⋆} {p : Term (Y₁ ⊕' Y₂) Y} (hp : ProvableIso p)
    {x₁ y₁ : Term Y₁ B⋆} {x₂ y₂ : Term Y₂ B⋆}
    (hT : (p ⨟ T) ≡ₜ Term.either x₁ x₂) (hS : (p ⨟ S) ≡ₜ Term.either y₁ y₂)
    (h₁ : JointCasesD B P d ((a ⊙ x₁) ⊙ b) ((a' ⊙ y₁) ⊙ b'))
    (h₂ : JointCasesD B P d ((a ⊙ x₂) ⊙ b) ((a' ⊙ y₂) ⊙ b')) :
    JointCasesD B P d ((a ⊙ T) ⊙ b) ((a' ⊙ S) ⊙ b') := by
  have key : ∀ (c : Term W₁ B⋆) (e : Term W₂ B⋆) (U : Term Y B⋆) (u₁ : Term Y₁ B⋆)
      (u₂ : Term Y₂ B⋆), (p ⨟ U) ≡ₜ Term.either u₁ u₂ →
      ((Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟
        Term.prodF (Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) (Term.id W₂)) ⨟
          ((c ⊙ U) ⊙ e)) ≡ₜ Term.either ((c ⊙ u₁) ⊙ e) ((c ⊙ u₂) ⊙ e) := by
    intro c e U u₁ u₂ hU
    have h1 : (Term.prodF (Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) (Term.id W₂) ⨟
        ((c ⊙ U) ⊙ e)) ≡ₜ
        (Term.either ((c ⊙ u₁)) ((c ⊙ u₂)) ⊙ e) := by
      refine (Term.fdot_comp_left e _ (c ⊙ U)).trans (Term.fdot_congr ?_ (PEq.refl _))
      calc ((Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) ⨟ (c ⊙ U))
          ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (Term.prodF (Term.id W₁) p ⨟ (c ⊙ U))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (c ⊙ (p ⨟ U))) :=
            PEq.compR _ (Term.fdot_comp_right c p U)
        _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (c ⊙ Term.either u₁ u₂)) :=
            PEq.compR _ (Term.fdot_congr (PEq.refl _) hU)
        _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟
              (Term.distR W₁ Y₁ Y₂ ⨟ Term.either (c ⊙ u₁) (c ⊙ u₂))) :=
            PEq.compR _ (Term.fdot_either_distR _ _ _)
        _ ≡ₜ ((Term.undistR W₁ Y₁ Y₂ ⨟ Term.distR W₁ Y₁ Y₂) ⨟
              Term.either (c ⊙ u₁) (c ⊙ u₂)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id _ ⨟ Term.either (c ⊙ u₁) (c ⊙ u₂)) :=
            PEq.compL _ (PEq.undistR_distR _ _ _)
        _ ≡ₜ _ := PEq.id_comp _
    calc ((Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟
          Term.prodF (Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) (Term.id W₂)) ⨟
            ((c ⊙ U) ⊙ e))
        ≡ₜ (Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟
            (Term.prodF (Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) (Term.id W₂) ⨟
              ((c ⊙ U) ⊙ e))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟ (Term.either (c ⊙ u₁) (c ⊙ u₂) ⊙ e)) :=
          PEq.compR _ h1
      _ ≡ₜ (Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟
            (Term.distL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟
              Term.either ((c ⊙ u₁) ⊙ e) ((c ⊙ u₂) ⊙ e))) :=
          PEq.compR _ (Term.fdot_either_distL _ _ _)
      _ ≡ₜ ((Term.undistL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂ ⨟ Term.distL (W₁ ⊗ Y₁) (W₁ ⊗ Y₂) W₂) ⨟
            Term.either ((c ⊙ u₁) ⊙ e) ((c ⊙ u₂) ⊙ e)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id _ ⨟ Term.either ((c ⊙ u₁) ⊙ e) ((c ⊙ u₂) ⊙ e)) :=
          PEq.compL _ (PEq.undistL_distL _ _ _)
      _ ≡ₜ _ := PEq.id_comp _
  refine precomp (ProvableIso.comp (ProvableIso.undistL _ _ _)
    (ProvableIso.prodF (ProvableIso.comp (ProvableIso.undistR _ _ _)
      (ProvableIso.prodF (ProvableIso.id _) hp)) (ProvableIso.id _))) ?_
  exact congr (key a b T x₁ x₂ hT) (key a' b' S y₁ y₂ hS) (node h₁ h₂)

/-- **Splitting a co-product inside a concatenation**, with nothing on the right. -/
theorem ctx_peelL {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ}
    {W₁ Y Y₁ Y₂ : Ty} (a a' : Term W₁ B⋆)
    {T S : Term Y B⋆} {p : Term (Y₁ ⊕' Y₂) Y} (hp : ProvableIso p)
    {x₁ y₁ : Term Y₁ B⋆} {x₂ y₂ : Term Y₂ B⋆}
    (hT : (p ⨟ T) ≡ₜ Term.either x₁ x₂) (hS : (p ⨟ S) ≡ₜ Term.either y₁ y₂)
    (h₁ : JointCasesD B P d (a ⊙ x₁) (a' ⊙ y₁))
    (h₂ : JointCasesD B P d (a ⊙ x₂) (a' ⊙ y₂)) :
    JointCasesD B P d (a ⊙ T) (a' ⊙ S) := by
  have key : ∀ (c : Term W₁ B⋆) (U : Term Y B⋆) (u₁ : Term Y₁ B⋆) (u₂ : Term Y₂ B⋆),
      (p ⨟ U) ≡ₜ Term.either u₁ u₂ →
      ((Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) ⨟ (c ⊙ U)) ≡ₜ
        Term.either (c ⊙ u₁) (c ⊙ u₂) := by
    intro c U u₁ u₂ hU
    calc ((Term.undistR W₁ Y₁ Y₂ ⨟ Term.prodF (Term.id W₁) p) ⨟ (c ⊙ U))
        ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (Term.prodF (Term.id W₁) p ⨟ (c ⊙ U))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (c ⊙ (p ⨟ U))) :=
          PEq.compR _ (Term.fdot_comp_right c p U)
      _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟ (c ⊙ Term.either u₁ u₂)) :=
          PEq.compR _ (Term.fdot_congr (PEq.refl _) hU)
      _ ≡ₜ (Term.undistR W₁ Y₁ Y₂ ⨟
            (Term.distR W₁ Y₁ Y₂ ⨟ Term.either (c ⊙ u₁) (c ⊙ u₂))) :=
          PEq.compR _ (Term.fdot_either_distR _ _ _)
      _ ≡ₜ ((Term.undistR W₁ Y₁ Y₂ ⨟ Term.distR W₁ Y₁ Y₂) ⨟
            Term.either (c ⊙ u₁) (c ⊙ u₂)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id _ ⨟ Term.either (c ⊙ u₁) (c ⊙ u₂)) :=
          PEq.compL _ (PEq.undistR_distR _ _ _)
      _ ≡ₜ _ := PEq.id_comp _
  refine precomp (ProvableIso.comp (ProvableIso.undistR _ _ _)
    (ProvableIso.prodF (ProvableIso.id _) hp)) ?_
  exact congr (key a T x₁ x₂ hT) (key a' S y₁ y₂ hS) (node h₁ h₂)

end JointCasesD

end Lax149335Proofs

bridge_export Lax149335Proofs
