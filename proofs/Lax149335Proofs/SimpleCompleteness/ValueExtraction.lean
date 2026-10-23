import Lax149335Proofs.SimpleCompleteness.Conjugacy

/-!
# Value extraction (appendix, proof of Lemma 6.4)

This file proves the value extraction lemma behind Lemma 6.4 and derives Lemma 6.4 itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The shape of a simple rational term

The input type of a simple rational term determines the shape of the term, since each of the
constructors of `Lax149335Proofs.IsSimple` except the two that concatenate a value determines the
input type. -/

/-- The shape of a simple rational term, read off from its input type. -/
def SimpleShape (B : Ty) : (A : Ty) → Term A B⋆ → Prop
  | .unit, f => ∃ v : Value B⋆, f ≡ₜ (Term.toUnit Ty.unit ⨟ v)
  | .prod A₁ A₂, f => ∃ (f₁ : Term A₁ B⋆) (f₂ : Term A₂ B⋆),
      IsSimple B f₁ ∧ IsSimple B f₂ ∧ f ≡ₜ (f₁ ⊙ f₂)
  | .sum A₁ A₂, f => ∃ (f₁ : Term A₁ B⋆) (f₂ : Term A₂ B⋆),
      IsSimple B f₁ ∧ IsSimple B f₂ ∧ f ≡ₜ Term.either f₁ f₂
  | .list A₁, f => ∃ (w₀ w₁ : Value B⋆) (h : Term A₁ B⋆),
      IsSimple B h ∧ f ≡ₜ Term.dotR (Term.dotL w₀ (homT h)) w₁

/-- Every simple rational term has the shape determined by its input type. -/
theorem IsSimple.shape {B : Ty} : {A : Ty} → {f : Term A B⋆} → IsSimple B f →
    SimpleShape B A f := by
  intro A f hf
  induction hf with
  | nil =>
      refine ⟨nilT _, ?_⟩
      exact PEq.symm ((PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans
        (PEq.id_comp _))
  | either h₁ h₂ _ _ => exact ⟨_, _, h₁, h₂, PEq.refl _⟩
  | fdot h₁ h₂ _ _ => exact ⟨_, _, h₁, h₂, PEq.refl _⟩
  | @hom A f hf _ =>
      refine ⟨nilT _, nilT _, f, hf, ?_⟩
      exact PEq.symm ((Term.dotR_congr (Term.dotL_nil _) (PEq.refl _)).trans (Term.dotR_nil _))
  | @dotL A f w _ ih =>
      match A, f, ih with
      | .unit, f, ⟨v, hv⟩ =>
          exact ⟨Term.dotL w v, (Term.dotL_congr (PEq.refl _) hv).trans
            (PEq.symm (Term.comp_dotL _ _ _))⟩
      | .prod A₁ A₂, f, ⟨f₁, f₂, h₁, h₂, hf⟩ =>
          exact ⟨Term.dotL w f₁, f₂, IsSimple.dotL w h₁, h₂,
            (Term.dotL_congr (PEq.refl _) hf).trans (PEq.symm (Term.dotL_fdot w f₁ f₂))⟩
      | .sum A₁ A₂, f, ⟨f₁, f₂, h₁, h₂, hf⟩ =>
          exact ⟨Term.dotL w f₁, Term.dotL w f₂, IsSimple.dotL w h₁, IsSimple.dotL w h₂,
            (Term.dotL_congr (PEq.refl _) hf).trans (Term.dotL_either w f₁ f₂)⟩
      | .list A₁, f, ⟨w₀, w₁, h, hh, hf⟩ =>
          refine ⟨Term.dotL w w₀, w₁, h, hh, ?_⟩
          calc Term.dotL w f
              ≡ₜ Term.dotL w (Term.dotR (Term.dotL w₀ (homT h)) w₁) :=
                Term.dotL_congr (PEq.refl _) hf
            _ ≡ₜ Term.dotR (Term.dotL w (Term.dotL w₀ (homT h))) w₁ :=
                PEq.symm (Term.dotR_dotL _ _ _)
            _ ≡ₜ Term.dotR (Term.dotL (Term.dotL w w₀) (homT h)) w₁ :=
                Term.dotR_congr (Term.dotL_dotL _ _ _) (PEq.refl _)
  | @dotR A f w _ ih =>
      match A, f, ih with
      | .unit, f, ⟨v, hv⟩ =>
          exact ⟨Term.dotR v w, (Term.dotR_congr hv (PEq.refl _)).trans
            (PEq.symm (Term.comp_dotR _ _ _))⟩
      | .prod A₁ A₂, f, ⟨f₁, f₂, h₁, h₂, hf⟩ =>
          exact ⟨f₁, Term.dotR f₂ w, h₁, IsSimple.dotR w h₂,
            (Term.dotR_congr hf (PEq.refl _)).trans (PEq.symm (Term.dotR_fdot f₁ f₂ w))⟩
      | .sum A₁ A₂, f, ⟨f₁, f₂, h₁, h₂, hf⟩ =>
          exact ⟨Term.dotR f₁ w, Term.dotR f₂ w, IsSimple.dotR w h₁, IsSimple.dotR w h₂,
            (Term.dotR_congr hf (PEq.refl _)).trans (Term.dotR_either f₁ f₂ w)⟩
      | .list A₁, f, ⟨w₀, w₁, h, hh, hf⟩ =>
          refine ⟨w₀, Term.dotR w₁ w, h, hh, ?_⟩
          calc Term.dotR f w
              ≡ₜ Term.dotR (Term.dotR (Term.dotL w₀ (homT h)) w₁) w :=
                Term.dotR_congr hf (PEq.refl _)
            _ ≡ₜ Term.dotR (Term.dotL w₀ (homT h)) (Term.dotL w₁ w) := Term.dotR_dotR _ _ _
            _ ≡ₜ Term.dotR (Term.dotL w₀ (homT h)) (Term.dotR w₁ w) :=
                Term.dotR_congr (PEq.refl _) (Term.dotL_eq_dotR w₁ w)

/-! ### `k`-guarded terms up to provable equality

The class of `k`-guarded terms is not closed under the operations used in the proof, because
its definition asks for *syntactic* equality and for values of length exactly `k`.  The
following relaxation is, and it produces `k`-guarded terms up to provable equality. -/

/-- A term is *equationally `k`-guarded* if it is provably either a constant or of the form
`u · h · v` for an equationally simple term `h` and values `u`, `v` of length at least `k`. -/
def KGuardedE (k : ℕ) (B : Ty) {A : Ty} (f : Term A B⋆) : Prop :=
  (∃ v : Value B⋆, f ≡ₜ (toUnit A ⨟ v)) ∨
  (∃ (u v : Value B⋆) (h : Term A B⋆), EqSimple B h ∧ k ≤ valLength u ∧ k ≤ valLength v ∧
      f ≡ₜ dotR (dotL u h) v)

namespace KGuardedE

variable {k : ℕ} {A B : Ty}

theorem congr {f g : Term A B⋆} (h : f ≡ₜ g) (hg : KGuardedE k B g) : KGuardedE k B f := by
  rcases hg with ⟨v, hv⟩ | ⟨u, v, hh, hs, hu, hv, he⟩
  · exact Or.inl ⟨v, h.trans hv⟩
  · exact Or.inr ⟨u, v, hh, hs, hu, hv, h.trans he⟩

theorem of_kguarded {f : Term A B⋆} (hf : KGuarded k B f) : KGuardedE k B f := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, hs, hu, hv, he⟩
  · exact Or.inl ⟨v, hv ▸ PEq.refl _⟩
  · exact Or.inr ⟨u, v, h, EqSimple.of_isSimple hs, le_of_eq hu.symm, le_of_eq hv.symm,
      he ▸ PEq.refl _⟩

/-- Splitting a value into a prefix of a prescribed length and the remaining suffix. -/
theorem _root_.Lax149335Proofs.value_split (B : Ty) (u : Value B⋆) (j : ℕ) (hj : j ≤ valLength u) :
    ∃ u₁ u₂ : Value B⋆, valLength u₁ = j ∧ u ≡ₜ dotL u₁ u₂ := by
  refine ⟨encV B⋆ ((u.den ()).take j), encV B⋆ ((u.den ()).drop j), ?_, ?_⟩
  · simp only [valLength] at hj ⊢
    simp only [den_encV, List.length_take]
    omega
  · refine value_eq_of_den _ _ ?_
    simp only [Term.den_dotL, den_encV, List.append_eq, List.take_append_drop]

/-- Splitting a value into a prefix and a suffix of a prescribed length. -/
theorem _root_.Lax149335Proofs.value_split_right (B : Ty) (u : Value B⋆) (j : ℕ)
    (hj : j ≤ valLength u) : ∃ u₁ u₂ : Value B⋆, valLength u₂ = j ∧ u ≡ₜ dotL u₁ u₂ := by
  refine ⟨encV B⋆ ((u.den ()).take ((u.den ()).length - j)),
    encV B⋆ ((u.den ()).drop ((u.den ()).length - j)), ?_, ?_⟩
  · simp only [valLength] at hj ⊢
    simp only [den_encV, List.length_drop]
    omega
  · refine value_eq_of_den _ _ ?_
    simp only [Term.den_dotL, den_encV, List.append_eq, List.take_append_drop]

/-- An equationally `k`-guarded term is provably equal to a `k`-guarded term. -/
theorem toKGuarded {f : Term A B⋆} (hf : KGuardedE k B f) :
    ∃ f' : Term A B⋆, f ≡ₜ f' ∧ KGuarded k B f' := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, ⟨s, hs, hhs⟩, hu, hv, he⟩
  · exact ⟨toUnit A ⨟ v, hv, Or.inl ⟨v, rfl⟩⟩
  obtain ⟨u₁, u₂, hu₁, hu₂⟩ := value_split B u k hu
  obtain ⟨v₁, v₂, hv₂, hv₁⟩ := value_split_right B v k hv
  refine ⟨dotR (dotL u₁ (dotR (dotL u₂ s) v₁)) v₂, ?_,
    Or.inr ⟨u₁, v₂, dotR (dotL u₂ s) v₁, IsSimple.dotR v₁ (IsSimple.dotL u₂ hs), hu₁, hv₂,
      rfl⟩⟩
  calc f ≡ₜ dotR (dotL u h) v := he
    _ ≡ₜ dotR (dotL u s) v := Term.dotR_congr (Term.dotL_congr (PEq.refl _) hhs) (PEq.refl _)
    _ ≡ₜ dotR (dotL (dotL u₁ u₂) s) v :=
        Term.dotR_congr (Term.dotL_congr hu₂ (PEq.refl _)) (PEq.refl _)
    _ ≡ₜ dotR (dotL u₁ (dotL u₂ s)) v :=
        Term.dotR_congr (PEq.symm (Term.dotL_dotL _ _ _)) (PEq.refl _)
    _ ≡ₜ dotR (dotL u₁ (dotL u₂ s)) (dotL v₁ v₂) := Term.dotR_congr (PEq.refl _) hv₁
    _ ≡ₜ dotR (dotR (dotL u₁ (dotL u₂ s)) v₁) v₂ := PEq.symm (Term.dotR_dotR _ _ _)
    _ ≡ₜ dotR (dotL u₁ (dotR (dotL u₂ s) v₁)) v₂ :=
        Term.dotR_congr (Term.dotR_dotL _ _ _) (PEq.refl _)

/-- Equational `k`-guardedness is preserved by prepending a value. -/
theorem prepend {f : Term A B⋆} (w : Value B⋆) (hf : KGuardedE k B f) :
    KGuardedE k B (Term.dotL w f) := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, hs, hu, hv, he⟩
  · refine Or.inl ⟨Term.dotL w v, ?_⟩
    exact (Term.dotL_congr (PEq.refl _) hv).trans (PEq.symm (Term.comp_dotL _ _ _))
  · refine Or.inr ⟨Term.dotL w u, v, h, hs, by rw [valLength_dotL]; omega, hv, ?_⟩
    calc Term.dotL w f ≡ₜ Term.dotL w (dotR (dotL u h) v) := Term.dotL_congr (PEq.refl _) he
      _ ≡ₜ dotR (dotL w (dotL u h)) v := PEq.symm (Term.dotR_dotL _ _ _)
      _ ≡ₜ dotR (dotL (Term.dotL w u) h) v :=
          Term.dotR_congr (Term.dotL_dotL _ _ _) (PEq.refl _)

/-- Equational `k`-guardedness is preserved by appending a value. -/
theorem append {f : Term A B⋆} (w : Value B⋆) (hf : KGuardedE k B f) :
    KGuardedE k B (Term.dotR f w) := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, hs, hu, hv, he⟩
  · refine Or.inl ⟨Term.dotR v w, ?_⟩
    exact (Term.dotR_congr hv (PEq.refl _)).trans (PEq.symm (Term.comp_dotR _ _ _))
  · refine Or.inr ⟨u, Term.dotL v w, h, hs, hu, by rw [valLength_dotL]; omega, ?_⟩
    calc Term.dotR f w ≡ₜ Term.dotR (dotR (dotL u h) v) w := Term.dotR_congr he (PEq.refl _)
      _ ≡ₜ dotR (dotL u h) (Term.dotL v w) := Term.dotR_dotR _ _ _

/-- Prefixing a constant to a term. -/
theorem _root_.Lax149335Proofs.Term.nilconst_fdot {A₁ A₂ B : Ty} (c : Value B⋆) (f : Term A₂ B⋆) :
    ((toUnit A₁ ⨟ c) ⊙ f) ≡ₜ Term.dotL c (snd A₁ A₂ ⨟ f) :=
  ((Term.fdot_congr (PEq.symm (Term.dotL_nilconst A₁ B c)) (PEq.refl _)).trans
      (Term.dotL_fdot c _ f)).trans
    (Term.dotL_congr (PEq.refl _) (Term.prodF_nilconst_binconcat_left f))

/-- Appending a constant to a term. -/
theorem _root_.Lax149335Proofs.Term.fdot_nilconst {A₁ A₂ B : Ty} (f : Term A₁ B⋆) (c : Value B⋆) :
    (f ⊙ (toUnit A₂ ⨟ c)) ≡ₜ Term.dotR (fst A₁ A₂ ⨟ f) c :=
  ((Term.fdot_congr (PEq.refl _) (PEq.symm (Term.dotR_nilconst A₂ B c))).trans
      (Term.dotR_fdot f _ c)).trans
    (Term.dotR_congr (Term.prodF_nilconst_binconcat f) (PEq.refl _))

/-- Composing with the second projection stays equationally simple. -/
theorem _root_.Lax149335Proofs.EqSimple.comp_snd {A₁ A₂ B : Ty} {h : Term A₂ B⋆} (hh : EqSimple B h) :
    EqSimple B (snd A₁ A₂ ⨟ h) :=
  EqSimple.congr (PEq.symm (Term.prodF_nilconst_binconcat_left h))
    (EqSimple.fdot (EqSimple.nilconst A₁ B) hh)

/-- Composing with the first projection stays equationally simple. -/
theorem _root_.Lax149335Proofs.EqSimple.comp_fst {A₁ A₂ B : Ty} {h : Term A₁ B⋆} (hh : EqSimple B h) :
    EqSimple B (fst A₁ A₂ ⨟ h) :=
  EqSimple.congr (PEq.symm (Term.prodF_nilconst_binconcat h))
    (EqSimple.fdot hh (EqSimple.nilconst A₂ B))

/-- Equational `k`-guardedness is preserved by pre-composition with a term that preserves
equational simplicity. -/
theorem comp {X : Ty} (q : Term X A)
    (hq : ∀ h : Term A B⋆, EqSimple B h → EqSimple B (q ⨟ h))
    {f : Term A B⋆} (hf : KGuardedE k B f) : KGuardedE k B (q ⨟ f) := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, hs, hu, hv, he⟩
  · refine Or.inl ⟨v, ?_⟩
    calc (q ⨟ f) ≡ₜ (q ⨟ (toUnit A ⨟ v)) := PEq.compR _ hv
      _ ≡ₜ ((q ⨟ toUnit A) ⨟ v) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (toUnit X ⨟ v) := PEq.compL _ (PEq.unit_unique _ _)
  · refine Or.inr ⟨u, v, q ⨟ h, hq h hs, hu, hv, ?_⟩
    calc (q ⨟ f) ≡ₜ (q ⨟ dotR (dotL u h) v) := PEq.compR _ he
      _ ≡ₜ dotR (q ⨟ dotL u h) v := Term.comp_dotR _ _ _
      _ ≡ₜ dotR (dotL u (q ⨟ h)) v := Term.dotR_congr (Term.comp_dotL _ _ _) (PEq.refl _)

/-- **Equational `k`-guardedness is preserved by concatenation.** -/
theorem fdot {A₁ A₂ : Ty} {f₁ : Term A₁ B⋆} {f₂ : Term A₂ B⋆}
    (h₁ : KGuardedE k B f₁) (h₂ : KGuardedE k B f₂) : KGuardedE k B (f₁ ⊙ f₂) := by
  rcases h₁ with ⟨c₁, hc₁⟩ | ⟨u₁, v₁, h₁', hs₁, hu₁, hv₁, he₁⟩
  · -- the left factor is a constant
    have hstep : (f₁ ⊙ f₂) ≡ₜ Term.dotL c₁ (snd A₁ A₂ ⨟ f₂) :=
      (Term.fdot_congr hc₁ (PEq.refl _)).trans (Term.nilconst_fdot c₁ f₂)
    exact KGuardedE.congr hstep
      (KGuardedE.prepend c₁ (KGuardedE.comp (snd A₁ A₂) (fun _ hh => hh.comp_snd) h₂))
  rcases h₂ with ⟨c₂, hc₂⟩ | ⟨u₂, v₂, h₂', hs₂, hu₂, hv₂, he₂⟩
  · -- the right factor is a constant
    have hstep : (f₁ ⊙ f₂) ≡ₜ Term.dotR (fst A₁ A₂ ⨟ f₁) c₂ :=
      (Term.fdot_congr (PEq.refl _) hc₂).trans (Term.fdot_nilconst f₁ c₂)
    refine KGuardedE.congr hstep
      (KGuardedE.append c₂ (KGuardedE.comp (fst A₁ A₂) (fun _ hh => hh.comp_fst) ?_))
    exact Or.inr ⟨u₁, v₁, h₁', hs₁, hu₁, hv₁, he₁⟩
  -- both factors are long
  refine Or.inr ⟨u₁, v₂, Term.dotR h₁' (Term.dotL v₁ u₂) ⊙ h₂', EqSimple.fdot
    (EqSimple.dotR _ hs₁) hs₂, hu₁, hv₂, ?_⟩
  have hinner : Term.dotL v₁ (dotR (dotL u₂ h₂') v₂) ≡ₜ
      Term.dotL (Term.dotL v₁ u₂) (dotR h₂' v₂) :=
    (Term.dotL_congr (PEq.refl _) (Term.dotR_dotL u₂ h₂' v₂)).trans (Term.dotL_dotL _ _ _)
  calc (f₁ ⊙ f₂)
      ≡ₜ (dotR (dotL u₁ h₁') v₁ ⊙ dotR (dotL u₂ h₂') v₂) := Term.fdot_congr he₁ he₂
    _ ≡ₜ (dotL u₁ h₁' ⊙ Term.dotL v₁ (dotR (dotL u₂ h₂') v₂)) := Term.fdot_dotR_dotL _ _ _
    _ ≡ₜ (dotL u₁ h₁' ⊙ Term.dotL (Term.dotL v₁ u₂) (dotR h₂' v₂)) :=
        Term.fdot_congr (PEq.refl _) hinner
    _ ≡ₜ Term.dotL u₁ (h₁' ⊙ Term.dotL (Term.dotL v₁ u₂) (dotR h₂' v₂)) :=
        Term.dotL_fdot _ _ _
    _ ≡ₜ Term.dotL u₁ (Term.dotR h₁' (Term.dotL v₁ u₂) ⊙ dotR h₂' v₂) :=
        Term.dotL_congr (PEq.refl _) (PEq.symm (Term.fdot_dotR_dotL _ _ _))
    _ ≡ₜ Term.dotL u₁ (dotR (Term.dotR h₁' (Term.dotL v₁ u₂) ⊙ h₂') v₂) :=
        Term.dotL_congr (PEq.refl _) (Term.dotR_fdot _ _ _)
    _ ≡ₜ dotR (Term.dotL u₁ (Term.dotR h₁' (Term.dotL v₁ u₂) ⊙ h₂')) v₂ :=
        PEq.symm (Term.dotR_dotL _ _ _)

/-- A product of `k`-guarded nonempty terms is equationally `k`-guarded. -/
theorem of_kprodT {j : ℕ} : {Y : Ty} → {T : Term Y B⋆} → KProdT k B j T → KGuardedE k B T := by
  intro Y T h
  induction h with
  | nil =>
      refine Or.inl ⟨nilT B, ?_⟩
      exact PEq.symm ((PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans
        (PEq.id_comp _))
  | cons hf _ _ ih => exact KGuardedE.fdot (KGuardedE.of_kguarded hf) ih

end KGuardedE

/-! ### Two more ways of combining joint case decompositions -/

namespace JointCases

variable {B : Ty}

/-- A joint decomposition is preserved by concatenating a fixed pair of terms on the right,
given a joint decomposition of every component after the concatenation. -/
theorem fdot_right {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {W : Ty}
    (f g : Term W B⋆)
    (hstep : ∀ {Y : Ty} (T S : Term Y B⋆), P T S → JointCases B P' (T ⊙ f) (S ⊙ g)) :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S → JointCases B P' (T ⊙ f) (S ⊙ g) := by
  intro X T S hTS
  induction hTS with
  | leaf hP => exact hstep _ _ hP
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      refine congr (Term.fdot_either_distL T₁ T₂ f) (Term.fdot_either_distL S₁ S₂ g) ?_
      refine precomp (ProvableIso.undistL X₁ X₂ W) ?_ ?_
      · simp only [Ty.listDepth]
        omega
      · refine congr ?_ ?_ (node ih₁ ih₂)
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistL_distL X₁ X₂ W)).trans (PEq.id_comp _))
        · exact (PEq.comp_assoc _ _ _).symm.trans
            ((PEq.compL _ (PEq.undistL_distL X₁ X₂ W)).trans (PEq.id_comp _))
  | @precomp X Y q T S hq hd _ ih =>
      refine precomp (ProvableIso.prodF hq (ProvableIso.id W)) ?_ ?_
      · simp only [Ty.listDepth]
        omega
      · refine congr ?_ ?_ ih
        · exact Term.fdot_comp_left f q T
        · exact Term.fdot_comp_left g q S
  | congr h₁ h₂ _ ih =>
      exact congr (Term.fdot_congr h₁ (PEq.refl _)) (Term.fdot_congr h₂ (PEq.refl _)) ih

end JointCases

/-! ### Flattening a co-pairing decomposition -/

/-- Appending two lists of cases. -/
def Cases.append {B : Ty} : {As : List Ty} → Cases B As → {Bs : List Ty} → Cases B Bs →
    Cases B (As ++ Bs)
  | [], _, _, gs => gs
  | _ :: _, .cons f fs, _, gs => .cons f (Cases.append fs gs)

bridge_export Lax149335Proofs

/-- A relation holds for all pairs of terms in two lists of cases. -/
def Cases.All2 {B : Ty} (P : {Y : Ty} → Term Y B → Term Y B → Prop) :
    {As : List Ty} → Cases B As → Cases B As → Prop
  | [], _, _ => True
  | _ :: _, .cons f fs, .cons g gs => P f g ∧ Cases.All2 P fs gs

/-- Appending preserves a relation that holds for all pairs of cases. -/
theorem Cases.all2_append {B : Ty} {P : {Y : Ty} → Term Y B → Term Y B → Prop} :
    {As : List Ty} → (fs fs' : Cases B As) → {Bs : List Ty} → (gs gs' : Cases B Bs) →
    Cases.All2 P fs fs' → Cases.All2 P gs gs' →
    Cases.All2 P (fs.append gs) (fs'.append gs')
  | [], .nil, .nil, _, _, _, _, hg => hg
  | _ :: _, .cons _ fs, .cons _ fs', _, gs, gs', hf, hg =>
      ⟨hf.1, Cases.all2_append fs fs' gs gs' hf.2 hg⟩

/-- Re-associating a co-product before a three-fold co-pairing, from right to left. -/
theorem Term.sumAssocL_either {A E N C : Ty} (f : Term A C) (x : Term E C) (y : Term N C) :
    (Term.sumAssocL A E N ⨟ Term.either (Term.either f x) y) ≡ₜ
      Term.either f (Term.either x y) :=
  calc (Term.sumAssocL A E N ⨟ Term.either (Term.either f x) y)
      ≡ₜ (Term.sumAssocL A E N ⨟ (Term.sumAssocR A E N ⨟
          Term.either f (Term.either x y))) :=
        PEq.compR _ (PEq.symm (Term.sumAssocR_either f x y))
    _ ≡ₜ ((Term.sumAssocL A E N ⨟ Term.sumAssocR A E N) ⨟
          Term.either f (Term.either x y)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (A ⊕' (E ⊕' N)) ⨟ Term.either f (Term.either x y)) :=
        PEq.compL _ (Term.sumAssocL_sumAssocR A E N)
    _ ≡ₜ Term.either f (Term.either x y) := PEq.id_comp _

/-- The term that splits the co-product of a concatenation of two lists of summands into the
co-product of the two co-products. -/
def sumSplitTy : (C₀ : Ty) → (Cs : List Ty) → (D₀ : Ty) → (Ds : List Ty) →
    Term (sumTyOf C₀ (Cs ++ D₀ :: Ds)) (sumTyOf C₀ Cs ⊕' sumTyOf D₀ Ds)
  | _, [], _, _ => Term.id _
  | C₀, (C :: Cs), D₀, Ds =>
      Term.sumF (Term.id C₀) (sumSplitTy C Cs D₀ Ds) ⨟
        Term.sumAssocL C₀ (sumTyOf C Cs) (sumTyOf D₀ Ds)

/-- The splitting term is a provable isomorphism. -/
theorem provableIso_sumSplitTy : (C₀ : Ty) → (Cs : List Ty) → (D₀ : Ty) → (Ds : List Ty) →
    ProvableIso (sumSplitTy C₀ Cs D₀ Ds)
  | _, [], _, _ => ProvableIso.id _
  | C₀, (C :: Cs), D₀, Ds =>
      ProvableIso.comp (ProvableIso.sumF (ProvableIso.id C₀)
          (provableIso_sumSplitTy C Cs D₀ Ds))
        ⟨Term.sumAssocR C₀ (sumTyOf C Cs) (sumTyOf D₀ Ds),
          Term.sumAssocL_sumAssocR _ _ _, Term.sumAssocR_sumAssocL _ _ _⟩

/-- The splitting term turns a co-pairing of two co-pairings into a single co-pairing. -/
theorem sumSplitTy_copair {B : Ty} : (C₀ : Ty) → (Cs : List Ty) → (D₀ : Ty) → (Ds : List Ty) →
    (f₀ : Term C₀ B) → (fs : Cases B Cs) → (g₀ : Term D₀ B) → (gs : Cases B Ds) →
    (sumSplitTy C₀ Cs D₀ Ds ⨟ Term.either (copair f₀ fs) (copair g₀ gs)) ≡ₜ
      copair f₀ (fs.append (Cases.cons g₀ gs))
  | _, [], _, _, _, .nil, _, _ => PEq.id_comp _
  | C₀, (C :: Cs), D₀, Ds, f₀, .cons f₁ fs, g₀, gs => by
      have ih := sumSplitTy_copair C Cs D₀ Ds f₁ fs g₀ gs
      calc (sumSplitTy C₀ (C :: Cs) D₀ Ds ⨟
            Term.either (copair f₀ (Cases.cons f₁ fs)) (copair g₀ gs))
          ≡ₜ (Term.sumF (Term.id C₀) (sumSplitTy C Cs D₀ Ds) ⨟
              (Term.sumAssocL C₀ (sumTyOf C Cs) (sumTyOf D₀ Ds) ⨟
                Term.either (Term.either f₀ (copair f₁ fs)) (copair g₀ gs))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.sumF (Term.id C₀) (sumSplitTy C Cs D₀ Ds) ⨟
              Term.either f₀ (Term.either (copair f₁ fs) (copair g₀ gs))) :=
            PEq.compR _ (Term.sumAssocL_either _ _ _)
        _ ≡ₜ Term.either (Term.id C₀ ⨟ f₀) (sumSplitTy C Cs D₀ Ds ⨟
              Term.either (copair f₁ fs) (copair g₀ gs)) := Term.sumF_either _ _ _ _
        _ ≡ₜ Term.either f₀ (copair f₁ (fs.append (Cases.cons g₀ gs))) :=
            Term.either_congr (PEq.id_comp _) ih

/-! ### Equational simplicity of guarded terms -/

/-- An equationally `k`-guarded term is equationally simple. -/
theorem KGuardedE.eqSimple {k : ℕ} {A B : Ty} {f : Term A B⋆} (hf : KGuardedE k B f) :
    EqSimple B f := by
  rcases hf with ⟨v, hv⟩ | ⟨u, v, h, hs, -, -, he⟩
  · exact EqSimple.congr (hv.trans (PEq.symm (Term.dotL_nilconst A B v)))
      (EqSimple.dotL v (EqSimple.nilconst A B))
  · exact EqSimple.congr he (EqSimple.dotR v (EqSimple.dotL u hs))

/-- A matching pair of co-pairings of `k`-guarded terms consists of equationally simple
terms. -/
theorem KCopair2.eqSimple_left {k : ℕ} {B : Ty} :
    {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G → EqSimple B F := by
  intro X F G h
  induction h with
  | leaf hf _ _ _ => exact (KGuardedE.of_kguarded hf).eqSimple
  | node _ _ ih₁ ih₂ => exact EqSimple.either ih₁ ih₂

/-- A matching pair of co-pairings of `k`-guarded terms consists of equationally simple
terms. -/
theorem KCopair2.eqSimple_right {k : ℕ} {B : Ty} :
    {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G → EqSimple B G := by
  intro X F G h
  induction h with
  | leaf _ hg _ _ => exact (KGuardedE.of_kguarded hg).eqSimple
  | node _ _ ih₁ ih₂ => exact EqSimple.either ih₁ ih₂

/-! ### The list nesting depth of the shapes used by the bundle decomposition -/

/-- The `j`-th power of a type does not increase the list nesting depth. -/
theorem pow_app_listDepth (X : Ty) : (j : ℕ) → ((Term.TyF.pow j).app X).listDepth ≤ X.listDepth
  | 0 => by simp [Term.TyF.pow, Term.TyF.app, Ty.listDepth]
  | (j + 1) => by
      have := pow_app_listDepth X j
      simp only [Term.TyF.pow, Term.TyF.app, Ty.listDepth, max_le_iff]
      exact ⟨le_rfl, this⟩

/-- The co-product of the powers up to `j` does not increase the list nesting depth. -/
theorem lt_app_listDepth (X : Ty) : (j : ℕ) → ((Term.TyF.lt j).app X).listDepth ≤ X.listDepth
  | 0 => pow_app_listDepth X 0
  | (j + 1) => by
      have h₁ := lt_app_listDepth X j
      have h₂ := pow_app_listDepth X (j + 1)
      simp only [Term.TyF.lt, Term.TyF.app, Ty.listDepth, max_le_iff]
      exact ⟨h₁, h₂⟩

/-- The shape used by the bundle decomposition raises the list nesting depth by at most
one. -/
theorem fixedShape_app_listDepth (X : Ty) (m : ℕ) :
    ((Term.fixedShape m).app X).listDepth ≤ X.listDepth + 1 := by
  have h₁ := lt_app_listDepth X (2 * m + 1)
  have h₂ := pow_app_listDepth X (m + 1)
  simp only [Term.fixedShape, Term.midShape, Term.TyF.app, Ty.listDepth, max_le_iff]
  exact ⟨by omega, ⟨by omega, by omega⟩, by omega⟩

/-! ### The joint decomposition of the bundle shape -/

variable {B : Ty}

/-- A pair of terms, both of which are equationally `k`-guarded. -/
def KGuardedPair (k : ℕ) (B : Ty) {Y : Ty} (T S : Term Y B⋆) : Prop :=
  KGuardedE k B T ∧ KGuardedE k B S

/-- The power of a matching pair of co-pairings decomposes jointly into equationally
`k`-guarded components. -/
theorem jointCases_powMap {k : ℕ} {X : Ty} {F G : Term X B⋆} (hK : KCopair2 k B F G)
    (j : ℕ) : JointCases B (KGuardedPair k B) ((Term.TyF.pow j).homMap F)
      ((Term.TyF.pow j).homMap G) :=
  JointCases.mono (fun _ _ h => ⟨KGuardedE.of_kprodT h.1, KGuardedE.of_kprodT h.2⟩)
    (hK.pow_jointCases j)

/-- The co-product of the powers up to `j` of a matching pair of co-pairings decomposes
jointly into equationally `k`-guarded components. -/
theorem jointCases_ltMap {k : ℕ} {X : Ty} {F G : Term X B⋆} (hK : KCopair2 k B F G) :
    (j : ℕ) → JointCases B (KGuardedPair k B) ((Term.TyF.lt j).homMap F)
      ((Term.TyF.lt j).homMap G)
  | 0 => jointCases_powMap hK 0
  | (j + 1) => JointCases.node (jointCases_ltMap hK j) (jointCases_powMap hK (j + 1))

/-- The middle shape of the bundle decomposition, applied to a matching pair of co-pairings,
decomposes jointly into equationally `k`-guarded components: the `k` factors on each side
provide the required guards. -/
theorem jointCases_midMap {m : ℕ} {X : Ty} {F G : Term X B⋆} (hK : KCopair2 (m + 1) B F G) :
    JointCases B (KGuardedPair (m + 1) B) ((Term.midShape m).homMap F)
      ((Term.midShape m).homMap G) := by
  have hSF : EqSimple B (homT F) := EqSimple.hom hK.eqSimple_left
  have hSG : EqSimple B (homT G) := EqSimple.hom hK.eqSimple_right
  -- the `k` factors on the left provide a prefix of length at least `k`
  have step1 : JointCases B (fun {Y} (T S : Term Y B⋆) =>
      (∃ (u : Value B⋆) (H : Term Y B⋆), m + 1 ≤ valLength u ∧ EqSimple B H ∧
        T ≡ₜ Term.dotL u H) ∧
      (∃ (u : Value B⋆) (H : Term Y B⋆), m + 1 ≤ valLength u ∧ EqSimple B H ∧
        S ≡ₜ Term.dotL u H))
      ((Term.TyF.pow (m + 1)).homMap F ⊙ homT F)
      ((Term.TyF.pow (m + 1)).homMap G ⊙ homT G) := by
    refine JointCases.fdot_right (homT F) (homT G) (fun T S hTS => JointCases.leaf ?_)
      (hK.pow_jointCases (m + 1))
    obtain ⟨u, H, hu, hH, hT⟩ := KProdT.dotL_factor hTS.1
    obtain ⟨u', H', hu', hH', hS⟩ := KProdT.dotL_factor hTS.2
    refine ⟨⟨u, H ⊙ homT F, by simpa using hu, EqSimple.fdot hH hSF, ?_⟩,
      ⟨u', H' ⊙ homT G, by simpa using hu', EqSimple.fdot hH' hSG, ?_⟩⟩
    · exact (Term.fdot_congr hT (PEq.refl _)).trans (Term.dotL_fdot u H (homT F))
    · exact (Term.fdot_congr hS (PEq.refl _)).trans (Term.dotL_fdot u' H' (homT G))
  -- the `k` factors on the right provide a suffix of length at least `k`
  refine JointCases.fdot_left ((Term.TyF.pow (m + 1)).homMap F ⊙ homT F)
    ((Term.TyF.pow (m + 1)).homMap G ⊙ homT G) (fun T S hTS => ?_) (hK.pow_jointCases (m + 1))
  obtain ⟨v, H₂, hv, hH₂, hT⟩ := KProdT.dotR_factor hTS.1
  obtain ⟨v', H₂', hv', hH₂', hS⟩ := KProdT.dotR_factor hTS.2
  refine JointCases.fdot_right T S (fun U V hUV => JointCases.leaf ?_) step1
  obtain ⟨⟨u, H₁, hu, hH₁, hU⟩, ⟨u', H₁', hu', hH₁', hV⟩⟩ := hUV
  constructor
  · refine Or.inr ⟨u, v, H₁ ⊙ H₂, EqSimple.fdot hH₁ hH₂, hu, by simpa using hv, ?_⟩
    calc (U ⊙ T) ≡ₜ (Term.dotL u H₁ ⊙ Term.dotR H₂ v) := Term.fdot_congr hU hT
      _ ≡ₜ Term.dotL u (H₁ ⊙ Term.dotR H₂ v) := Term.dotL_fdot _ _ _
      _ ≡ₜ Term.dotL u (Term.dotR (H₁ ⊙ H₂) v) :=
          Term.dotL_congr (PEq.refl _) (Term.dotR_fdot _ _ _)
      _ ≡ₜ Term.dotR (Term.dotL u (H₁ ⊙ H₂)) v := PEq.symm (Term.dotR_dotL _ _ _)
  · refine Or.inr ⟨u', v', H₁' ⊙ H₂', EqSimple.fdot hH₁' hH₂', hu', by simpa using hv', ?_⟩
    calc (V ⊙ S) ≡ₜ (Term.dotL u' H₁' ⊙ Term.dotR H₂' v') := Term.fdot_congr hV hS
      _ ≡ₜ Term.dotL u' (H₁' ⊙ Term.dotR H₂' v') := Term.dotL_fdot _ _ _
      _ ≡ₜ Term.dotL u' (Term.dotR (H₁' ⊙ H₂') v') :=
          Term.dotL_congr (PEq.refl _) (Term.dotR_fdot _ _ _)
      _ ≡ₜ Term.dotR (Term.dotL u' (H₁' ⊙ H₂')) v' := PEq.symm (Term.dotR_dotL _ _ _)

/-- The whole bundle shape, applied to a matching pair of co-pairings, decomposes jointly
into equationally `k`-guarded components. -/
theorem jointCases_fixedMap {m : ℕ} {X : Ty} {F G : Term X B⋆} (hK : KCopair2 (m + 1) B F G) :
    JointCases B (KGuardedPair (m + 1) B) ((Term.fixedShape m).homMap F)
      ((Term.fixedShape m).homMap G) :=
  JointCases.node (jointCases_ltMap hK (2 * m + 1)) (jointCases_midMap hK)

end Lax149335Proofs

bridge_export Lax149335Proofs
