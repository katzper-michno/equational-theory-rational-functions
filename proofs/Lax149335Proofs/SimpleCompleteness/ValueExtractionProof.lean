import Lax149335Proofs.SimpleCompleteness.ListCase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

/-!
# Value extraction (the appendix lemma behind Lemma 6.4) and Lemma 6.4

This file states the *value extraction* lemma of the appendix (the section *Proofs for
soundness of the conjugacy rule*) and derives Lemma 6.4 from it.  The two statements were
originally in `Lax149335Proofs.SimpleCompleteness.Statements`; they live here because the proof of value
extraction uses the whole toolkit of `Lax149335Proofs.SimpleCompleteness.ValueExtraction`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- **Upgrading a co-pairing of equationally `k`-guarded terms to a co-pairing of `k`-guarded
terms.**  The class of `k`-guarded terms is not closed under provable equality, but every
equationally `k`-guarded term is provably equal to a `k`-guarded one, and the replacement can
be carried out inside a co-pairing. -/
theorem copair_upgrade2 {B : Ty} {k : ℕ} : {As : List Ty} → {A : Ty} → (T₀ S₀ : Term A B⋆) →
    (Ts Ss : Cases B⋆ As) → KGuardedPair k B T₀ S₀ → Cases.All2 (KGuardedPair k B) Ts Ss →
    ∃ (T₀' S₀' : Term A B⋆) (Ts' Ss' : Cases B⋆ As), KGuarded k B T₀' ∧ KGuarded k B S₀' ∧
      Ts'.All (fun _ T => KGuarded k B T) ∧ Ss'.All (fun _ S => KGuarded k B S) ∧
      copair T₀ Ts ≡ₜ copair T₀' Ts' ∧ copair S₀ Ss ≡ₜ copair S₀' Ss' := by
  intro As
  induction As with
  | nil =>
      intro A T₀ S₀ Ts Ss hP _
      match Ts, Ss with
      | Cases.nil, Cases.nil =>
      obtain ⟨T', hT, hkT⟩ := hP.1.toKGuarded
      obtain ⟨S', hS, hkS⟩ := hP.2.toKGuarded
      exact ⟨T', S', Cases.nil, Cases.nil, hkT, hkS, trivial, trivial, hT, hS⟩
  | cons A₁ As₁ ih =>
      intro A T₀ S₀ Ts Ss hP hAll
      match Ts, Ss with
      | Cases.cons T₁ Ts₁, Cases.cons S₁ Ss₁ =>
      obtain ⟨hP₁, hAll₁⟩ := hAll
      obtain ⟨T', hT, hkT⟩ := hP.1.toKGuarded
      obtain ⟨S', hS, hkS⟩ := hP.2.toKGuarded
      obtain ⟨T₁', S₁', Ts₁', Ss₁', hkT₁, hkS₁, hkTs₁, hkSs₁, heT₁, heS₁⟩ :=
        ih T₁ S₁ Ts₁ Ss₁ hP₁ hAll₁
      exact ⟨T', S', Cases.cons T₁' Ts₁', Cases.cons S₁' Ss₁', hkT, hkS,
        ⟨hkT₁, hkTs₁⟩, ⟨hkS₁, hkSs₁⟩, Term.either_congr hT heT₁, Term.either_congr hS heS₁⟩

/-- **The induction behind value extraction.**  Two equationally simple terms on a common
input type whose output lengths differ by a constant decompose jointly into equationally
`k`-guarded components whose input types have list nesting depth at most that of the input
type.  The induction is on the input type: the shape of an equationally simple term is
determined by its input type (`Lax149335Proofs.IsSimple.shape`), and the only difficult case is the
one of a list type, which is handled by `Lax149335Proofs.homT_jointCases`. -/
theorem jointCases_of_eqSimple {B : Ty} {k : ℕ} (hk : 0 < k) :
    ∀ (A : Ty) (f g : Term A B⋆), EqSimple B f → EqSimple B g →
      (∃ delta : ℤ, ∀ x : ⟦A⟧, ((f.den x).length : ℤ) = ((g.den x).length : ℤ) + delta) →
      JointCasesD B (KGuardedPair k B) A.listDepth f g := by
  intro A
  induction A with
  | unit =>
      intro f g hf hg _
      obtain ⟨s, hs, hfs⟩ := hf
      obtain ⟨t, ht, hgt⟩ := hg
      obtain ⟨v, hv⟩ := hs.shape
      obtain ⟨v', hv'⟩ := ht.shape
      exact JointCasesD.leaf (by simp [Ty.listDepth])
        ⟨Or.inl ⟨v, hfs.trans hv⟩, Or.inl ⟨v', hgt.trans hv'⟩⟩
  | prod A₁ A₂ ih₁ ih₂ =>
      intro f g hf hg hlen
      obtain ⟨s, hs, hfs⟩ := hf
      obtain ⟨t, ht, hgt⟩ := hg
      obtain ⟨f₁, f₂, hf₁, hf₂, hfe⟩ := hs.shape
      obtain ⟨g₁, g₂, hg₁, hg₂, hge⟩ := ht.shape
      have hfe' : f ≡ₜ (f₁ ⊙ f₂) := hfs.trans hfe
      have hge' : g ≡ₜ (g₁ ⊙ g₂) := hgt.trans hge
      obtain ⟨delta, hd⟩ := hlen
      have hfd : ∀ x : ⟦A₁ ⊗ A₂⟧,
          (f.den x).length = (f₁.den x.1).length + (f₂.den x.2).length := by
        intro x
        rw [congrFun (PEq.sound hfe') x]
        simp
      have hgd : ∀ x : ⟦A₁ ⊗ A₂⟧,
          (g.den x).length = (g₁.den x.1).length + (g₂.den x.2).length := by
        intro x
        rw [congrFun (PEq.sound hge') x]
        simp
      have hkey : ∀ (x₁ : ⟦A₁⟧) (x₂ : ⟦A₂⟧),
          (((f₁.den x₁).length : ℤ) + (f₂.den x₂).length) =
            ((g₁.den x₁).length : ℤ) + (g₂.den x₂).length + delta := by
        intro x₁ x₂
        have h := hd (x₁, x₂)
        rw [hfd (x₁, x₂), hgd (x₁, x₂)] at h
        push_cast at h
        linarith
      set y₀ : ⟦A₂⟧ := Ty.someElem A₂ with hy₀
      set z₀ : ⟦A₁⟧ := Ty.someElem A₁ with hz₀
      set d₂ : ℤ := ((f₂.den y₀).length : ℤ) - ((g₂.den y₀).length : ℤ) with hd₂
      have hstep₁ : ∀ x₁ : ⟦A₁⟧,
          ((f₁.den x₁).length : ℤ) = ((g₁.den x₁).length : ℤ) + (delta - d₂) := by
        intro x₁
        have h := hkey x₁ y₀
        simp only [hd₂]
        linarith
      have hstep₂ : ∀ x₂ : ⟦A₂⟧,
          ((f₂.den x₂).length : ℤ) = ((g₂.den x₂).length : ℤ) + d₂ := by
        intro x₂
        have h := hkey z₀ x₂
        have h' := hstep₁ z₀
        simp only [hd₂] at *
        linarith
      have j₁ := ih₁ f₁ g₁ (EqSimple.of_isSimple hf₁) (EqSimple.of_isSimple hg₁)
        ⟨delta - d₂, hstep₁⟩
      have j₂ := ih₂ f₂ g₂ (EqSimple.of_isSimple hf₂) (EqSimple.of_isSimple hg₂) ⟨d₂, hstep₂⟩
      refine JointCasesD.congr hfe' hge' ?_
      refine JointCasesD.fdot_right f₂ g₂ (fun {Y} U V hY hP => ?_) j₁
      refine JointCasesD.fdot_left U V (fun {Z} T S hZ hQ => JointCasesD.leaf ?_
        ⟨KGuardedE.fdot hP.1 hQ.1, KGuardedE.fdot hP.2 hQ.2⟩) j₂
      simp only [Ty.listDepth, max_le_iff]
      exact ⟨le_trans hY (le_max_left _ _), le_trans hZ (le_max_right _ _)⟩
  | sum A₁ A₂ ih₁ ih₂ =>
      intro f g hf hg hlen
      obtain ⟨s, hs, hfs⟩ := hf
      obtain ⟨t, ht, hgt⟩ := hg
      obtain ⟨f₁, f₂, hf₁, hf₂, hfe⟩ := hs.shape
      obtain ⟨g₁, g₂, hg₁, hg₂, hge⟩ := ht.shape
      have hfe' : f ≡ₜ Term.either f₁ f₂ := hfs.trans hfe
      have hge' : g ≡ₜ Term.either g₁ g₂ := hgt.trans hge
      obtain ⟨delta, hd⟩ := hlen
      have hstep₁ : ∀ x : ⟦A₁⟧,
          ((f₁.den x).length : ℤ) = ((g₁.den x).length : ℤ) + delta := by
        intro x
        have h := hd (Sum.inl x)
        rw [congrFun (PEq.sound hfe') (Sum.inl x), congrFun (PEq.sound hge') (Sum.inl x)] at h
        simpa using h
      have hstep₂ : ∀ x : ⟦A₂⟧,
          ((f₂.den x).length : ℤ) = ((g₂.den x).length : ℤ) + delta := by
        intro x
        have h := hd (Sum.inr x)
        rw [congrFun (PEq.sound hfe') (Sum.inr x), congrFun (PEq.sound hge') (Sum.inr x)] at h
        simpa using h
      refine JointCasesD.congr hfe' hge' (JointCasesD.node ?_ ?_)
      · exact JointCasesD.mono_d (le_max_left _ _)
          (ih₁ f₁ g₁ (EqSimple.of_isSimple hf₁) (EqSimple.of_isSimple hg₁) ⟨delta, hstep₁⟩)
      · exact JointCasesD.mono_d (le_max_right _ _)
          (ih₂ f₂ g₂ (EqSimple.of_isSimple hf₂) (EqSimple.of_isSimple hg₂) ⟨delta, hstep₂⟩)
  | list A₁ ih =>
      intro f g hf hg hlen
      obtain ⟨s, hs, hfs⟩ := hf
      obtain ⟨t, ht, hgt⟩ := hg
      obtain ⟨w₀, w₁, h, hh, hfe⟩ := hs.shape
      obtain ⟨w₀', w₁', h', hh', hge⟩ := ht.shape
      have hfe' : f ≡ₜ Term.dotR (Term.dotL w₀ (homT h)) w₁ := hfs.trans hfe
      have hge' : g ≡ₜ Term.dotR (Term.dotL w₀' (homT h')) w₁' := hgt.trans hge
      obtain ⟨delta, hd⟩ := hlen
      have hfd : ∀ x : List ⟦A₁⟧, (f.den x).length =
          (w₀.den ()).length + ((x.map h.den).flatten).length + (w₁.den ()).length := by
        intro x
        rw [congrFun (PEq.sound hfe') x]
        simp only [Term.den_dotR, Term.den_dotL, Term.den_homT, List.append_eq,
          List.length_append]
      have hgd : ∀ x : List ⟦A₁⟧, (g.den x).length =
          (w₀'.den ()).length + ((x.map h'.den).flatten).length + (w₁'.den ()).length := by
        intro x
        rw [congrFun (PEq.sound hge') x]
        simp only [Term.den_dotR, Term.den_dotL, Term.den_homT, List.append_eq,
          List.length_append]
      have hkey : ∀ x : List ⟦A₁⟧,
          ((x.map h.den).flatten).length = ((x.map h'.den).flatten).length := by
        intro x
        have h0 := hd ([] : List ⟦A₁⟧)
        have hx := hd x
        rw [hfd, hgd] at h0 hx
        simp only [List.map_nil] at h0
        simp at h0
        push_cast at h0 hx
        omega
      have hstep : ∀ a : ⟦A₁⟧, ((h.den a).length : ℤ) = ((h'.den a).length : ℤ) + 0 := by
        intro a
        have := hkey [a]
        simp only [List.map_cons, List.map_nil] at this
        simp at this
        omega
      have j := ih h h' (EqSimple.of_isSimple hh) (EqSimple.of_isSimple hh') ⟨0, hstep⟩
      have j2 := JointCasesD.addRel (fun u v => u.length = v.length) j
        (fun x => by have := hstep x; omega)
      refine JointCasesD.congr hfe' hge' ?_
      exact JointCasesD.dotLR w₀ w₁ w₀' w₁'
        (fun T S hP => ⟨KGuardedE.append w₁ (KGuardedE.prepend w₀ hP.1),
          KGuardedE.append w₁' (KGuardedE.prepend w₀' hP.2)⟩)
        (homT_jointCases hk j2)

/-- **Lemma (Value extraction)** (appendix, proof of Lemma 6.4).  For `k ≥ 1` and two simple
rational terms `f, g : A → B*` that are denotationally `w`-conjugate for a value `w` of
length `k`, there is a provable isomorphism `π : C₁ + ⋯ + Cₙ → A` whose summands have at
most the list nesting depth of `A`, and such that both `π; f` and `π; g` are provably
equivalent to co-pairings of `k`-guarded terms.

This is the appendix lemma from which Lemma 6.4 below is derived; it is stated here rather
than in `Lax149335Proofs.Appendix.ConjugacyRule.Soundness` so that Lemma 6.4 can use it. -/
theorem value_extraction {A B : Ty} (f g : Term A B⋆)
    (hf : IsSimple B f) (hg : IsSimple B g) (w : Value B⋆) (hw : 0 < valLength w)
    (hconj : DenConjugate w f g) :
    ∃ (C₀ : Ty) (Cs : List Ty) (pi : Term (sumTyOf C₀ Cs) A),
      ProvableIso pi ∧
      C₀.listDepth ≤ A.listDepth ∧ (∀ C ∈ Cs, Ty.listDepth C ≤ A.listDepth) ∧
      (∃ (f₀ : Term C₀ B⋆) (fs : Cases B⋆ Cs),
        KGuarded (valLength w) B f₀ ∧ fs.All (fun _ f' => KGuarded (valLength w) B f') ∧
        (pi ⨟ f) ≡ₜ copair f₀ fs) ∧
      (∃ (g₀ : Term C₀ B⋆) (gs : Cases B⋆ Cs),
        KGuarded (valLength w) B g₀ ∧ gs.All (fun _ g' => KGuarded (valLength w) B g') ∧
        (pi ⨟ g) ≡ₜ copair g₀ gs) := by
  have hlen : ∀ x : ⟦A⟧, ((f.den x).length : ℤ) = ((g.den x).length : ℤ) + 0 := by
    intro x
    have h := congrFun hconj x
    have h' := congrArg List.length h
    simp only [Term.den_dotR, Term.den_dotL, List.append_eq, List.length_append] at h'
    omega
  have j := jointCases_of_eqSimple hw A f g (EqSimple.of_isSimple hf) (EqSimple.of_isSimple hg)
    ⟨0, hlen⟩
  obtain ⟨C₀, Cs, q, hq, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll, hT, hS⟩ := j.toCopair
  obtain ⟨T₀', S₀', Ts', Ss', hkT, hkS, hkTs, hkSs, heT, heS⟩ :=
    copair_upgrade2 T₀ S₀ Ts Ss hP hAll
  exact ⟨C₀, Cs, q, hq, hd₀, hds, ⟨T₀', Ts', hkT, hkTs, hT.trans heT⟩,
    ⟨S₀', Ss', hkS, hkSs, hS.trans heS⟩⟩

/-- **Lemma 6.4.**  In the proof of the conjugacy rule of Lemma 6.1, one can assume without
loss of generality that `f` and `g` are co-pairings `either_n f₁ ⋯ fₙ` and
`either_n g₁ ⋯ gₙ` of `k`-guarded terms, where `k` is the length of `w`.  This is formalised
as: if the conclusion of the conjugacy rule holds for all such co-pairings, then it holds for
all simple rational terms.

The reduction is the one of the paper: the value extraction lemma above supplies a provable
isomorphism `π` after which both terms become co-pairings of `k`-guarded terms, and the
conclusion is transported back along the provable isomorphism `π*` of the list types.  The
assumption that `B` is a finite alphabet is not needed for this step and has been dropped
from the statement.

The reduction moreover keeps the list nesting depth of the input type, which the proof of
Lemma 6.1 needs, so the co-pairings may be assumed to have an input type of list nesting
depth at most that of `A`. -/
theorem wlog_kguarded {B : Ty} (w : Value B⋆)
    (hw : 0 < valLength w)
    {A : Ty}
    (H : ∀ (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As),
      (sumTyOf A₀ As).listDepth ≤ A.listDepth →
      KGuarded (valLength w) B f₀ → KGuarded (valLength w) B g₀ →
      fs.All (fun _ f => KGuarded (valLength w) B f) →
      gs.All (fun _ g => KGuarded (valLength w) B g) →
      dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs) →
      dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs)))
    (f g : Term A B⋆) (hf : IsSimple B f) (hg : IsSimple B g)
    (hfg : dotR f w ≡ₜ dotL w g) :
    dotR (homT f) w ≡ₜ dotL w (homT g) := by
  obtain ⟨C₀, Cs, pi, ⟨pi', -, hpi'⟩, hd₀, hds, ⟨f₀, fs, hkf, hkfs, heqf⟩,
      ⟨g₀, gs, hkg, hkgs, heqg⟩⟩ :=
    value_extraction f g hf hg w hw (PEq.sound hfg)
  -- after `π` the two terms are co-pairings of `k`-guarded terms, and they are still
  -- provably `w`-conjugate
  have hconj : dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs) :=
    (Term.dotR_congr (PEq.symm heqf) (PEq.refl _)).trans
      ((Term.conj_precomp pi f g w hfg).trans (Term.dotL_congr (PEq.refl _) heqg))
  have hH := H C₀ Cs f₀ g₀ fs gs (sumTyOf_listDepth_le C₀ Cs hd₀ hds) hkf hkg hkfs hkgs
    hconj
  -- the homomorphism of a pre-composition is a pre-composition of the homomorphism
  have hFf : homT (copair f₀ fs) ≡ₜ (Term.listF pi ⨟ homT f) :=
    (Term.homT_congr (PEq.symm heqf)).trans (Term.homT_precomp pi f)
  have hFg : homT (copair g₀ gs) ≡ₜ (Term.listF pi ⨟ homT g) :=
    (Term.homT_congr (PEq.symm heqg)).trans (Term.homT_precomp pi g)
  have h2 : dotR (Term.listF pi ⨟ homT f) w ≡ₜ dotL w (Term.listF pi ⨟ homT g) :=
    (Term.dotR_congr (PEq.symm hFf) (PEq.refl _)).trans
      (hH.trans (Term.dotL_congr (PEq.refl _) hFg))
  -- pre-composing with the inverse isomorphism cancels `π*`
  have h3 := Term.conj_precomp (Term.listF pi') _ _ w h2
  have hcancel : ∀ F : Term (A⋆) (B⋆),
      (Term.listF pi' ⨟ (Term.listF pi ⨟ F)) ≡ₜ F := by
    intro F
    calc (Term.listF pi' ⨟ (Term.listF pi ⨟ F))
        ≡ₜ ((Term.listF pi' ⨟ Term.listF pi) ⨟ F) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.listF (pi' ⨟ pi) ⨟ F) := PEq.compL _ (PEq.list_comp _ _)
      _ ≡ₜ (Term.listF (Term.id A) ⨟ F) := PEq.compL _ (PEq.congr_listF hpi')
      _ ≡ₜ (Term.id (A⋆) ⨟ F) := PEq.compL _ (PEq.list_id A)
      _ ≡ₜ F := PEq.id_comp _
  exact ((Term.dotR_congr (PEq.symm (hcancel (homT f))) (PEq.refl _)).trans h3).trans
    (Term.dotL_congr (PEq.refl _) (hcancel (homT g)))

end Lax149335Proofs

bridge_export Lax149335Proofs
