import Lax149335Proofs.Appendix.Bundles.Composition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-!
# Bundles of bundles, for the injectivity half of the bundle lemma

`Lax149335Proofs.Appendix.Bundles.Composition` shows that the bundle lemma (Lemma 6.7) is
multiplicative in the bundle size: bundles of bundles are bundles.  Exactly the same
composition works for the *injectivity half* of the bundle lemma alone, because provably
injective terms enjoy the same closure properties as provable isomorphisms.

This file repeats the development of `ContIso` and `BundleIso` with provable isomorphisms
replaced by provably injective terms, so that the injectivity half of Lemma 6.7 for the
bundle size two (`Lax149335Proofs.BundleTwo.bundle_two_injective`, proved in
`Lax149335Proofs.Appendix.Bundles.BundleTwo`) yields the injectivity half for arbitrarily large bundle
sizes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- A provably injective term between two types equipped with maps into `A*`, which commutes
with those two maps. -/
def ContInj {A X Y : Ty} (cX : Term X A⋆) (cY : Term Y A⋆) : Prop :=
  ∃ h : Term X Y, ProvablyInjective h ∧ (h ⨟ cY) ≡ₜ cX

namespace ContInj

variable {A X Y Z : Ty}

theorem refl (cX : Term X A⋆) : ContInj cX cX :=
  ⟨Term.id X, ProvablyInjective.id X, PEq.id_comp _⟩

/-- A content-preserving isomorphism is in particular a content-preserving injection. -/
theorem of_contIso {cX : Term X A⋆} {cY : Term Y A⋆} (h : ContIso cX cY) : ContInj cX cY := by
  obtain ⟨u, ⟨u', hu, _⟩, hue⟩ := h
  exact ⟨u, ⟨u', hu⟩, hue⟩

/-- A provably injective term is a content-preserving injection into its codomain, with the
identity as the content map there. -/
theorem of_provablyInjective {c : Term X A⋆} (h : ProvablyInjective c) :
    ContInj c (Term.id A⋆) :=
  ⟨c, h, PEq.comp_id _⟩

theorem toProvablyInjective {c : Term X A⋆} (h : ContInj c (Term.id A⋆)) :
    ProvablyInjective c := by
  obtain ⟨u, hu, he⟩ := h
  exact ProvablyInjective.of_peq (PEq.symm ((PEq.comp_id u).symm.trans he)) hu

theorem trans {cX : Term X A⋆} {cY : Term Y A⋆} {cZ : Term Z A⋆}
    (h₁ : ContInj cX cY) (h₂ : ContInj cY cZ) : ContInj cX cZ := by
  obtain ⟨u, hu, hue⟩ := h₁
  obtain ⟨v, hv, hve⟩ := h₂
  refine ⟨u ⨟ v, ProvablyInjective.comp hu hv, ?_⟩
  calc ((u ⨟ v) ⨟ cZ) ≡ₜ (u ⨟ (v ⨟ cZ)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (u ⨟ cY) := PEq.compR _ hve
    _ ≡ₜ cX := hue

/-- The right-hand content map may be replaced by a provably equivalent one. -/
theorem congrR {cX : Term X A⋆} {cY cY' : Term Y A⋆} (h : cY ≡ₜ cY') (hc : ContInj cX cY) :
    ContInj cX cY' := by
  obtain ⟨u, hu, hue⟩ := hc
  exact ⟨u, hu, (PEq.compR _ (PEq.symm h)).trans hue⟩

theorem prod {X₁ X₂ Y₁ Y₂ : Ty} {c₁ : Term X₁ A⋆} {c₂ : Term X₂ A⋆}
    {d₁ : Term Y₁ A⋆} {d₂ : Term Y₂ A⋆} (h₁ : ContInj c₁ d₁) (h₂ : ContInj c₂ d₂) :
    ContInj (c₁ ⊙ c₂) (d₁ ⊙ d₂) := by
  obtain ⟨u, hu, hue⟩ := h₁
  obtain ⟨v, hv, hve⟩ := h₂
  refine ⟨Term.prodF u v, ProvablyInjective.prodF hu hv, ?_⟩
  calc (Term.prodF u v ⨟ (Term.prodF d₁ d₂ ⨟ binconcat A))
      ≡ₜ ((Term.prodF u v ⨟ Term.prodF d₁ d₂) ⨟ binconcat A) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.prodF (u ⨟ d₁) (v ⨟ d₂) ⨟ binconcat A) := PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.prodF c₁ c₂ ⨟ binconcat A) := PEq.compL _ (PEq.congr_prodF hue hve)

end ContInj

/-! ### The injectivity half of the bundle lemma, and bundles of bundles -/

/-- The injectivity half of the bundle lemma for the bundle size `k+1`: for every type `A`
the concatenation map `(A^{k+1})* × A^{<k+1} ↣ A*` is provably injective. -/
def BundleInj (k : ℕ) : Prop :=
  ∀ A : Ty, ProvablyInjective (TyF.concatMap (TyF.bundle k) A)

/-- **Bundles of bundles, for the injectivity half.**  If the concatenation maps of the
bundle sizes `m+1` and `n+1` are provably injective, then so is the concatenation map of the
bundle size `(m+1)(n+1)`.  The proof is the one of `Lax149335Proofs.BundleIso.mul`: all the steps
except the two uses of the hypotheses are provable isomorphisms. -/
theorem BundleInj.mul {m n : ℕ} (hm : BundleInj m) (hn : BundleInj n) :
    BundleInj ((m + 1) * n + m) := by
  intro A
  set P : Ty := (TyF.pow (m + 1)).app A with hP
  set cP : Term P A⋆ := TyF.concatMap (TyF.pow (m + 1)) A with hcP
  have hmul : ((m + 1) * n + m) + 1 = (m + 1) * (n + 1) := by
    rw [Nat.mul_succ]; omega
  -- Step 1: a list of `(m+1)(n+1)`-bundles is a list of `(n+1)`-bundles of `(m+1)`-bundles,
  -- and the tail splits accordingly
  have step1 :
      ContInj (TyF.concatMap (TyF.bundle ((m + 1) * n + m)) A)
        (TyF.concatMap
          (.prod (.prod (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n))
            (TyF.lt m)) A) :=
    ContInj.of_contIso (ContIso.of_riso
      ((Term.RIso.prod
          (Term.RIso.list
            ((Term.powCastRIso A hmul).trans (Term.powCompRIso A (m + 1) (n + 1))))
          (Term.ltCompRIso A m n)).trans
        ((Term.assocRRIso A (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n)
          (TyF.lt m)).symm)))
  -- Step 2: the contents of the inner shapes are computed over the base type `P`
  have step2 :
      ContInj
        (TyF.concatMap
          (.prod (.prod (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n))
            (TyF.lt m)) A)
        (((homT (TyF.concatMap (TyF.pow (n + 1)) P ⨟ homT cP)) ⊙
            (TyF.concatMap (TyF.lt n) P ⨟ homT cP)) ⊙ TyF.concatMap (TyF.lt m) A) :=
    ContInj.of_contIso
      (ContIso.prod
        (ContIso.prod (ContIso.list (contIso_powComp A (m + 1) (n + 1)))
          (contIso_ltComp A (m + 1) n))
        (ContIso.refl (TyF.concatMap (TyF.lt m) A)))
  -- Step 3: the first factor is the concatenation map of the `(n+1)`-bundles over `P`
  have step3 :
      (((homT (TyF.concatMap (TyF.pow (n + 1)) P ⨟ homT cP)) ⊙
          (TyF.concatMap (TyF.lt n) P ⨟ homT cP)) ⊙ TyF.concatMap (TyF.lt m) A) ≡ₜ
        ((TyF.concatMap (TyF.bundle n) P ⨟ homT cP) ⊙ TyF.concatMap (TyF.lt m) A) := by
    refine fdot_congr ?_ (PEq.refl _)
    show _ ≡ₜ ((homT (TyF.concatMap (TyF.pow (n + 1)) P) ⊙ TyF.concatMap (TyF.lt n) P) ⨟
      homT cP)
    exact PEq.symm ((fdot_comp_homT _ _ _).trans
      (fdot_congr (homT_comp _ _) (PEq.refl _)))
  -- Step 4: the inner bundle injection, and then the outer one
  have step4 :
      ContInj ((TyF.concatMap (TyF.bundle n) P ⨟ homT cP) ⊙ TyF.concatMap (TyF.lt m) A)
        (TyF.concatMap (TyF.bundle m) A) :=
    ContInj.prod ⟨TyF.concatMap (TyF.bundle n) P, hn P, PEq.refl _⟩
      (ContInj.refl (TyF.concatMap (TyF.lt m) A))
  exact ContInj.toProvablyInjective
    ((step1.trans ((step2.trans (ContInj.congrR step3 (ContInj.refl _))).trans step4)).trans
      (ContInj.of_provablyInjective (hm A)))

/-- Doubling the bundle size, for the injectivity half. -/
theorem BundleInj.double {k : ℕ} (hk : BundleInj k) (h₂ : BundleInj 1) :
    BundleInj (2 * k + 1) := by
  have h := hk.mul h₂
  have he : (k + 1) * 1 + k = 2 * k + 1 := by omega
  rwa [he] at h

/-- The injectivity half for the bundle size `2` gives the injectivity half for all the
bundle sizes `2ʲ⁺¹`. -/
theorem BundleInj.two_pow (h₂ : BundleInj 1) : (j : ℕ) → BundleInj (2 ^ (j + 1) - 1)
  | 0 => by simpa using h₂
  | (j + 1) => by
      have h := (BundleInj.two_pow h₂ j).double h₂
      have hp : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
      have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
      have he : 2 * (2 ^ (j + 1) - 1) + 1 = 2 ^ (j + 1 + 1) - 1 := by omega
      rwa [he] at h

end Lax149335Proofs

bridge_export Lax149335Proofs
