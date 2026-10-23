import Lax149335Proofs.Appendix.Guarded.FixedLengths
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-!
# Bundles of bundles (Lemma 6.7 for composite bundle sizes)

The bundle lemma (Lemma 6.7) states that for every bundle size `k ≥ 1` the concatenation map

```
(Aᵏ)* × A^{<k}  ↣  A*
```

is a provable isomorphism.  The appendix only proves this for `k = 2`; the general case is
left to the reader.  This file proves that the property is *multiplicative* in the bundle
size: if it holds for the sizes `M` and `N` then it holds for the size `M · N`, by grouping
a list into bundles of size `M` and then grouping the bundles into bundles of `N` bundles.
In particular the case `k = 2` gives all bundle sizes `2ʲ`, hence bundle isomorphisms of
arbitrarily large size, which is all that the proof of Lemma 6.1 uses.

The main results are

* `Lax149335Proofs.BundleIso`, the property "the concatenation map for bundles of size `k+1` is a
  provable isomorphism", i.e. the statement of Lemma 6.7 for that bundle size;
* `Lax149335Proofs.BundleIso.mul`, the multiplicativity of that property;
* `Lax149335Proofs.BundleIso.two_pow` and `Lax149335Proofs.BundleIso.arbitrarily_large`, its consequences
  for the sizes `2ʲ`.

The proof is a chain of *content-preserving isomorphisms* (`Lax149335Proofs.ContIso`, a version of
`Lax149335Proofs.Term.RIso` indexed by the concatenation maps themselves rather than by the shapes,
which is what makes it possible to change the base type in the middle of the chain).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Closure properties of provable isomorphisms -/

namespace ProvableIso

theorem id (A : Ty) : ProvableIso (Term.id A) :=
  ⟨Term.id A, PEq.comp_id _, PEq.comp_id _⟩

theorem of_peq {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) (hg : ProvableIso g) :
    ProvableIso f := by
  obtain ⟨g', h₁, h₂⟩ := hg
  exact ⟨g', (PEq.compL _ h).trans h₁, (PEq.compR _ h).trans h₂⟩

theorem comp {A B C : Ty} {f : Term A B} {g : Term B C}
    (hf : ProvableIso f) (hg : ProvableIso g) : ProvableIso (f ⨟ g) := by
  obtain ⟨f', hf₁, hf₂⟩ := hf
  obtain ⟨g', hg₁, hg₂⟩ := hg
  refine ⟨g' ⨟ f', ?_, ?_⟩
  · calc ((f ⨟ g) ⨟ (g' ⨟ f'))
        ≡ₜ (f ⨟ (g ⨟ (g' ⨟ f'))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (f ⨟ ((g ⨟ g') ⨟ f')) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (f ⨟ (Term.id B ⨟ f')) := PEq.compR _ (PEq.compL _ hg₁)
      _ ≡ₜ (f ⨟ f') := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := hf₁
  · calc ((g' ⨟ f') ⨟ (f ⨟ g))
        ≡ₜ (g' ⨟ (f' ⨟ (f ⨟ g))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (g' ⨟ ((f' ⨟ f) ⨟ g)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (g' ⨟ (Term.id B ⨟ g)) := PEq.compR _ (PEq.compL _ hf₂)
      _ ≡ₜ (g' ⨟ g) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id C := hg₂

theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : ProvableIso f) (hg : ProvableIso g) : ProvableIso (Term.prodF f g) := by
  obtain ⟨f', hf₁, hf₂⟩ := hf
  obtain ⟨g', hg₁, hg₂⟩ := hg
  exact ⟨Term.prodF f' g',
    (PEq.prod_comp _ _ _ _).trans ((PEq.congr_prodF hf₁ hg₁).trans (PEq.prod_id _ _)),
    (PEq.prod_comp _ _ _ _).trans ((PEq.congr_prodF hf₂ hg₂).trans (PEq.prod_id _ _))⟩

theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : ProvableIso f) (hg : ProvableIso g) : ProvableIso (Term.sumF f g) := by
  obtain ⟨f', hf₁, hf₂⟩ := hf
  obtain ⟨g', hg₁, hg₂⟩ := hg
  exact ⟨Term.sumF f' g',
    (PEq.sum_comp _ _ _ _).trans ((PEq.congr_sumF hf₁ hg₁).trans (PEq.sum_id _ _)),
    (PEq.sum_comp _ _ _ _).trans ((PEq.congr_sumF hf₂ hg₂).trans (PEq.sum_id _ _))⟩

theorem listF {A B : Ty} {f : Term A B} (hf : ProvableIso f) : ProvableIso (Term.listF f) := by
  obtain ⟨f', hf₁, hf₂⟩ := hf
  exact ⟨Term.listF f',
    (PEq.list_comp _ _).trans ((PEq.congr_listF hf₁).trans (PEq.list_id _)),
    (PEq.list_comp _ _).trans ((PEq.congr_listF hf₂).trans (PEq.list_id _))⟩

end ProvableIso

/-! ### Content-preserving isomorphisms

The isomorphisms of `Lax149335Proofs.Term.RIso` are indexed by two *shapes* over a common base type.
In the proof below the base type changes in the middle of the chain (from `A` to `Aᴹ`), so we
use the following variant, which is indexed by the two concatenation maps themselves. -/

/-- A provable isomorphism between two types equipped with maps into `A*`, which commutes
with those two maps. -/
def ContIso {A X Y : Ty} (cX : Term X A⋆) (cY : Term Y A⋆) : Prop :=
  ∃ h : Term X Y, ProvableIso h ∧ (h ⨟ cY) ≡ₜ cX

namespace ContIso

variable {A X Y Z : Ty}

theorem refl (cX : Term X A⋆) : ContIso cX cX :=
  ⟨Term.id X, ProvableIso.id X, PEq.id_comp _⟩

/-- A term that is a provable isomorphism is a content-preserving isomorphism onto its
codomain, with the identity as the content map there. -/
theorem of_provableIso {c : Term X A⋆} (h : ProvableIso c) : ContIso c (Term.id A⋆) :=
  ⟨c, h, PEq.comp_id _⟩

theorem toProvableIso {c : Term X A⋆} (h : ContIso c (Term.id A⋆)) : ProvableIso c := by
  obtain ⟨u, hu, he⟩ := h
  exact ProvableIso.of_peq (PEq.symm ((PEq.comp_id u).symm.trans he)) hu

theorem trans {cX : Term X A⋆} {cY : Term Y A⋆} {cZ : Term Z A⋆}
    (h₁ : ContIso cX cY) (h₂ : ContIso cY cZ) : ContIso cX cZ := by
  obtain ⟨u, hu, hue⟩ := h₁
  obtain ⟨v, hv, hve⟩ := h₂
  refine ⟨u ⨟ v, ProvableIso.comp hu hv, ?_⟩
  calc ((u ⨟ v) ⨟ cZ) ≡ₜ (u ⨟ (v ⨟ cZ)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (u ⨟ cY) := PEq.compR _ hve
    _ ≡ₜ cX := hue

/-- The right-hand content map may be replaced by a provably equivalent one. -/
theorem congrR {cX : Term X A⋆} {cY cY' : Term Y A⋆} (h : cY ≡ₜ cY') (hc : ContIso cX cY) :
    ContIso cX cY' := by
  obtain ⟨u, hu, hue⟩ := hc
  exact ⟨u, hu, (PEq.compR _ (PEq.symm h)).trans hue⟩

theorem prod {X₁ X₂ Y₁ Y₂ : Ty} {c₁ : Term X₁ A⋆} {c₂ : Term X₂ A⋆}
    {d₁ : Term Y₁ A⋆} {d₂ : Term Y₂ A⋆} (h₁ : ContIso c₁ d₁) (h₂ : ContIso c₂ d₂) :
    ContIso (c₁ ⊙ c₂) (d₁ ⊙ d₂) := by
  obtain ⟨u, hu, hue⟩ := h₁
  obtain ⟨v, hv, hve⟩ := h₂
  refine ⟨Term.prodF u v, ProvableIso.prodF hu hv, ?_⟩
  calc (Term.prodF u v ⨟ (Term.prodF d₁ d₂ ⨟ binconcat A))
      ≡ₜ ((Term.prodF u v ⨟ Term.prodF d₁ d₂) ⨟ binconcat A) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.prodF (u ⨟ d₁) (v ⨟ d₂) ⨟ binconcat A) := PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.prodF c₁ c₂ ⨟ binconcat A) := PEq.compL _ (PEq.congr_prodF hue hve)

theorem sum {X₁ X₂ Y₁ Y₂ : Ty} {c₁ : Term X₁ A⋆} {c₂ : Term X₂ A⋆}
    {d₁ : Term Y₁ A⋆} {d₂ : Term Y₂ A⋆} (h₁ : ContIso c₁ d₁) (h₂ : ContIso c₂ d₂) :
    ContIso (either c₁ c₂) (either d₁ d₂) := by
  obtain ⟨u, hu, hue⟩ := h₁
  obtain ⟨v, hv, hve⟩ := h₂
  exact ⟨Term.sumF u v, ProvableIso.sumF hu hv,
    (sumF_either _ _ _ _).trans (either_congr hue hve)⟩

theorem list {c : Term X A⋆} {d : Term Y A⋆} (h : ContIso c d) : ContIso (homT c) (homT d) := by
  obtain ⟨u, hu, hue⟩ := h
  exact ⟨Term.listF u, ProvableIso.listF hu,
    (PEq.symm (homT_precomp _ _)).trans (homT_congr hue)⟩

/-- Every isomorphism of shapes that commutes with the concatenation maps is a
content-preserving isomorphism. -/
theorem of_riso {C : Ty} {F G : TyF} (e : Term.RIso C F G) :
    ContIso (F.concatMap C) (G.concatMap C) :=
  ⟨e.fwd, ⟨e.bwd, e.fwd_bwd, e.bwd_fwd⟩, e.rebr⟩

end ContIso

/-! ### The shapes of bundles of bundles -/

/-- The shape `A ↦ (Aᴹ)ᴺ`, i.e. the `N`-fold power of the `M`-fold power. -/
def TyF.powComp (M : ℕ) : ℕ → TyF
  | 0 => .unit
  | (N + 1) => .prod (TyF.pow M) (TyF.powComp M N)

/-- The shape `A ↦ (Aᴹ)⁰ + ⋯ + (Aᴹ)ᴺ`, i.e. `TyF.lt N` with the parameter replaced by the
`M`-fold power. -/
def TyF.ltComp (M : ℕ) : ℕ → TyF
  | 0 => .unit
  | (N + 1) => .sum (TyF.ltComp M N) (TyF.powComp M (N + 1))

/-- The shape of the bundles of size `k+1`: a list of bundles, followed by a tail of length
at most `k`. -/
def TyF.bundle (k : ℕ) : TyF := .prod (.list (TyF.pow (k + 1))) (TyF.lt k)

namespace Term

/-- Transport of an isomorphism of powers along an equality of exponents. -/
def powCastRIso (C : Ty) {i j : ℕ} (h : i = j) : RIso C (TyF.pow i) (TyF.pow j) := by
  subst h; exact RIso.refl C (TyF.pow i)

/-- Transport of an isomorphism of bounded powers along an equality of bounds. -/
def ltCastRIso (C : Ty) {i j : ℕ} (h : i = j) : RIso C (TyF.lt i) (TyF.lt j) := by
  subst h; exact RIso.refl C (TyF.lt i)

/-- Splitting a power in two: `A^{j+i} ≅ Aⁱ × Aʲ`. -/
def powAddRIso (C : Ty) : (i j : ℕ) →
    RIso C (TyF.pow (j + i)) (.prod (TyF.pow i) (TyF.pow j))
  | 0, j => unitLRIso C (TyF.pow j)
  | (i + 1), j =>
      (RIso.prod (RIso.refl C TyF.param) (powAddRIso C i j)).trans
        ((assocRRIso C TyF.param (TyF.pow i) (TyF.pow j)).symm)

/-- A power of a power is a power: `(Aᴹ)ᴺ ≅ A^{M·N}`. -/
def powCompRIso (C : Ty) (M : ℕ) : (N : ℕ) →
    RIso C (TyF.pow (M * N)) (TyF.powComp M N)
  | 0 => RIso.refl C TyF.unit
  | (N + 1) =>
      (powAddRIso C M (M * N)).trans
        (RIso.prod (RIso.refl C (TyF.pow M)) (powCompRIso C M N))

/-- Splitting the bounded powers: `A^{≤ d+m+1} ≅ A^{≤ d} + A^{d+1} × A^{≤ m}`. -/
def ltSplitRIso (C : Ty) (d : ℕ) : (m : ℕ) →
    RIso C (TyF.lt (d + m + 1)) (.sum (TyF.lt d) (.prod (TyF.pow (d + 1)) (TyF.lt m)))
  | 0 => RIso.sum (RIso.refl C (TyF.lt d)) (unitRRIso C (TyF.pow (d + 1)))
  | (m + 1) => by
      have hpow : d + (m + 1) + 1 = (m + 1) + (d + 1) := by omega
      exact
        ((RIso.sum (ltSplitRIso C d m) (RIso.refl C (TyF.pow (d + (m + 1) + 1)))).trans
          ((sumAssocRIso C (TyF.lt d) (.prod (TyF.pow (d + 1)) (TyF.lt m))
              (TyF.pow (d + (m + 1) + 1))).trans
            (RIso.sum (RIso.refl C (TyF.lt d))
              (RIso.sum (RIso.refl C (.prod (TyF.pow (d + 1)) (TyF.lt m)))
                ((powCastRIso C hpow).trans (powAddRIso C (d + 1) (m + 1))))))).trans
          (RIso.sum (RIso.refl C (TyF.lt d))
            ((distRRIso C (TyF.pow (d + 1)) (TyF.lt m) (TyF.pow (m + 1))).symm))

/-- Bundles of bundles, on the tail: `A^{≤ (m+1)·n+m} ≅ (A^{m+1})^{≤ n} × A^{≤ m}`. -/
def ltCompRIso (C : Ty) (m : ℕ) : (n : ℕ) →
    RIso C (TyF.lt ((m + 1) * n + m)) (.prod (TyF.ltComp (m + 1) n) (TyF.lt m))
  | 0 => (ltCastRIso C (by omega : (m + 1) * 0 + m = m)).trans (unitLRIso C (TyF.lt m))
  | (n + 1) => by
      have h₁ : (m + 1) * (n + 1) + m = ((m + 1) * n + m) + m + 1 := by
        rw [Nat.mul_succ]; omega
      have h₂ : ((m + 1) * n + m) + 1 = (m + 1) * (n + 1) := by
        rw [Nat.mul_succ]; omega
      exact
        ((ltCastRIso C h₁).trans (ltSplitRIso C ((m + 1) * n + m) m)).trans
          (((RIso.sum (ltCompRIso C m n)
              (RIso.prod ((powCastRIso C h₂).trans (powCompRIso C (m + 1) (n + 1)))
                (RIso.refl C (TyF.lt m)))).trans
            ((distLRIso C (TyF.ltComp (m + 1) n) (TyF.powComp (m + 1) (n + 1))
              (TyF.lt m)).symm)))

end Term

/-! ### Changing the base type

The two lemmas that compare the concatenation map of a shape over the base type `A` with the
concatenation map of the corresponding shape over the base type `Aᴹ`, followed by the
concatenation map of `Aᴹ` extended to lists. -/

/-- The content of `(Aᴹ)ᴺ` is the content of the `N`-th power of `Aᴹ`, followed by the
homomorphic extension of the content of `Aᴹ`. -/
theorem contIso_powComp (A : Ty) (M : ℕ) : (N : ℕ) →
    ContIso (TyF.concatMap (TyF.powComp M N) A)
      (TyF.concatMap (TyF.pow N) ((TyF.pow M).app A) ⨟
        homT (TyF.concatMap (TyF.pow M) A))
  | 0 => ContIso.congrR (PEq.symm (homT_nil (TyF.concatMap (TyF.pow M) A)))
      (ContIso.refl (nilT A))
  | (N + 1) => by
    have hstep :
        ((TyF.concatMap (TyF.pow M) A) ⊙
            (TyF.concatMap (TyF.pow N) ((TyF.pow M).app A) ⨟
              homT (TyF.concatMap (TyF.pow M) A))) ≡ₜ
          (TyF.concatMap (TyF.pow (N + 1)) ((TyF.pow M).app A) ⨟
            homT (TyF.concatMap (TyF.pow M) A)) := by
      refine PEq.symm (((fdot_comp_homT _ _ _).trans ?_))
      exact fdot_congr (homT_pure _) (PEq.refl _)
    exact ContIso.congrR hstep
      (ContIso.prod (ContIso.refl (TyF.concatMap (TyF.pow M) A)) (contIso_powComp A M N))

/-- The same for the bounded powers. -/
theorem contIso_ltComp (A : Ty) (M : ℕ) : (N : ℕ) →
    ContIso (TyF.concatMap (TyF.ltComp M N) A)
      (TyF.concatMap (TyF.lt N) ((TyF.pow M).app A) ⨟
        homT (TyF.concatMap (TyF.pow M) A))
  | 0 => ContIso.congrR (PEq.symm (homT_nil (TyF.concatMap (TyF.pow M) A)))
      (ContIso.refl (nilT A))
  | (N + 1) =>
    ContIso.congrR (PEq.symm (either_comp _ _ _))
      (ContIso.sum (contIso_ltComp A M N) (contIso_powComp A M (N + 1)))

/-! ### The bundle lemma for composite bundle sizes -/

/-- **Lemma 6.7** for the bundle size `k+1`: the concatenation map
`(A^{k+1})* × A^{<k+1} ↣ A*` is a provable isomorphism, for every type `A`. -/
def BundleIso (k : ℕ) : Prop :=
  ∀ A : Ty, ProvableIso (TyF.concatMap (TyF.bundle k) A)

/-- **Bundles of bundles.**  The bundle lemma is multiplicative in the bundle size: if it
holds for the bundle sizes `m+1` and `n+1`, then it holds for their product, because a list
can be grouped into bundles of size `m+1` and those bundles can then themselves be grouped
into bundles of `n+1` bundles.

The resulting bundle size is `(m+1)·(n+1)`, i.e. the index of the conclusion is
`(m+1)·n + m`. -/
theorem BundleIso.mul {m n : ℕ} (hm : BundleIso m) (hn : BundleIso n) :
    BundleIso ((m + 1) * n + m) := by
  intro A
  -- the base type of the inner bundles
  set P : Ty := (TyF.pow (m + 1)).app A with hP
  set cP : Term P A⋆ := TyF.concatMap (TyF.pow (m + 1)) A with hcP
  have hmul : ((m + 1) * n + m) + 1 = (m + 1) * (n + 1) := by
    rw [Nat.mul_succ]; omega
  -- Step 1: a list of `(m+1)(n+1)`-bundles is a list of `(n+1)`-bundles of `(m+1)`-bundles,
  -- and the tail splits accordingly
  have step1 :
      ContIso (TyF.concatMap (TyF.bundle ((m + 1) * n + m)) A)
        (TyF.concatMap
          (.prod (.prod (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n))
            (TyF.lt m)) A) :=
    ContIso.of_riso
      ((Term.RIso.prod
          (Term.RIso.list
            ((Term.powCastRIso A hmul).trans (Term.powCompRIso A (m + 1) (n + 1))))
          (Term.ltCompRIso A m n)).trans
        ((Term.assocRRIso A (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n)
          (TyF.lt m)).symm))
  -- Step 2: the contents of the inner shapes are computed over the base type `P`
  have step2 :
      ContIso
        (TyF.concatMap
          (.prod (.prod (.list (TyF.powComp (m + 1) (n + 1))) (TyF.ltComp (m + 1) n))
            (TyF.lt m)) A)
        (((homT (TyF.concatMap (TyF.pow (n + 1)) P ⨟ homT cP)) ⊙
            (TyF.concatMap (TyF.lt n) P ⨟ homT cP)) ⊙ TyF.concatMap (TyF.lt m) A) :=
    ContIso.prod
      (ContIso.prod (ContIso.list (contIso_powComp A (m + 1) (n + 1)))
        (contIso_ltComp A (m + 1) n))
      (ContIso.refl (TyF.concatMap (TyF.lt m) A))
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
  -- Step 4: the inner bundle isomorphism, and then the outer one
  have step4 :
      ContIso ((TyF.concatMap (TyF.bundle n) P ⨟ homT cP) ⊙ TyF.concatMap (TyF.lt m) A)
        (TyF.concatMap (TyF.bundle m) A) :=
    ContIso.prod ⟨TyF.concatMap (TyF.bundle n) P, hn P, PEq.refl _⟩
      (ContIso.refl (TyF.concatMap (TyF.lt m) A))
  exact ContIso.toProvableIso
    ((step1.trans ((step2.trans (ContIso.congrR step3 (ContIso.refl _))).trans step4)).trans
      (ContIso.of_provableIso (hm A)))

/-- Doubling the bundle size: bundles of two bundles. -/
theorem BundleIso.double {k : ℕ} (hk : BundleIso k) (h₂ : BundleIso 1) :
    BundleIso (2 * k + 1) := by
  have h := hk.mul h₂
  have he : (k + 1) * 1 + k = 2 * k + 1 := by omega
  rwa [he] at h

/-- The bundle lemma for the bundle size `2` gives the bundle lemma for all the bundle sizes
`2ʲ⁺¹`, by iterating the construction of bundles of bundles. -/
theorem BundleIso.two_pow (h₂ : BundleIso 1) : (j : ℕ) → BundleIso (2 ^ (j + 1) - 1)
  | 0 => by simpa using h₂
  | (j + 1) => by
      have h := (BundleIso.two_pow h₂ j).double h₂
      have hp : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
      have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
      have he : 2 * (2 ^ (j + 1) - 1) + 1 = 2 ^ (j + 1 + 1) - 1 := by omega
      rwa [he] at h

/-- The bundle lemma holds for arbitrarily large bundle sizes as soon as it holds for the
bundle size `2`.  This is all that the proof of Lemma 6.1 uses. -/
theorem BundleIso.arbitrarily_large (h₂ : BundleIso 1) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ BundleIso k := by
  refine ⟨2 ^ (N + 1) - 1, ?_, BundleIso.two_pow h₂ N⟩
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have hp : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
  omega

end Lax149335Proofs

bridge_export Lax149335Proofs
