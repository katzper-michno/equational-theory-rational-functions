import Lax149335Proofs.Appendix.Groups.ComponentWiseExchange

/-!
# The group exchange lemma, in its inverted form: the induction

This file completes the proof of the **inverted group exchange lemma**
`Lax149335Proofs.group_exchange_inv` of the appendix section *Completeness in the presence
of groups*.  It is separated from `Lax149335Proofs.Appendix.Groups.Exchange`, which sets up
the predicate `Lax149335Proofs.IsGExch` and the functorial cases, only because the induction uses
the prefix exchange lemma (`Lax149335Proofs.prefix_exchange_group`), whose proof takes up the whole
of `Lax149335Proofs.Appendix.Groups.PrefixExchange`,
`Lax149335Proofs.Appendix.Groups.StarConsolidation` and
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`.

The induction is on the definition of a group-lift pair (`Lax149335Proofs.IsGLiftPair`):

* for a prime lift, the aperiodic exchange lemma (Lemma 7.5) does the job, after which the
  new lift is inverted using Lemma 7.2;
* for a group injection, the composition of the drop with the group injection is an
  aperiodic term, so the aperiodic lift-drop factorisation (Lemma 7.3) applies to it, and
  inverting the lift (Lemma 7.2) gives the required square;
* for a Simon lift, the drop is first pushed past the group prefix multiplication by the
  prefix exchange lemma, and then past the lift of the Simon lift by the aperiodic exchange
  lemma;
* the composition case chains the two induction hypotheses, and the three functorial cases
  are handled by the normalisation lemmas for drops with a product, a co-product and a list
  codomain, exactly as in the aperiodic case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The group exchange lemma -/

/-- The induction underlying the inverted group exchange lemma. -/
theorem group_exchange_inv_aux : ∀ {B D : Ty} {mu : Term B D} {pi : Term D B},
    IsGLiftPair mu pi → ∀ {A : Ty} {f : Term A B}, IsDrop f → IsGExch f pi := by
  intro B D mu pi hp
  induction hp with
  | @ofLift B D l d hlift hdrop hld =>
      intro A f hf
      obtain ⟨E, l', d', hl', hd', he⟩ := exchange f l hf hlift
      obtain ⟨l'', hl'', h₁, h₂⟩ := lift_iso l' hl'
      refine ⟨E, l', l'', d', .ofLift hl' hl'' h₁, hd', ?_⟩
      calc (l'' ⨟ f) ≡ₜ (l'' ⨟ (f ⨟ Term.id B)) := PEq.compR _ (PEq.symm (PEq.comp_id _))
        _ ≡ₜ (l'' ⨟ (f ⨟ (l ⨟ d))) := PEq.compR _ (PEq.compR _ (PEq.symm hld))
        _ ≡ₜ (l'' ⨟ ((f ⨟ l) ⨟ d)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (l'' ⨟ ((l' ⨟ d') ⨟ d)) := PEq.compR _ (PEq.compL _ he)
        _ ≡ₜ (l'' ⨟ (l' ⨟ (d' ⨟ d))) := PEq.compR _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((l'' ⨟ l') ⨟ (d' ⨟ d)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id E ⨟ (d' ⨟ d)) := PEq.compL _ h₂
        _ ≡ₜ (d' ⨟ d) := PEq.id_comp _
  | @groupInj B D f₀ g₀ hf₀ hg₀ hfg =>
      intro A f hf
      -- the drop `f` is provably equal to an aperiodic drop `f'`, so `f' ; f₀` is aperiodic
      obtain ⟨f', -, hf'ap, hff'⟩ := hf.aperiodic_normal
      have hap : IsAperiodic (f' ⨟ f₀) := by
        simpa [Term.isAperiodic_comp] using ⟨hf'ap, hf₀⟩
      obtain ⟨C, l, d, hl, hd, he⟩ := isLiftDrop_of_aperiodic _ hap
      obtain ⟨l', hl', h₁, h₂⟩ := lift_iso l hl
      refine ⟨C, l, l', d, .ofLift hl hl' h₁, hd, ?_⟩
      calc (l' ⨟ f) ≡ₜ (l' ⨟ f') := PEq.compR _ hff'
        _ ≡ₜ (l' ⨟ (f' ⨟ Term.id B)) := PEq.compR _ (PEq.symm (PEq.comp_id _))
        _ ≡ₜ (l' ⨟ (f' ⨟ (f₀ ⨟ g₀))) := PEq.compR _ (PEq.compR _ (PEq.symm hfg))
        _ ≡ₜ (l' ⨟ ((f' ⨟ f₀) ⨟ g₀)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (l' ⨟ ((l ⨟ d) ⨟ g₀)) := PEq.compR _ (PEq.compL _ he)
        _ ≡ₜ (l' ⨟ (l ⨟ (d ⨟ g₀))) := PEq.compR _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((l' ⨟ l) ⨟ (d ⨟ g₀)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id C ⨟ (d ⨟ g₀)) := PEq.compL _ h₂
        _ ≡ₜ (d ⨟ g₀) := PEq.id_comp _
  | @simon X S A₁ n G s gamma d₀ l hd₀ hl hs hgamma hret =>
      intro A f hf
      obtain ⟨C₁, nu₁, rho₁, k₁, hnu₁, hk₁, he₁⟩ :=
        prefix_exchange_group G (f ⨟ d₀) (IsDrop.comp hf hd₀)
      -- `ρ₁ ; f ; s` is provably equal to `k₁ ; l`, a drop followed by a lift.
      have hstep : ((rho₁ ⨟ f) ⨟ s) ≡ₜ (k₁ ⨟ l) := by
        calc ((rho₁ ⨟ f) ⨟ s) ≡ₜ ((rho₁ ⨟ f) ⨟ (d₀ ⨟ (Term.spref A₁ G ⨟ l))) :=
              PEq.compR _ hs
          _ ≡ₜ (((rho₁ ⨟ f) ⨟ d₀) ⨟ (Term.spref A₁ G ⨟ l)) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((rho₁ ⨟ (f ⨟ d₀)) ⨟ (Term.spref A₁ G ⨟ l)) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((k₁ ⨟ Term.unspref A₁ G) ⨟ (Term.spref A₁ G ⨟ l)) := PEq.compL _ he₁
          _ ≡ₜ (k₁ ⨟ l) := comp_cancel_mid (Term.unspref_spref A₁ G)
      obtain ⟨C₂, L, d₄, hL, hd₄, he₂⟩ := exchange k₁ l hk₁ hl
      obtain ⟨L', hL', h₁, h₂⟩ := lift_iso L hL
      refine ⟨C₂, nu₁ ⨟ L, L' ⨟ rho₁, d₄, .comp hnu₁ (.ofLift hL hL' h₁), hd₄, ?_⟩
      calc ((L' ⨟ rho₁) ⨟ f) ≡ₜ (L' ⨟ (rho₁ ⨟ f)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (L' ⨟ ((rho₁ ⨟ f) ⨟ Term.id X)) := PEq.compR _ (PEq.symm (PEq.comp_id _))
        _ ≡ₜ (L' ⨟ ((rho₁ ⨟ f) ⨟ (s ⨟ gamma))) :=
            PEq.compR _ (PEq.compR _ (PEq.symm hret))
        _ ≡ₜ (L' ⨟ (((rho₁ ⨟ f) ⨟ s) ⨟ gamma)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (L' ⨟ ((k₁ ⨟ l) ⨟ gamma)) := PEq.compR _ (PEq.compL _ hstep)
        _ ≡ₜ (L' ⨟ ((L ⨟ d₄) ⨟ gamma)) := PEq.compR _ (PEq.compL _ he₂)
        _ ≡ₜ (L' ⨟ (L ⨟ (d₄ ⨟ gamma))) := PEq.compR _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((L' ⨟ L) ⨟ (d₄ ⨟ gamma)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id C₂ ⨟ (d₄ ⨟ gamma)) := PEq.compL _ h₂
        _ ≡ₜ (d₄ ⨟ gamma) := PEq.id_comp _
  | @comp B B' B'' f₁ f₁' g₁ g₁' _ _ ih₁ ih₂ =>
      intro A f hf
      obtain ⟨C₁, nu₁, rho₁, k₁, hnu₁, hk₁, he₁⟩ := ih₁ hf
      obtain ⟨C₂, nu₂, rho₂, k₂, hnu₂, hk₂, he₂⟩ := ih₂ hk₁
      refine ⟨C₂, nu₁ ⨟ nu₂, rho₂ ⨟ rho₁, k₂, hnu₁.comp hnu₂, hk₂, ?_⟩
      calc ((rho₂ ⨟ rho₁) ⨟ f) ≡ₜ (rho₂ ⨟ (rho₁ ⨟ f)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (rho₂ ⨟ (k₁ ⨟ f₁')) := PEq.compR _ he₁
        _ ≡ₜ ((rho₂ ⨟ k₁) ⨟ f₁') := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((k₂ ⨟ g₁') ⨟ f₁') := PEq.compL _ he₂
        _ ≡ₜ (k₂ ⨟ (g₁' ⨟ f₁')) := PEq.comp_assoc _ _ _
  | @prodF B₁ B₂ D₁ D₂ f₁ f₁' g₁ g₁' _ _ ih₁ ih₂ =>
      intro A f hf
      obtain ⟨E, alpha, g₀, halpha, -, hnorm, he⟩ := drops_with_prod_codomain f hf
      exact IsGExch.congr he
        (IsGExch.of_lift_comp halpha (gexch_normalProd ih₁ ih₂ hnorm.isNormalProd))
  | @sumF B₁ B₂ D₁ D₂ f₁ f₁' g₁ g₁' _ _ ih₁ ih₂ =>
      intro A f hf
      obtain ⟨E, alpha, g₀, halpha, -, hnorm, he⟩ := drops_with_sum_codomain_tree f hf
      exact IsGExch.congr he
        (IsGExch.of_lift_comp halpha (gexch_normalSumTree ih₁ ih₂ hnorm))
  | @listF B D f₁ f₁' hp₁ ih₁ =>
      intro A f hf
      classical
      obtain ⟨F, As, alpha, fs, halpha, hleaf, he⟩ := drops_with_list_codomain f hf
      obtain ⟨fs', hfseq, hleaf'⟩ : ∃ fs' : (i : ℕ) → Term (As i) B⋆,
          (∀ i, F.usesParam i → fs i ≡ₜ fs' i) ∧ ∀ i, IsNormalListLeaf B (fs' i) := by
        refine ⟨fun i => if F.usesParam i then fs i else (Term.toUnit (As i) ⨟ Term.nilT B),
          fun i hi => ?_, fun i => ?_⟩
        · simp only [if_pos hi]
          exact PEq.refl _
        · by_cases h : F.usesParam i
          · simp only [if_pos h]
            exact (hleaf i h).isNormalListLeaf
          · simp only [if_neg h]
            exact IsNormalListLeaf.const (A := As i) (Term.nilT B)
      have hshape : normalListShape B F As fs ≡ₜ normalListShape B F As fs' :=
        PEq.compL _ (F.mapN_congr hfseq)
      have hfac : ∀ i, IsGExch (fs' i) (Term.listF f₁') :=
        fun i => gexch_normalListLeaf hp₁.retract ih₁ (hleaf' i)
      choose Cs nus rhos ks hnus hks hes using hfac
      obtain ⟨k₀, hk₀, hek₀⟩ :
          IsEqDrop (F.mapN ks ⨟ F.listConcatMap D) :=
        IsEqDrop.comp (IsEqDrop.of_isDrop (TyFn.isDrop_mapN F hks))
          (TyFn.isEqDrop_listConcatMap F D)
      refine IsGExch.congr (he.trans (PEq.compR _ hshape)) ?_
      refine IsGExch.of_lift_comp halpha ?_
      refine ⟨F.app Cs, F.mapN nus, F.mapN rhos, k₀, IsGLiftPair.mapN F hnus, hk₀, ?_⟩
      calc (F.mapN rhos ⨟ (F.mapN fs' ⨟ F.listConcatMap B))
          ≡ₜ ((F.mapN rhos ⨟ F.mapN fs') ⨟ F.listConcatMap B) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (F.mapN (fun i => rhos i ⨟ fs' i) ⨟ F.listConcatMap B) :=
            PEq.compL _ (TyFn.mapN_comp F _ _)
        _ ≡ₜ (F.mapN (fun i => ks i ⨟ Term.listF f₁') ⨟ F.listConcatMap B) :=
            PEq.compL _ (TyFn.mapN_congr F (fun i _ => hes i))
        _ ≡ₜ ((F.mapN ks ⨟ F.mapN (fun _ => Term.listF f₁')) ⨟ F.listConcatMap B) :=
            PEq.compL _ (PEq.symm (TyFn.mapN_comp F _ _))
        _ ≡ₜ (F.mapN ks ⨟ (F.mapN (fun _ => Term.listF f₁') ⨟ F.listConcatMap B)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (F.mapN ks ⨟ (F.listConcatMap D ⨟ Term.listF f₁')) :=
            PEq.compR _ (PEq.symm (TyFn.listConcatMap_natural F f₁'))
        _ ≡ₜ ((F.mapN ks ⨟ F.listConcatMap D) ⨟ Term.listF f₁') :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (k₀ ⨟ Term.listF f₁') := PEq.compL _ hek₀

/-- **Lemma (Group exchange)** (appendix, *Completeness in the presence of
groups*).  For every drop `f : A ⇒ B` and every group-lift `μ : B ⊸ D` with one-sided inverse
`π : D ⇒ B`, there are a group-lift `ν : A ⊸ C` with one-sided inverse `ρ : C ⇒ A` and a drop
`k : C ⇒ D` such that `ρ ; f ≡ k ; π`. -/
theorem group_exchange_inv {A B D : Ty} {mu : Term B D} {pi : Term D B}
    (hp : IsGLiftPair mu pi) (f : Term A B) (hf : IsDrop f) :
    ∃ (C : Ty) (nu : Term A C) (rho : Term C A) (k : Term C D),
      IsGLiftPair nu rho ∧ IsDrop k ∧ (rho ⨟ f) ≡ₜ (k ⨟ pi) :=
  group_exchange_inv_aux hp hf

end Lax149335Proofs

bridge_export Lax149335Proofs
