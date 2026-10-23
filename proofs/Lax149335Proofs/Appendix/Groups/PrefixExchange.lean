import Lax149335Proofs.Appendix.Groups.Exchange
import Lax149335Proofs.Appendix.Groups.ProductConsolidation

/-!
# The prefix exchange lemma: the induction on the shape of a drop with a list codomain

This file carries out the proof of the **prefix exchange lemma**
(`Lax149335Proofs.prefix_exchange_group`, proved in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`) of the appendix section
*Completeness in the presence of groups*.

The lemma says that every drop `f : A ⇒ (Σ B)*` fits in an inverted exchange square over the
inverse `unspref` of the group prefix multiplication, i.e. that `IsGExch f (unspref B G)`
holds: there are a group-lift `ν : A ⊸ C` with one-sided inverse `ρ : C ⇒ A` and a drop
`k : C ⇒ T B` with `ρ ; f ≡ k ; unspref`.

The proof of the appendix normalises `f` (list normalisation, `drops_with_list_codomain`) and
then proceeds by induction on the list-polynomial functor `F` of the normal form
`F(f₁,…,fₙ) ; genconc`.  This file follows that plan:

* `Lax149335Proofs.IsGExch.of_gliftPair_liftDrop` is the bookkeeping lemma used everywhere: to
  establish an exchange square it is enough to produce *some* group-lift pair `(ν, ρ)` and a
  term `m` that is provably a lift followed by a drop with `ρ ; f ≡ m ; π`; the lift of `m`
  is absorbed into the group-lift.
* the three leaf shapes: a constant (`Lax149335Proofs.gexch_const`), a singleton
  (`Lax149335Proofs.gexch_sing`) and a homomorphic image (the *map case*);
* the functorial nodes: co-product (`Lax149335Proofs.IsGExch.either`), product
  (`Lax149335Proofs.gexch_prodNode`, which uses the *product consolidation* of the appendix, proved
  in `Lax149335Proofs.Appendix.Groups.ProductConsolidation`) and list
  (`Lax149335Proofs.gexch_listNode`).

Two ingredients of the appendix's argument are not proved *in this file*; they are recorded
as the explicit hypotheses `Lax149335Proofs.PrefixExchangeMapCase` and
`Lax149335Proofs.StarConsolidation`, and everything else is derived from them.
Both are proved elsewhere:

* the **map case**: for a drop `g : A ⇒ Σ Y`, the term `g*` satisfies the exchange square.
  The appendix proves it with a group injection followed by a Simon lift; this is done in
  `Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`
  (`Lax149335Proofs.prefixExchangeMapCase_group`), from the Simon lift lemma
  (`Lax149335Proofs.simon_lift_H`) and the component-wise exchange lemma
  (`Lax149335Proofs.simon_exchange_component_wise`).
* the **star consolidation square** (the top-right face of the appendix's star diagram) —
  this one is *proved*, in `Lax149335Proofs.Appendix.Groups.StarConsolidation`
  (`Lax149335Proofs.starConsolidation`): the
  unprefixing of a list of prefixed blocks, followed by concatenation, factors as an
  aperiodic annotation of each block, one group prefix multiplication on the outer labels, an
  aperiodic re-multiplication, and one unprefixing.  The appendix obtains it by the
  isomorphism trick from an aperiodic identity, using the auxiliary terms `repair` and
  `postrepair`.

`Lax149335Proofs.prefix_exchange_of_claims` is the conclusion: the prefix exchange lemma follows
from those two claims, and hence unconditionally
(`Lax149335Proofs.prefix_exchange_group`, in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Bookkeeping -/

/-- To establish an exchange square it is enough to produce a group-lift pair `(ν, ρ)` and a
term `m` that is provably a lift followed by a drop with `ρ ; f ≡ m ; π`: the lift of `m` is
absorbed into the group-lift. -/
theorem IsGExch.of_gliftPair_liftDrop {A B C D : Ty} {f : Term A B} {pi : Term D B}
    {nu : Term A C} {rho : Term C A} {m : Term C D} (hp : IsGLiftPair nu rho)
    (hm : IsLiftDrop m) (he : (rho ⨟ f) ≡ₜ (m ⨟ pi)) : IsGExch f pi := by
  obtain ⟨E, l, d, hl, hd, hme⟩ := hm
  obtain ⟨l', hl'drop, h₁, h₂⟩ := lift_iso l hl
  refine ⟨E, nu ⨟ l, l' ⨟ rho, d, hp.comp (.ofLift hl hl'drop h₁), hd, ?_⟩
  calc ((l' ⨟ rho) ⨟ f) ≡ₜ (l' ⨟ (rho ⨟ f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (l' ⨟ (m ⨟ pi)) := PEq.compR _ he
    _ ≡ₜ (l' ⨟ ((l ⨟ d) ⨟ pi)) := PEq.compR _ (PEq.compL _ hme)
    _ ≡ₜ (l' ⨟ (l ⨟ (d ⨟ pi))) := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((l' ⨟ l) ⨟ (d ⨟ pi)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id E ⨟ (d ⨟ pi)) := PEq.compL _ h₂
    _ ≡ₜ (d ⨟ pi) := PEq.id_comp _

/-- The special case in which no group-lift is needed: `f ≡ m ; π` with `m` provably a lift
followed by a drop. -/
theorem IsGExch.of_liftDrop {A B D : Ty} {f : Term A B} {pi : Term D B} {m : Term A D}
    (hm : IsLiftDrop m) (he : f ≡ₜ (m ⨟ pi)) : IsGExch f pi :=
  IsGExch.of_gliftPair_liftDrop (IsGLiftPair.id A) hm ((PEq.id_comp _).trans he)

/-- A drop composed with an aperiodic term is provably a lift followed by a drop. -/
theorem isLiftDrop_drop_aperiodic {A B C : Ty} {d : Term A B} {a : Term B C} (hd : IsDrop d)
    (ha : IsAperiodic a) : IsLiftDrop (d ⨟ a) :=
  (IsLiftDrop.of_isDrop hd).comp (isLiftDrop_of_aperiodic a ha)

/-! ### The two claims that are not proved here -/

/-- **Claim (map case)** (appendix, proof of the prefix exchange lemma, leaf case `g*`).  For
every drop `g : A ⇒ Σ Y` into a co-product indexed by the group, the homomorphic image `g*`
satisfies the inverted exchange square over `unspref`.

The appendix proves this by injecting `A` into a co-product `Σ_H C` indexed by a subset of the
group (`Lax149335Proofs.group_injection`) and then applying the Simon lift for `H`
(`Lax149335Proofs.simon_lift_H`) together with the component-wise naturality of its one-sided
inverse `γ`; that is carried out in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`. -/
def PrefixExchangeMapCase {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) : Prop :=
  ∀ (Y A : Ty) (g : Term A (Term.sigmaTy Y n)), IsDrop g →
    IsGExch (Term.listF g) (Term.unspref Y G)

/-- **Claim (star consolidation)** (appendix, proof of the prefix exchange lemma, star case:
the top-right face of the diagram).  Unprefixing every block of a list of prefixed words and
concatenating the results is the same as annotating every block with its last group element,
prefix-multiplying those annotations, re-multiplying the blocks accordingly and concatenating,
and then unprefixing once.

Both `ap` (the annotation of a block by its last group element) and `q` (the
re-multiplication followed by the concatenation) are aperiodic; the only prefix multiplication
of the right-hand side is the one on the outer annotations.  The appendix proves the identity
by the isomorphism trick, after replacing `ap` by a one-sided inverse built from its auxiliary
terms `repair` and `postrepair`. -/
def StarConsolidation {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) : Prop :=
  ∀ B : Ty, ∃ (ap : Term (Term.tTy B n) (Term.sigmaTy ((Term.sigmaTy B n)⋆) n))
      (q : Term (Term.tTy ((Term.sigmaTy B n)⋆) n) (Term.tTy B n)),
    IsAperiodic ap ∧ IsAperiodic q ∧
      (Term.listF (Term.unspref B G) ⨟ Term.concat (Term.sigmaTy B n)) ≡ₜ
        ((Term.listF ap ⨟ (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G)

/-! ### The leaf cases -/

/-- The leaf case of a constant: a value of type `(Σ B)*` is the image under `unspref` of the
value that represents its prefix multiplication. -/
theorem gexch_const {A B : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (v : Value ((Term.sigmaTy B n)⋆)) :
    IsGExch (Term.toUnit A ⨟ v) (Term.unspref B G) := by
  classical
  have hsu : ∀ y : ⟦(Term.sigmaTy B n)⋆⟧,
      (Term.unspref B G).den ((Term.spref B G).den y) = y := by
    intro y
    have h := congrFun (PEq.sound (Term.spref_unspref B G)) y
    simpa using h
  refine IsGExch.of_liftDrop
    (IsLiftDrop.of_isDrop (IsDrop.bangV A (encV (Term.tTy B n)
      ((Term.spref B G).den (v.den ()))))) ?_
  have hval : (encV (Term.tTy B n) ((Term.spref B G).den (v.den ())) ⨟
      Term.unspref B G) ≡ₜ v := by
    refine (computes (Term.unspref B G) ((Term.spref B G).den (v.den ()))).trans ?_
    rw [hsu]
    exact PEq.symm ((PEq.symm (PEq.id_comp v)).trans (computes v ()))
  calc (Term.toUnit A ⨟ v)
      ≡ₜ (Term.toUnit A ⨟ (encV (Term.tTy B n) ((Term.spref B G).den (v.den ())) ⨟
          Term.unspref B G)) := PEq.compR _ (PEq.symm hval)
    _ ≡ₜ ((Term.toUnit A ⨟ encV (Term.tTy B n) ((Term.spref B G).den (v.den ()))) ⨟
          Term.unspref B G) := PEq.symm (PEq.comp_assoc _ _ _)

/-- The leaf case of a singleton: `unspref` does not change a one-letter word. -/
theorem gexch_sing {A B : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) {g : Term A (Term.sigmaTy B n)}
    (hg : IsDrop g) :
    IsGExch (g ⨟ Term.pureT (Term.sigmaTy B n)) (Term.unspref B G) := by
  have hap : IsAperiodic (Term.pureT (Term.sigmaTy B n) ⨟ Term.toT B n) := by
    simp [IsAperiodic, Term.usesPref, Term.pureT]
  have hden : (Term.pureT (Term.sigmaTy B n) ⨟ (Term.toT B n ⨟ Term.unspref B G)).den =
      (Term.pureT (Term.sigmaTy B n)).den := by
    funext z
    letI := G
    show (Term.unspref B G).den ((Term.toT B n).den [z]) = [z]
    rw [Term.den_unspref, Term.den_fromT_toT]
    have hone : ∀ p : ⟦B⟧ × ⟦Ty.finAlph n⟧,
        unprefDen (1 : ⟦Ty.finAlph n⟧) [p] = [p] := by
      rintro ⟨a, k⟩
      simp
    simp [Term.unsprefW, hone]
  have hsing : Term.pureT (Term.sigmaTy B n) ≡ₜ
      (Term.pureT (Term.sigmaTy B n) ⨟ (Term.toT B n ⨟ Term.unspref B G)) := by
    refine PEq.symm (completeness_aperiodic _ _ ?_ ?_ hden)
    · simp [IsAperiodic, Term.usesPref, Term.pureT]
    · simp [IsAperiodic, Term.usesPref, Term.pureT]
  refine IsGExch.of_liftDrop (isLiftDrop_drop_aperiodic hg hap) ?_
  calc (g ⨟ Term.pureT (Term.sigmaTy B n))
      ≡ₜ (g ⨟ (Term.pureT (Term.sigmaTy B n) ⨟ (Term.toT B n ⨟ Term.unspref B G))) :=
        PEq.compR _ hsing
    _ ≡ₜ (g ⨟ ((Term.pureT (Term.sigmaTy B n) ⨟ Term.toT B n) ⨟ Term.unspref B G)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((g ⨟ (Term.pureT (Term.sigmaTy B n) ⨟ Term.toT B n)) ⨟ Term.unspref B G) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- The three leaf shapes together. -/
theorem gexch_leaf {A B : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hmap : PrefixExchangeMapCase G) {u : Term A ((Term.sigmaTy B n)⋆)}
    (hu : IsNormalListLeaf (Term.sigmaTy B n) u) : IsGExch u (Term.unspref B G) := by
  induction hu with
  | const v => exact gexch_const G v
  | sing hg => exact gexch_sing G hg
  | map hg => exact hmap B _ _ hg

/-! ### The functorial nodes -/

/-- The product node: this is where the product case of the consolidation claim of the
appendix is used. -/
theorem gexch_prodNode {A₁ A₂ B : Ty} {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {u₁ : Term A₁ ((Term.sigmaTy B n)⋆)} {u₂ : Term A₂ ((Term.sigmaTy B n)⋆)}
    (h₁ : IsGExch u₁ (Term.unspref B G)) (h₂ : IsGExch u₂ (Term.unspref B G)) :
    IsGExch (Term.prodF u₁ u₂ ⨟ Term.binconcat (Term.sigmaTy B n)) (Term.unspref B G) := by
  obtain ⟨C₁, nu₁, rho₁, k₁, hp₁, hk₁, he₁⟩ := h₁
  obtain ⟨C₂, nu₂, rho₂, k₂, hp₂, hk₂, he₂⟩ := h₂
  refine IsGExch.of_gliftPair_liftDrop (hp₁.prodF hp₂)
    (isLiftDrop_drop_aperiodic (IsDrop.prodF hk₁ hk₂) (isAperiodic_consolProd B G)) ?_
  calc (Term.prodF rho₁ rho₂ ⨟ (Term.prodF u₁ u₂ ⨟ Term.binconcat (Term.sigmaTy B n)))
      ≡ₜ ((Term.prodF rho₁ rho₂ ⨟ Term.prodF u₁ u₂) ⨟ Term.binconcat (Term.sigmaTy B n)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.prodF (rho₁ ⨟ u₁) (rho₂ ⨟ u₂) ⨟ Term.binconcat (Term.sigmaTy B n)) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.prodF (k₁ ⨟ Term.unspref B G) (k₂ ⨟ Term.unspref B G) ⨟
          Term.binconcat (Term.sigmaTy B n)) := PEq.compL _ (PEq.congr_prodF he₁ he₂)
    _ ≡ₜ ((Term.prodF k₁ k₂ ⨟ Term.prodF (Term.unspref B G) (Term.unspref B G)) ⨟
          Term.binconcat (Term.sigmaTy B n)) := PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
    _ ≡ₜ (Term.prodF k₁ k₂ ⨟ (Term.prodF (Term.unspref B G) (Term.unspref B G) ⨟
          Term.binconcat (Term.sigmaTy B n))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.prodF k₁ k₂ ⨟ (Term.consolProd B G ⨟ Term.unspref B G)) :=
        PEq.compR _ (PEq.symm (consolProd_unspref B G))
    _ ≡ₜ ((Term.prodF k₁ k₂ ⨟ Term.consolProd B G) ⨟ Term.unspref B G) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- The list node: this is where the star consolidation claim and the map case are used. -/
theorem gexch_listNode {A B : Ty} {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    (hmap : PrefixExchangeMapCase G) (hstar : StarConsolidation G)
    {u : Term A ((Term.sigmaTy B n)⋆)} (h : IsGExch u (Term.unspref B G)) :
    IsGExch (Term.listF u ⨟ Term.concat (Term.sigmaTy B n)) (Term.unspref B G) := by
  obtain ⟨C, nu, rho, k, hp, hk, he⟩ := h
  obtain ⟨ap, q, hapAp, hapQ, hsq⟩ := hstar B
  -- the annotation of every block, after the drop `k`, is a lift followed by a drop
  obtain ⟨D, l₁, q₁, hl₁, hq₁, hd₁⟩ := isLiftDrop_drop_aperiodic hk hapAp
  obtain ⟨l₁', hl₁'drop, hl₁₁, hl₁₂⟩ := lift_iso l₁ hl₁
  -- the map case, applied to the drop `q₁`
  obtain ⟨C₂, nu₂, rho₂, k₂, hp₂, hk₂, he₂⟩ := hmap ((Term.sigmaTy B n)⋆) D q₁ hq₁
  have hlist₁ : (Term.listF l₁ ⨟ Term.listF l₁') ≡ₜ Term.id (C⋆) :=
    (PEq.list_comp _ _).trans ((PEq.congr_listF hl₁₁).trans (PEq.list_id _))
  have hlist₂ : (Term.listF l₁' ⨟ Term.listF l₁) ≡ₜ Term.id (D⋆) :=
    (PEq.list_comp _ _).trans ((PEq.congr_listF hl₁₂).trans (PEq.list_id _))
  refine IsGExch.of_gliftPair_liftDrop
    (((hp.listF).comp (.ofLift (IsLift.listF hl₁) (IsDrop.listF hl₁'drop) hlist₁)).comp hp₂)
    (isLiftDrop_drop_aperiodic hk₂ hapQ) ?_
  -- the inner square, at the level of lists
  have h₁ : (Term.listF rho ⨟ Term.listF u) ≡ₜ (Term.listF k ⨟ Term.listF (Term.unspref B G)) :=
    (PEq.list_comp _ _).trans ((PEq.congr_listF he).trans (PEq.symm (PEq.list_comp _ _)))
  have h₂ : (Term.listF k ⨟ Term.listF ap) ≡ₜ (Term.listF l₁ ⨟ Term.listF q₁) :=
    (PEq.list_comp _ _).trans ((PEq.congr_listF hd₁).trans (PEq.symm (PEq.list_comp _ _)))
  have s₁ : (Term.listF rho ⨟ (Term.listF u ⨟ Term.concat (Term.sigmaTy B n))) ≡ₜ
      ((Term.listF l₁ ⨟ (Term.listF q₁ ⨟
        (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q))) ⨟ Term.unspref B G) := by
    calc (Term.listF rho ⨟ (Term.listF u ⨟ Term.concat (Term.sigmaTy B n)))
        ≡ₜ ((Term.listF rho ⨟ Term.listF u) ⨟ Term.concat (Term.sigmaTy B n)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((Term.listF k ⨟ Term.listF (Term.unspref B G)) ⨟
            Term.concat (Term.sigmaTy B n)) := PEq.compL _ h₁
      _ ≡ₜ (Term.listF k ⨟ (Term.listF (Term.unspref B G) ⨟
            Term.concat (Term.sigmaTy B n))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.listF k ⨟ ((Term.listF ap ⨟
            (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G)) :=
          PEq.compR _ hsq
      _ ≡ₜ (((Term.listF k ⨟ Term.listF ap) ⨟
            (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G) :=
          (PEq.symm (PEq.comp_assoc _ _ _)).trans
            (PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _)))
      _ ≡ₜ (((Term.listF l₁ ⨟ Term.listF q₁) ⨟
            (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G) :=
          PEq.compL _ (PEq.compL _ h₂)
      _ ≡ₜ ((Term.listF l₁ ⨟ (Term.listF q₁ ⨟
            (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q))) ⨟ Term.unspref B G) :=
          PEq.compL _ (PEq.comp_assoc _ _ _)
  -- and the outer one, after cancelling the lift and using the map case
  have s₂ : (rho₂ ⨟ (Term.listF q₁ ⨟ (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q))) ≡ₜ
      (k₂ ⨟ q) := by
    calc (rho₂ ⨟ (Term.listF q₁ ⨟ (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)))
        ≡ₜ (rho₂ ⨟ ((Term.listF q₁ ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟ q)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((rho₂ ⨟ (Term.listF q₁ ⨟ Term.spref ((Term.sigmaTy B n)⋆) G)) ⨟ q) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((rho₂ ⨟ Term.listF q₁) ⨟ Term.spref ((Term.sigmaTy B n)⋆) G) ⨟ q) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((k₂ ⨟ Term.unspref ((Term.sigmaTy B n)⋆) G) ⨟
            Term.spref ((Term.sigmaTy B n)⋆) G) ⨟ q) := PEq.compL _ (PEq.compL _ he₂)
      _ ≡ₜ ((k₂ ⨟ (Term.unspref ((Term.sigmaTy B n)⋆) G ⨟
            Term.spref ((Term.sigmaTy B n)⋆) G)) ⨟ q) :=
          PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((k₂ ⨟ Term.id (Term.tTy ((Term.sigmaTy B n)⋆) n)) ⨟ q) :=
          PEq.compL _ (PEq.compR _ (Term.unspref_spref _ G))
      _ ≡ₜ (k₂ ⨟ q) := PEq.compL _ (PEq.comp_id _)
  calc ((rho₂ ⨟ (Term.listF l₁' ⨟ Term.listF rho)) ⨟
        (Term.listF u ⨟ Term.concat (Term.sigmaTy B n)))
      ≡ₜ (rho₂ ⨟ (Term.listF l₁' ⨟ (Term.listF rho ⨟
          (Term.listF u ⨟ Term.concat (Term.sigmaTy B n))))) :=
        (PEq.comp_assoc _ _ _).trans (PEq.compR _ (PEq.comp_assoc _ _ _))
    _ ≡ₜ (rho₂ ⨟ (Term.listF l₁' ⨟ ((Term.listF l₁ ⨟ (Term.listF q₁ ⨟
          (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q))) ⨟ Term.unspref B G))) :=
        PEq.compR _ (PEq.compR _ s₁)
    _ ≡ₜ (rho₂ ⨟ ((Term.listF l₁' ⨟ Term.listF l₁) ⨟ ((Term.listF q₁ ⨟
          (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G))) :=
        PEq.compR _ ((PEq.compR _ (PEq.comp_assoc _ _ _)).trans
          (PEq.symm (PEq.comp_assoc _ _ _)))
    _ ≡ₜ (rho₂ ⨟ (Term.id (D⋆) ⨟ ((Term.listF q₁ ⨟
          (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟ Term.unspref B G))) :=
        PEq.compR _ (PEq.compL _ hlist₂)
    _ ≡ₜ (rho₂ ⨟ ((Term.listF q₁ ⨟ (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q)) ⨟
          Term.unspref B G)) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ ((rho₂ ⨟ (Term.listF q₁ ⨟ (Term.spref ((Term.sigmaTy B n)⋆) G ⨟ q))) ⨟
          Term.unspref B G) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((k₂ ⨟ q) ⨟ Term.unspref B G) := PEq.compL _ s₂

/-! ### The induction on the shape of the normal form -/

/-- The induction of the appendix, on the list-polynomial functor of the normal form. -/
theorem gexch_normalListShape {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    (hmap : PrefixExchangeMapCase G) (hstar : StarConsolidation G) :
    ∀ (F : TyFn) (B : Ty) (As : ℕ → Ty) (fs : (i : ℕ) → Term (As i) ((Term.sigmaTy B n)⋆)),
      (∀ i, IsNormalListLeaf (Term.sigmaTy B n) (fs i)) →
      IsGExch (F.mapN fs ⨟ F.listConcatMap (Term.sigmaTy B n)) (Term.unspref B G) := by
  intro F
  induction F with
  | param i =>
      intro B As fs hfs
      exact IsGExch.congr (PEq.comp_id _) (gexch_leaf G hmap (hfs i))
  | unit =>
      intro B As _ _
      exact IsGExch.congr (PEq.compL _ (PEq.unit_unique _ _))
        (gexch_const (A := Ty.unit) G (Term.nilT (Term.sigmaTy B n)))
  | prod F₁ F₂ ih₁ ih₂ =>
      intro B As fs hfs
      refine IsGExch.congr ?_ (gexch_prodNode (ih₁ B As fs hfs) (ih₂ B As fs hfs))
      calc (Term.prodF (F₁.mapN fs) (F₂.mapN fs) ⨟
            (Term.prodF (F₁.listConcatMap (Term.sigmaTy B n))
              (F₂.listConcatMap (Term.sigmaTy B n)) ⨟ Term.binconcat (Term.sigmaTy B n)))
          ≡ₜ ((Term.prodF (F₁.mapN fs) (F₂.mapN fs) ⨟
              Term.prodF (F₁.listConcatMap (Term.sigmaTy B n))
                (F₂.listConcatMap (Term.sigmaTy B n))) ⨟ Term.binconcat (Term.sigmaTy B n)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.prodF (F₁.mapN fs ⨟ F₁.listConcatMap (Term.sigmaTy B n))
              (F₂.mapN fs ⨟ F₂.listConcatMap (Term.sigmaTy B n)) ⨟
              Term.binconcat (Term.sigmaTy B n)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
  | sum F₁ F₂ ih₁ ih₂ =>
      intro B As fs hfs
      exact IsGExch.congr (Term.sumF_either _ _ _ _)
        ((ih₁ B As fs hfs).either (ih₂ B As fs hfs))
  | list F₁ ih₁ =>
      intro B As fs hfs
      refine IsGExch.congr ?_ (gexch_listNode hmap hstar (ih₁ B As fs hfs))
      calc (Term.listF (F₁.mapN fs) ⨟
            (Term.listF (F₁.listConcatMap (Term.sigmaTy B n)) ⨟
              Term.concat (Term.sigmaTy B n)))
          ≡ₜ ((Term.listF (F₁.mapN fs) ⨟ Term.listF (F₁.listConcatMap (Term.sigmaTy B n))) ⨟
              Term.concat (Term.sigmaTy B n)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.listF (F₁.mapN fs ⨟ F₁.listConcatMap (Term.sigmaTy B n)) ⨟
              Term.concat (Term.sigmaTy B n)) := PEq.compL _ (PEq.list_comp _ _)

/-- **Lemma (Prefix exchange)** (appendix, *Proof of the group exchange lemma*), from
the two claims that are not proved here. -/
theorem prefix_exchange_of_claims {A B : Ty} {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    (hmap : PrefixExchangeMapCase G) (hstar : StarConsolidation G)
    (f : Term A ((Term.sigmaTy B n)⋆)) (hf : IsDrop f) :
    IsGExch f (Term.unspref B G) := by
  classical
  obtain ⟨F, As, alpha, fs, halpha, hleaf, he⟩ := drops_with_list_codomain f hf
  obtain ⟨fs', hfseq, hleaf'⟩ : ∃ fs' : (i : ℕ) → Term (As i) ((Term.sigmaTy B n)⋆),
      (∀ i, F.usesParam i → fs i ≡ₜ fs' i) ∧
        ∀ i, IsNormalListLeaf (Term.sigmaTy B n) (fs' i) := by
    refine ⟨fun i => if F.usesParam i then fs i else
        (Term.toUnit (As i) ⨟ Term.nilT (Term.sigmaTy B n)), fun i hi => ?_, fun i => ?_⟩
    · simp only [if_pos hi]
      exact PEq.refl _
    · by_cases h : F.usesParam i
      · simp only [if_pos h]
        exact (hleaf i h).isNormalListLeaf
      · simp only [if_neg h]
        exact IsNormalListLeaf.const (A := As i) (Term.nilT (Term.sigmaTy B n))
  have hshape : normalListShape (Term.sigmaTy B n) F As fs ≡ₜ
      normalListShape (Term.sigmaTy B n) F As fs' := PEq.compL _ (F.mapN_congr hfseq)
  exact IsGExch.congr (he.trans (PEq.compR _ hshape))
    (IsGExch.of_lift_comp halpha (gexch_normalListShape hmap hstar F B As fs' hleaf'))

/-! ### Re-indexing along the injection `ρ`

What is left of the appendix's proof of the map case is carried out in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`: the source of the drop `g : A ⇒ Σ Y`
is injected into a co-product `Σ_H C` indexed by a subset `H` of the group
(`Lax149335Proofs.group_injection`, proved), after which the component-wise exchange lemma
(`Lax149335Proofs.simon_exchange_component_wise`) applies.  The small piece of bookkeeping that
both files need is the following. -/

/-- Re-indexing a case tree along the injection `ρ : Σ_H Y ↣ Σ Y`. -/
theorem sigmaCase_rhoInj {C Y : Ty} {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (fs : ⟦Ty.finAlph m⟧ → Term C Y) :
    Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y (hm i)) ≡ₜ
      (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i) ⨟ Term.rhoInj Y hm) := by
  refine PEq.symm ((Term.sigmaCase_comp _ _).trans (Term.sigmaCase_congr (fun i => ?_)))
  calc ((fs i ⨟ Term.injSigma Y i) ⨟ Term.rhoInj Y hm)
      ≡ₜ (fs i ⨟ (Term.injSigma Y i ⨟ Term.rhoInj Y hm)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (fs i ⨟ Term.injSigma Y (hm i)) :=
        PEq.compR _ (Term.injSigma_sigmaCase (fun j => Term.injSigma Y (hm j)) i)

end Lax149335Proofs

bridge_export Lax149335Proofs
