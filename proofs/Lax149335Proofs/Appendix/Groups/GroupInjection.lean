import Lax149335Proofs.Appendix.Groups.GroupliftPairs
import Lax149335Proofs.Appendix.Drops.SumProdNormalisation

/-!
# Group injections (appendix, *Completeness in the presence of groups*)

This file proves the **group injection lemma** of the appendix section: a drop
function `f : A ⇒ Σ B` into a group-annotated co-product becomes *annotation-diagonal* after
its domain has been injected into a co-product `Σ_H C` indexed by a subset `H` of the group.

The predicate that collects the conclusion is `Lax149335Proofs.HasGroupInjection`.  As in the
appendix, the injection is an **aperiodic** term, provably injective with a drop one-sided
inverse.

The proof is the one of the appendix:

* the co-product normalisation of drops (`Lax149335Proofs.drops_with_sum_codomain`) writes `f` as a
  lift followed by a co-pairing of components `gᵢ ; ρᵢ`, each of which injects into a single
  variant of `Σ B`;
* a component is annotation-diagonal for the one-element subset `H = {ρᵢ}`;
* the co-pairing of two annotation-diagonal drops is annotation-diagonal for the union of
  the two subsets — this is the *grouping of summands* of the appendix, and it is where the
  one-sided inverse has to be chosen with care: on a variant that only one of the two sides
  uses, the inverse must send the *other* side's summand to a constant of the domain of that
  one, so that the composition with `f` still lands in the intended variant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Enumerating a subset of a finite alphabet

A subset `H` of the alphabet `⟦finAlph n⟧` is presented, as in the appendix, by an injective
map `⟦finAlph m⟧ → ⟦finAlph n⟧`.  Combining two such presentations into one for the union of
the two subsets is the only combinatorial ingredient of the proof. -/

/-- The list of all the letters of a finite alphabet. -/
def enumFin : (m : ℕ) → List ⟦Ty.finAlph m⟧
  | 0 => [()]
  | (m + 1) => (Sum.inl () : ⟦Ty.finAlph (m + 1)⟧) :: (enumFin m).map Sum.inr

/-- A letter of a finite alphabet; finite alphabets are never empty. -/
def firstLetter : (m : ℕ) → ⟦Ty.finAlph m⟧
  | 0 => ()
  | (_ + 1) => .inl ()

theorem mem_enumFin : (m : ℕ) → (x : ⟦Ty.finAlph m⟧) → x ∈ enumFin m
  | 0, () => List.mem_singleton.mpr rfl
  | (_ + 1), .inl () => List.mem_cons_self ..
  | (m + 1), .inr g => List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_enumFin m g))

/-- Every non-empty duplicate-free list of letters is the range of an injective map from a
finite alphabet. -/
theorem exists_enum_of_nodup {n : ℕ} : (L : List ⟦Ty.finAlph n⟧) → L ≠ [] → L.Nodup →
    ∃ (m : ℕ) (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧),
      Function.Injective hm ∧ (∀ k, hm k ∈ L) ∧ ∀ x ∈ L, ∃ k, hm k = x
  | [], h, _ => absurd rfl h
  | [x], _, _ => by
      refine ⟨0, fun _ => x, ?_, ?_, ?_⟩
      · rintro ⟨⟩ ⟨⟩ _; rfl
      · intro _; exact List.mem_singleton.mpr rfl
      · intro y hy
        exact ⟨(), (List.mem_singleton.mp hy).symm⟩
  | (x :: y :: L), _, hnd => by
      obtain ⟨m, hm, hinj, hmem, hsurj⟩ :=
        exists_enum_of_nodup (y :: L) (by simp) hnd.of_cons
      have hx : x ∉ (y :: L) := by
        simpa using hnd.notMem
      refine ⟨m + 1, fun k => match k with | .inl () => x | .inr g => hm g, ?_, ?_, ?_⟩
      · rintro (⟨⟩ | a) (⟨⟩ | b) h
        · rfl
        · exact absurd (show x ∈ y :: L from (show x = hm b from h) ▸ hmem b) hx
        · exact absurd (show x ∈ y :: L from (show hm a = x from h) ▸ hmem a) hx
        · exact congrArg Sum.inr (hinj h)
      · rintro (⟨⟩ | g)
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hmem g)
      · intro z hz
        rcases List.mem_cons.mp hz with h | h
        · exact ⟨.inl (), h.symm⟩
        · obtain ⟨k, hk⟩ := hsurj z h
          exact ⟨.inr k, hk⟩

/-- **The union of two subsets of the alphabet.**  Two presentations of subsets of
`⟦finAlph n⟧` are refined by a common one, whose range is the union of the two ranges. -/
theorem exists_union_enum {n m₁ m₂ : ℕ} (hm₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph n⟧)
    (hm₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph n⟧) :
    ∃ (m : ℕ) (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
      (u₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph m⟧) (u₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph m⟧),
      Function.Injective hm ∧ (∀ i, hm (u₁ i) = hm₁ i) ∧ (∀ j, hm (u₂ j) = hm₂ j) ∧
        ∀ k, (∃ i, u₁ i = k) ∨ ∃ j, u₂ j = k := by
  classical
  set L : List ⟦Ty.finAlph n⟧ :=
    (((enumFin m₁).map hm₁ ++ (enumFin m₂).map hm₂).dedup) with hL
  have hmem₁ : ∀ i, hm₁ i ∈ L := by
    intro i
    rw [hL, List.mem_dedup]
    exact List.mem_append_left _ (List.mem_map_of_mem (mem_enumFin m₁ i))
  have hmem₂ : ∀ j, hm₂ j ∈ L := by
    intro j
    rw [hL, List.mem_dedup]
    exact List.mem_append_right _ (List.mem_map_of_mem (mem_enumFin m₂ j))
  have hne : L ≠ [] := by
    intro h
    exact absurd (h ▸ hmem₁ (firstLetter m₁)) (List.not_mem_nil)
  obtain ⟨m, hm, hinj, hmemL, hsurjL⟩ := exists_enum_of_nodup L hne (List.nodup_dedup _)
  have hu₁ : ∀ i, ∃ k, hm k = hm₁ i := fun i => hsurjL _ (hmem₁ i)
  have hu₂ : ∀ j, ∃ k, hm k = hm₂ j := fun j => hsurjL _ (hmem₂ j)
  refine ⟨m, hm, fun i => (hu₁ i).choose, fun j => (hu₂ j).choose, hinj,
    fun i => (hu₁ i).choose_spec, fun j => (hu₂ j).choose_spec, ?_⟩
  intro k
  have hk : hm k ∈ L := hmemL k
  rw [hL, List.mem_dedup, List.mem_append] at hk
  rcases hk with h | h
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp h
    refine Or.inl ⟨i, hinj ?_⟩
    rw [(hu₁ i).choose_spec, hi]
  · obtain ⟨j, -, hj⟩ := List.mem_map.mp h
    refine Or.inr ⟨j, hinj ?_⟩
    rw [(hu₂ j).choose_spec, hj]

/-! ### The conclusion of the group injection lemma -/

/-- **The conclusion of the group injection lemma.**  There are a subset `H` of the group —
presented by the injective map `hm` — a type `C`, an aperiodic term `iota : A → Σ_H C` which
is provably injective with the drop one-sided inverse `sigma`, and drops `fs` such that
`sigma ; f` is the case tree that sends the `i`-th variant of `Σ_H C` into the `hm i`-th
variant of `Σ B` by the drop `fs i`. -/
def HasGroupInjection {A B : Ty} {n : ℕ} (f : Term A (Term.sigmaTy B n)) : Prop :=
  ∃ (m : ℕ) (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (C : Ty)
    (iota : Term A (Term.sigmaTy C m)) (sigma : Term (Term.sigmaTy C m) A)
    (fs : ⟦Ty.finAlph m⟧ → Term C B),
    Function.Injective hm ∧ IsAperiodic iota ∧ IsDrop sigma ∧
      (iota ⨟ sigma) ≡ₜ Term.id A ∧ (∀ i, IsDrop (fs i)) ∧
      (sigma ⨟ f) ≡ₜ Term.sigmaCase (fun i => fs i ⨟ Term.injSigma B (hm i))

namespace HasGroupInjection

theorem congr {A B : Ty} {n : ℕ} {f f' : Term A (Term.sigmaTy B n)} (h : f ≡ₜ f')
    (hf : HasGroupInjection f') : HasGroupInjection f := by
  obtain ⟨m, hm, C, iota, sigma, fs, hinj, hap, hsig, hret, hfs, he⟩ := hf
  exact ⟨m, hm, C, iota, sigma, fs, hinj, hap, hsig, hret, hfs, (PEq.compR _ h).trans he⟩

/-- A lift in front of the drop is absorbed into the group-lift. -/
theorem of_lift_comp {A E B : Ty} {n : ℕ} {alpha : Term A E} {g : Term E (Term.sigmaTy B n)}
    (hl : IsLift alpha) (hg : HasGroupInjection g) :
    HasGroupInjection (alpha ⨟ g) := by
  obtain ⟨m, hm, C, iota, sigma, fs, hinj, hap, hsig, hret, hfs, he⟩ := hg
  obtain ⟨alpha', halpha', h₁, h₂⟩ := lift_iso alpha hl
  refine ⟨m, hm, C, alpha ⨟ iota, sigma ⨟ alpha', fs, hinj,
    by simpa [Term.isAperiodic_comp] using ⟨hl.isAperiodic, hap⟩,
    IsDrop.comp hsig halpha', ?_, hfs, ?_⟩
  · calc ((alpha ⨟ iota) ⨟ (sigma ⨟ alpha')) ≡ₜ (alpha ⨟ alpha') := comp_cancel_mid hret
      _ ≡ₜ Term.id _ := h₁
  · calc ((sigma ⨟ alpha') ⨟ (alpha ⨟ g)) ≡ₜ (sigma ⨟ g) := comp_cancel_mid h₂
      _ ≡ₜ _ := he

/-- A drop into a single variant of `Σ B` is annotation-diagonal for the one-element subset
consisting of that variant. -/
theorem leaf {A B : Ty} {n : ℕ} {g : Term A B} (hg : IsDrop g) (k : ⟦Ty.finAlph n⟧) :
    HasGroupInjection (g ⨟ Term.injSigma B k) := by
  refine ⟨0, fun _ => k, A, Term.id A, Term.id A, fun _ => g, ?_,
    by simp [IsAperiodic, Term.usesPref], IsDrop.id A, PEq.id_comp _, fun _ => hg, ?_⟩
  · rintro ⟨⟩ ⟨⟩ _; rfl
  · exact PEq.id_comp _

/-- Passing from `Σ B` to one more variant. -/
theorem inr {A B : Ty} {n : ℕ} {h : Term A (Term.sigmaTy B n)} (hh : HasGroupInjection h) :
    HasGroupInjection (n := n + 1) (h ⨟ Term.inr B (Term.sigmaTy B n)) := by
  obtain ⟨m, hm, C, iota, sigma, fs, hinj, hap, hsig, hret, hfs, he⟩ := hh
  refine ⟨m, fun i => (Sum.inr (hm i) : ⟦Ty.finAlph (n + 1)⟧), C, iota, sigma, fs,
    -- the map into the larger alphabet is injective
    fun a b hab => hinj (Sum.inr_injective hab), hap, hsig, hret, hfs, ?_⟩
  calc (sigma ⨟ (h ⨟ Term.inr B (Term.sigmaTy B n)))
      ≡ₜ ((sigma ⨟ h) ⨟ Term.inr B (Term.sigmaTy B n)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma B (hm i)) ⨟
          Term.inr B (Term.sigmaTy B n)) := PEq.compL _ he
    _ ≡ₜ Term.sigmaCase (fun i => (fs i ⨟ Term.injSigma B (hm i)) ⨟
          Term.inr B (Term.sigmaTy B n)) := sigmaCase_comp _ _
    _ ≡ₜ Term.sigmaCase
          (fun i => fs i ⨟ Term.injSigma (n := n + 1) B (Sum.inr (hm i))) :=
        sigmaCase_congr (fun i => PEq.comp_assoc _ _ _)

end HasGroupInjection

/-! ### Grouping of summands

The one-sided inverse of the co-pairing of two group injections has to be chosen with care,
which is what the next two lemmas do, one for each of the two components of the type `C`.
On a variant of the union that the component's own subset uses, the inverse is the
co-projection — this is what makes it a one-sided inverse; on the other variants it is a
constant of the *other* component, chosen in the summand that the other subset attaches to
that variant, so that the composition with the drop still lands in the intended variant. -/

/-- The component of the retraction on the first summand of `C = C₁ + C₂`. -/
theorem exists_retract_left {B C₁ C₂ : Ty} {n m m₁ m₂ : ℕ}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    {hm₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph n⟧} {hm₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph n⟧}
    {u₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph m⟧} {u₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph m⟧}
    (hu₁ : ∀ i, hm (u₁ i) = hm₁ i) (hu₂ : ∀ j, hm (u₂ j) = hm₂ j)
    (hinj₁ : Function.Injective hm₁)
    {E₁ : Term (Term.sigmaTy C₁ m₁) (Term.sigmaTy B n)}
    {E₂ : Term (Term.sigmaTy C₂ m₂) (Term.sigmaTy B n)}
    {fs₁ : ⟦Ty.finAlph m₁⟧ → Term C₁ B} {fs₂ : ⟦Ty.finAlph m₂⟧ → Term C₂ B}
    (hfs₁ : ∀ i, IsDrop (fs₁ i)) (hfs₂ : ∀ j, IsDrop (fs₂ j))
    (hE₁ : E₁ ≡ₜ Term.sigmaCase (fun i => fs₁ i ⨟ Term.injSigma B (hm₁ i)))
    (hE₂ : E₂ ≡ₜ Term.sigmaCase (fun j => fs₂ j ⨟ Term.injSigma B (hm₂ j)))
    (k : ⟦Ty.finAlph m⟧) (hk : (∃ i, u₁ i = k) ∨ ∃ j, u₂ j = k) :
    ∃ (a : Term C₁ (Term.sigmaTy C₁ m₁ ⊕' Term.sigmaTy C₂ m₂)) (c : Term C₁ B),
      IsDrop a ∧ IsDrop c ∧
      (∀ i, u₁ i = k → a ≡ₜ (Term.injSigma C₁ i ⨟ Term.inl _ _)) ∧
      (a ⨟ Term.either E₁ E₂) ≡ₜ (c ⨟ Term.injSigma B (hm k)) := by
  classical
  by_cases hcase : ∃ i, u₁ i = k
  · obtain ⟨i₀, hi₀⟩ := hcase
    subst hi₀
    refine ⟨Term.injSigma C₁ i₀ ⨟ Term.inl _ _, fs₁ i₀,
      IsDrop.comp (isDrop_injSigma C₁ i₀) (IsDrop.inl _ _), hfs₁ i₀, ?_, ?_⟩
    · intro i hi
      have hii : i = i₀ := by
        refine hinj₁ ?_
        rw [← hu₁ i, ← hu₁ i₀, hi]
      subst hii
      exact PEq.refl _
    · rw [hu₁ i₀]
      calc ((Term.injSigma C₁ i₀ ⨟ Term.inl _ _) ⨟ Term.either E₁ E₂)
          ≡ₜ (Term.injSigma C₁ i₀ ⨟ (Term.inl _ _ ⨟ Term.either E₁ E₂)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.injSigma C₁ i₀ ⨟ E₁) := PEq.compR _ (inl_either _ _)
        _ ≡ₜ (Term.injSigma C₁ i₀ ⨟
              Term.sigmaCase (fun i => fs₁ i ⨟ Term.injSigma B (hm₁ i))) :=
            PEq.compR _ hE₁
        _ ≡ₜ (fs₁ i₀ ⨟ Term.injSigma B (hm₁ i₀)) := injSigma_sigmaCase _ _
  · obtain ⟨j₀, hj₀⟩ := hk.resolve_left hcase
    subst hj₀
    refine ⟨Term.anyTerm C₁ C₂ ⨟ (Term.injSigma C₂ j₀ ⨟ Term.inr _ _),
      Term.anyTerm C₁ C₂ ⨟ fs₂ j₀,
      IsDrop.comp (isDrop_anyTerm C₁ C₂)
        (IsDrop.comp (isDrop_injSigma C₂ j₀) (IsDrop.inr _ _)),
      IsDrop.comp (isDrop_anyTerm C₁ C₂) (hfs₂ j₀), ?_, ?_⟩
    · intro i hi
      exact absurd ⟨i, hi⟩ hcase
    · rw [hu₂ j₀]
      calc ((Term.anyTerm C₁ C₂ ⨟ (Term.injSigma C₂ j₀ ⨟ Term.inr _ _)) ⨟
              Term.either E₁ E₂)
          ≡ₜ (Term.anyTerm C₁ C₂ ⨟ ((Term.injSigma C₂ j₀ ⨟ Term.inr _ _) ⨟
              Term.either E₁ E₂)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.anyTerm C₁ C₂ ⨟ (Term.injSigma C₂ j₀ ⨟
              (Term.inr _ _ ⨟ Term.either E₁ E₂))) :=
            PEq.compR _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.anyTerm C₁ C₂ ⨟ (Term.injSigma C₂ j₀ ⨟ E₂)) :=
            PEq.compR _ (PEq.compR _ (inr_either _ _))
        _ ≡ₜ (Term.anyTerm C₁ C₂ ⨟ (Term.injSigma C₂ j₀ ⨟
              Term.sigmaCase (fun j => fs₂ j ⨟ Term.injSigma B (hm₂ j)))) :=
            PEq.compR _ (PEq.compR _ hE₂)
        _ ≡ₜ (Term.anyTerm C₁ C₂ ⨟ (fs₂ j₀ ⨟ Term.injSigma B (hm₂ j₀))) :=
            PEq.compR _ (injSigma_sigmaCase _ _)
        _ ≡ₜ ((Term.anyTerm C₁ C₂ ⨟ fs₂ j₀) ⨟ Term.injSigma B (hm₂ j₀)) :=
            PEq.symm (PEq.comp_assoc _ _ _)

/-- The component of the retraction on the second summand of `C = C₁ + C₂`. -/
theorem exists_retract_right {B C₁ C₂ : Ty} {n m m₁ m₂ : ℕ}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    {hm₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph n⟧} {hm₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph n⟧}
    {u₁ : ⟦Ty.finAlph m₁⟧ → ⟦Ty.finAlph m⟧} {u₂ : ⟦Ty.finAlph m₂⟧ → ⟦Ty.finAlph m⟧}
    (hu₁ : ∀ i, hm (u₁ i) = hm₁ i) (hu₂ : ∀ j, hm (u₂ j) = hm₂ j)
    (hinj₂ : Function.Injective hm₂)
    {E₁ : Term (Term.sigmaTy C₁ m₁) (Term.sigmaTy B n)}
    {E₂ : Term (Term.sigmaTy C₂ m₂) (Term.sigmaTy B n)}
    {fs₁ : ⟦Ty.finAlph m₁⟧ → Term C₁ B} {fs₂ : ⟦Ty.finAlph m₂⟧ → Term C₂ B}
    (hfs₁ : ∀ i, IsDrop (fs₁ i)) (hfs₂ : ∀ j, IsDrop (fs₂ j))
    (hE₁ : E₁ ≡ₜ Term.sigmaCase (fun i => fs₁ i ⨟ Term.injSigma B (hm₁ i)))
    (hE₂ : E₂ ≡ₜ Term.sigmaCase (fun j => fs₂ j ⨟ Term.injSigma B (hm₂ j)))
    (k : ⟦Ty.finAlph m⟧) (hk : (∃ i, u₁ i = k) ∨ ∃ j, u₂ j = k) :
    ∃ (b : Term C₂ (Term.sigmaTy C₁ m₁ ⊕' Term.sigmaTy C₂ m₂)) (c : Term C₂ B),
      IsDrop b ∧ IsDrop c ∧
      (∀ j, u₂ j = k → b ≡ₜ (Term.injSigma C₂ j ⨟ Term.inr _ _)) ∧
      (b ⨟ Term.either E₁ E₂) ≡ₜ (c ⨟ Term.injSigma B (hm k)) := by
  classical
  by_cases hcase : ∃ j, u₂ j = k
  · obtain ⟨j₀, hj₀⟩ := hcase
    subst hj₀
    refine ⟨Term.injSigma C₂ j₀ ⨟ Term.inr _ _, fs₂ j₀,
      IsDrop.comp (isDrop_injSigma C₂ j₀) (IsDrop.inr _ _), hfs₂ j₀, ?_, ?_⟩
    · intro j hj
      have hjj : j = j₀ := by
        refine hinj₂ ?_
        rw [← hu₂ j, ← hu₂ j₀, hj]
      subst hjj
      exact PEq.refl _
    · rw [hu₂ j₀]
      calc ((Term.injSigma C₂ j₀ ⨟ Term.inr _ _) ⨟ Term.either E₁ E₂)
          ≡ₜ (Term.injSigma C₂ j₀ ⨟ (Term.inr _ _ ⨟ Term.either E₁ E₂)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.injSigma C₂ j₀ ⨟ E₂) := PEq.compR _ (inr_either _ _)
        _ ≡ₜ (Term.injSigma C₂ j₀ ⨟
              Term.sigmaCase (fun j => fs₂ j ⨟ Term.injSigma B (hm₂ j))) :=
            PEq.compR _ hE₂
        _ ≡ₜ (fs₂ j₀ ⨟ Term.injSigma B (hm₂ j₀)) := injSigma_sigmaCase _ _
  · obtain ⟨i₀, hi₀⟩ := hk.resolve_right hcase
    subst hi₀
    refine ⟨Term.anyTerm C₂ C₁ ⨟ (Term.injSigma C₁ i₀ ⨟ Term.inl _ _),
      Term.anyTerm C₂ C₁ ⨟ fs₁ i₀,
      IsDrop.comp (isDrop_anyTerm C₂ C₁)
        (IsDrop.comp (isDrop_injSigma C₁ i₀) (IsDrop.inl _ _)),
      IsDrop.comp (isDrop_anyTerm C₂ C₁) (hfs₁ i₀), ?_, ?_⟩
    · intro j hj
      exact absurd ⟨j, hj⟩ hcase
    · rw [hu₁ i₀]
      calc ((Term.anyTerm C₂ C₁ ⨟ (Term.injSigma C₁ i₀ ⨟ Term.inl _ _)) ⨟
              Term.either E₁ E₂)
          ≡ₜ (Term.anyTerm C₂ C₁ ⨟ ((Term.injSigma C₁ i₀ ⨟ Term.inl _ _) ⨟
              Term.either E₁ E₂)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.anyTerm C₂ C₁ ⨟ (Term.injSigma C₁ i₀ ⨟
              (Term.inl _ _ ⨟ Term.either E₁ E₂))) :=
            PEq.compR _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.anyTerm C₂ C₁ ⨟ (Term.injSigma C₁ i₀ ⨟ E₁)) :=
            PEq.compR _ (PEq.compR _ (inl_either _ _))
        _ ≡ₜ (Term.anyTerm C₂ C₁ ⨟ (Term.injSigma C₁ i₀ ⨟
              Term.sigmaCase (fun i => fs₁ i ⨟ Term.injSigma B (hm₁ i)))) :=
            PEq.compR _ (PEq.compR _ hE₁)
        _ ≡ₜ (Term.anyTerm C₂ C₁ ⨟ (fs₁ i₀ ⨟ Term.injSigma B (hm₁ i₀))) :=
            PEq.compR _ (injSigma_sigmaCase _ _)
        _ ≡ₜ ((Term.anyTerm C₂ C₁ ⨟ fs₁ i₀) ⨟ Term.injSigma B (hm₁ i₀)) :=
            PEq.symm (PEq.comp_assoc _ _ _)

/-- **Grouping of summands.**  The co-pairing of two annotation-diagonal drops is
annotation-diagonal, for the union of the two subsets of the group. -/
theorem HasGroupInjection.either {A₁ A₂ B : Ty} {n : ℕ} {f₁ : Term A₁ (Term.sigmaTy B n)}
    {f₂ : Term A₂ (Term.sigmaTy B n)} (h₁ : HasGroupInjection f₁)
    (h₂ : HasGroupInjection f₂) : HasGroupInjection (Term.either f₁ f₂) := by
  classical
  obtain ⟨m₁, hm₁, C₁, iota₁, sigma₁, fs₁, hinj₁, hap₁, hsig₁, hret₁, hfs₁, he₁⟩ :=
    h₁
  obtain ⟨m₂, hm₂, C₂, iota₂, sigma₂, fs₂, hinj₂, hap₂, hsig₂, hret₂, hfs₂, he₂⟩ :=
    h₂
  obtain ⟨m, hm, u₁, u₂, hinj, hu₁, hu₂, hsurj⟩ := exists_union_enum hm₁ hm₂
  choose aa cs₁ haaD hcs₁D haaP haaE using fun k =>
    exists_retract_left (E₁ := sigma₁ ⨟ f₁) (E₂ := sigma₂ ⨟ f₂)
      hu₁ hu₂ hinj₁ hfs₁ hfs₂ he₁ he₂ k (hsurj k)
  choose bb cs₂ hbbD hcs₂D hbbP hbbE using fun k =>
    exists_retract_right (E₁ := sigma₁ ⨟ f₁) (E₂ := sigma₂ ⨟ f₂)
      hu₁ hu₂ hinj₂ hfs₁ hfs₂ he₁ he₂ k (hsurj k)
  set ellL : Term (Term.sigmaTy C₁ m₁) (Term.sigmaTy (C₁ ⊕' C₂) m) :=
    Term.sigmaCase (fun i => Term.inl C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₁ i)) with hellL
  set ellR : Term (Term.sigmaTy C₂ m₂) (Term.sigmaTy (C₁ ⊕' C₂) m) :=
    Term.sigmaCase (fun j => Term.inr C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₂ j)) with hellR
  set J : Term (Term.sigmaTy C₁ m₁ ⊕' Term.sigmaTy C₂ m₂) (Term.sigmaTy (C₁ ⊕' C₂) m) :=
    Term.either ellL ellR with hJdef
  set K : Term (Term.sigmaTy (C₁ ⊕' C₂) m) (Term.sigmaTy C₁ m₁ ⊕' Term.sigmaTy C₂ m₂) :=
    Term.sigmaCase (fun k => Term.either (aa k) (bb k)) with hKdef
  have hJap : IsAperiodic J := by
    have hL : IsAperiodic ellL :=
      isAperiodic_sigmaCase (fun i => by
        simpa [Term.isAperiodic_comp] using
          ⟨show IsAperiodic (Term.inl C₁ C₂) by simp [IsAperiodic, Term.usesPref],
            isAperiodic_injSigma (C₁ ⊕' C₂) (u₁ i)⟩)
    have hR : IsAperiodic ellR :=
      isAperiodic_sigmaCase (fun j => by
        simpa [Term.isAperiodic_comp] using
          ⟨show IsAperiodic (Term.inr C₁ C₂) by simp [IsAperiodic, Term.usesPref],
            isAperiodic_injSigma (C₁ ⊕' C₂) (u₂ j)⟩)
    simp only [hJdef, IsAperiodic, Term.either, Term.usesPref, Bool.or_eq_false_iff] at hL hR ⊢
    exact ⟨⟨hL, hR⟩, trivial⟩
  have hK : IsDrop K := isDrop_sigmaCase (fun k => isDrop_either (haaD k) (hbbD k))
  have hKcase : ∀ k, (Term.injSigma (C₁ ⊕' C₂) k ⨟ K) ≡ₜ Term.either (aa k) (bb k) :=
    fun k => injSigma_sigmaCase _ _
  have hellLK : (ellL ⨟ K) ≡ₜ Term.inl (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂) := by
    calc (ellL ⨟ K)
        ≡ₜ Term.sigmaCase
            (fun i => (Term.inl C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₁ i)) ⨟ K) :=
          sigmaCase_comp _ _
      _ ≡ₜ Term.sigmaCase (fun i => Term.injSigma C₁ i ⨟
            Term.inl (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) := by
          refine sigmaCase_congr (fun i => ?_)
          calc ((Term.inl C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₁ i)) ⨟ K)
              ≡ₜ (Term.inl C₁ C₂ ⨟ (Term.injSigma (C₁ ⊕' C₂) (u₁ i) ⨟ K)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.inl C₁ C₂ ⨟ Term.either (aa (u₁ i)) (bb (u₁ i))) :=
                PEq.compR _ (hKcase (u₁ i))
            _ ≡ₜ aa (u₁ i) := inl_either _ _
            _ ≡ₜ (Term.injSigma C₁ i ⨟ Term.inl _ _) := haaP (u₁ i) i rfl
      _ ≡ₜ (Term.sigmaCase (fun i => Term.injSigma C₁ i) ⨟
            Term.inl (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) :=
          PEq.symm (sigmaCase_comp _ _)
      _ ≡ₜ (Term.id (Term.sigmaTy C₁ m₁) ⨟
            Term.inl (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) :=
          PEq.compL _ (sigmaCase_injSigma C₁ m₁)
      _ ≡ₜ Term.inl (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂) := PEq.id_comp _
  have hellRK : (ellR ⨟ K) ≡ₜ Term.inr (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂) := by
    calc (ellR ⨟ K)
        ≡ₜ Term.sigmaCase
            (fun j => (Term.inr C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₂ j)) ⨟ K) :=
          sigmaCase_comp _ _
      _ ≡ₜ Term.sigmaCase (fun j => Term.injSigma C₂ j ⨟
            Term.inr (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) := by
          refine sigmaCase_congr (fun j => ?_)
          calc ((Term.inr C₁ C₂ ⨟ Term.injSigma (C₁ ⊕' C₂) (u₂ j)) ⨟ K)
              ≡ₜ (Term.inr C₁ C₂ ⨟ (Term.injSigma (C₁ ⊕' C₂) (u₂ j) ⨟ K)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.inr C₁ C₂ ⨟ Term.either (aa (u₂ j)) (bb (u₂ j))) :=
                PEq.compR _ (hKcase (u₂ j))
            _ ≡ₜ bb (u₂ j) := inr_either _ _
            _ ≡ₜ (Term.injSigma C₂ j ⨟ Term.inr _ _) := hbbP (u₂ j) j rfl
      _ ≡ₜ (Term.sigmaCase (fun j => Term.injSigma C₂ j) ⨟
            Term.inr (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) :=
          PEq.symm (sigmaCase_comp _ _)
      _ ≡ₜ (Term.id (Term.sigmaTy C₂ m₂) ⨟
            Term.inr (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂)) :=
          PEq.compL _ (sigmaCase_injSigma C₂ m₂)
      _ ≡ₜ Term.inr (Term.sigmaTy C₁ m₁) (Term.sigmaTy C₂ m₂) := PEq.id_comp _
  have hJK : (J ⨟ K) ≡ₜ Term.id (Term.sigmaTy C₁ m₁ ⊕' Term.sigmaTy C₂ m₂) := by
    refine Term.either_ext _ _ ?_ ?_
    · calc (Term.inl _ _ ⨟ (J ⨟ K)) ≡ₜ ((Term.inl _ _ ⨟ J) ⨟ K) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (ellL ⨟ K) := PEq.compL _ (inl_either _ _)
        _ ≡ₜ Term.inl _ _ := hellLK
        _ ≡ₜ (Term.inl _ _ ⨟ Term.id _) := PEq.symm (PEq.comp_id _)
    · calc (Term.inr _ _ ⨟ (J ⨟ K)) ≡ₜ ((Term.inr _ _ ⨟ J) ⨟ K) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (ellR ⨟ K) := PEq.compL _ (inr_either _ _)
        _ ≡ₜ Term.inr _ _ := hellRK
        _ ≡ₜ (Term.inr _ _ ⨟ Term.id _) := PEq.symm (PEq.comp_id _)
  refine ⟨m, hm, C₁ ⊕' C₂, Term.sumF iota₁ iota₂ ⨟ J, K ⨟ Term.sumF sigma₁ sigma₂,
    fun k => Term.either (cs₁ k) (cs₂ k), hinj,
    by simpa [Term.isAperiodic_comp, Term.isAperiodic_sumF] using ⟨⟨hap₁, hap₂⟩, hJap⟩,
    IsDrop.comp hK (IsDrop.sumF hsig₁ hsig₂), ?_,
    fun k => isDrop_either (hcs₁D k) (hcs₂D k), ?_⟩
  · calc ((Term.sumF iota₁ iota₂ ⨟ J) ⨟ (K ⨟ Term.sumF sigma₁ sigma₂))
        ≡ₜ (Term.sumF iota₁ iota₂ ⨟ Term.sumF sigma₁ sigma₂) := comp_cancel_mid hJK
      _ ≡ₜ Term.sumF (iota₁ ⨟ sigma₁) (iota₂ ⨟ sigma₂) := PEq.sum_comp _ _ _ _
      _ ≡ₜ Term.sumF (Term.id A₁) (Term.id A₂) := PEq.congr_sumF hret₁ hret₂
      _ ≡ₜ Term.id (A₁ ⊕' A₂) := PEq.sum_id _ _
  calc ((K ⨟ Term.sumF sigma₁ sigma₂) ⨟ Term.either f₁ f₂)
      ≡ₜ (K ⨟ (Term.sumF sigma₁ sigma₂ ⨟ Term.either f₁ f₂)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (K ⨟ Term.either (sigma₁ ⨟ f₁) (sigma₂ ⨟ f₂)) :=
        PEq.compR _ (sumF_either _ _ _ _)
    _ ≡ₜ Term.sigmaCase (fun k => Term.either (aa k) (bb k) ⨟
          Term.either (sigma₁ ⨟ f₁) (sigma₂ ⨟ f₂)) := sigmaCase_comp _ _
    _ ≡ₜ Term.sigmaCase (fun k => Term.either
          (aa k ⨟ Term.either (sigma₁ ⨟ f₁) (sigma₂ ⨟ f₂))
          (bb k ⨟ Term.either (sigma₁ ⨟ f₁) (sigma₂ ⨟ f₂))) :=
        sigmaCase_congr (fun k => either_comp _ _ _)
    _ ≡ₜ Term.sigmaCase (fun k => Term.either (cs₁ k ⨟ Term.injSigma B (hm k))
          (cs₂ k ⨟ Term.injSigma B (hm k))) :=
        sigmaCase_congr (fun k => either_congr (haaE k) (hbbE k))
    _ ≡ₜ Term.sigmaCase (fun k => Term.either (cs₁ k) (cs₂ k) ⨟
          Term.injSigma B (hm k)) :=
        sigmaCase_congr (fun k => PEq.symm (either_comp _ _ _))

/-! ### The induction -/

theorem hasGroupInjection_leafStep {B : Ty} {n r : ℕ}
    (ih : ∀ {Y : Ty} (h : Term Y (Term.sigmaTy B n)), IsDrop h → HasGroupInjection h) :
    {A : Ty} → {M : Term A (Term.sigmaTy B (n + 1))} → IsSumLeaf r M → HasGroupInjection M
  | _, _, .inl (g := g) hg _ => HasGroupInjection.leaf hg (n := n + 1) (.inl ())
  | _, _, .inr (g := h) hh _ => (ih h hh).inr

theorem hasGroupInjection_normalStep {B : Ty} {n r : ℕ}
    (ih : ∀ {Y : Ty} (h : Term Y (Term.sigmaTy B n)), IsDrop h → HasGroupInjection h) :
    {A : Ty} → {M : Term A (Term.sigmaTy B (n + 1))} → IsNormalSumVec r M →
      HasGroupInjection M
  | _, _, .single hl => hasGroupInjection_leafStep ih hl
  | _, _, .cons hl ht =>
      (hasGroupInjection_leafStep ih hl).either (hasGroupInjection_normalStep ih ht)

/-- **Lemma (Group injection)** (appendix, *Completeness in the presence of groups*).
Every drop `f : A ⇒ Σ B` is annotation-diagonal after its domain has been injected into a
co-product `Σ_H C` indexed by a subset `H` of the group. -/
theorem hasGroupInjection_of_isDrop : (n : ℕ) → {A B : Ty} → (f : Term A (Term.sigmaTy B n)) →
    IsDrop f → HasGroupInjection f
  | 0, A, B, f, hf =>
      ⟨0, fun _ => (), A, Term.id A, Term.id A, fun _ => f, (by rintro ⟨⟩ ⟨⟩ _; rfl),
        (by simp [IsAperiodic, Term.usesPref]), IsDrop.id A, PEq.id_comp _, fun _ => hf,
        (PEq.id_comp _).trans (PEq.symm (PEq.comp_id _))⟩
  | (n + 1), _, _, f, hf => by
      obtain ⟨D, alpha, N, halpha, -, hN, he⟩ := drops_with_sum_codomain f hf
      exact HasGroupInjection.congr he
        (HasGroupInjection.of_lift_comp halpha
          (hasGroupInjection_normalStep (fun h hh => hasGroupInjection_of_isDrop n h hh) hN))

end Lax149335Proofs

bridge_export Lax149335Proofs
