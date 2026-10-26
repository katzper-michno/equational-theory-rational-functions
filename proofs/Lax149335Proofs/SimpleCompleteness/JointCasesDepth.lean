import Lax149335Proofs.SimpleCompleteness.ValueExtraction

/-!
# Joint case decompositions with a bound on the list nesting depth of the components

`Lax149335Proofs.JointCases` (in `Lax149335Proofs.SimpleCompleteness.Conjugacy`) records a joint decomposition of
two terms into co-pairings, and asks every re-organisation of the input type to be
non-increasing for the list nesting depth.  The proof of value extraction has to pass through
*intermediate* input types of a larger nesting depth (the `block` isomorphism increases the
nesting depth by one), even though the components it finally produces do not.

The variant of this file therefore records the bound on the list nesting depth at the
components: `JointCasesD B P d T S` says that `T` and `S` are provably co-pairings, along a
common re-organisation of the input type by provable isomorphisms of any nesting depth, of
components that are related by `P` and whose input types have nesting depth at most `d`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- A joint decomposition of two terms into co-pairings of components related by `P`, whose
input types have list nesting depth at most `d`. -/
inductive JointCasesD (B : Ty) (P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop) (d : ℕ) :
    {X : Ty} → Term X B⋆ → Term X B⋆ → Prop
  /-- A single component, of list nesting depth at most `d`. -/
  | leaf {X : Ty} {T S : Term X B⋆} : X.listDepth ≤ d → P T S → JointCasesD B P d T S
  /-- Two decompositions of the two cases of a co-pairing. -/
  | node {X₁ X₂ : Ty} {T₁ S₁ : Term X₁ B⋆} {T₂ S₂ : Term X₂ B⋆} :
      JointCasesD B P d T₁ S₁ → JointCasesD B P d T₂ S₂ →
      JointCasesD B P d (Term.either T₁ T₂) (Term.either S₁ S₂)
  /-- Re-organising the input type by a provable isomorphism. -/
  | precomp {X Y : Ty} {q : Term Y X} {T S : Term X B⋆} : ProvableIso q →
      JointCasesD B P d (q ⨟ T) (q ⨟ S) → JointCasesD B P d T S
  /-- Provable equality of the two terms. -/
  | congr {X : Ty} {T T' S S' : Term X B⋆} : T ≡ₜ T' → S ≡ₜ S' →
      JointCasesD B P d T' S' → JointCasesD B P d T S

namespace JointCasesD

variable {B : Ty}

/-- The bound on the nesting depth of the components can be relaxed. -/
theorem mono_d {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d d' : ℕ} (hd : d ≤ d') :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S → JointCasesD B P d' T S := by
  intro X T S h
  induction h with
  | leaf hX hP => exact leaf (le_trans hX hd) hP
  | node _ _ ih₁ ih₂ => exact node ih₁ ih₂
  | precomp hq _ ih => exact precomp hq ih
  | congr h₁ h₂ _ ih => exact congr h₁ h₂ ih

/-- Every joint decomposition in the sense of `Lax149335Proofs.JointCases` bounds the nesting depth
of its components by the nesting depth of the input type. -/
theorem of_jointCases {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} :
    {X : Ty} → {T S : Term X B⋆} → JointCases B P T S → JointCasesD B P X.listDepth T S := by
  intro X T S h
  induction h with
  | leaf hP => exact leaf le_rfl hP
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      refine node (mono_d ?_ ih₁) (mono_d ?_ ih₂) <;> simp [Ty.listDepth]
  | precomp hq hd _ ih => exact precomp hq (mono_d hd ih)
  | congr h₁ h₂ _ ih => exact congr h₁ h₂ ih

/-- A relation between the denotations of the two terms that is inherited by the components
can be added to the relation on the components. -/
theorem addRel {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ}
    (R : List ⟦B⟧ → List ⟦B⟧ → Prop) :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S → (∀ x : ⟦X⟧, R (T.den x) (S.den x)) →
      JointCasesD B (fun {Y} T S => P T S ∧ ∀ x : ⟦Y⟧, R (T.den x) (S.den x)) d T S := by
  intro X T S h
  induction h with
  | leaf hX hP => exact fun hR => leaf hX ⟨hP, hR⟩
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      intro hR
      refine node (ih₁ ?_) (ih₂ ?_)
      · intro x
        have := hR (Sum.inl x)
        simpa [Term.either] using this
      · intro x
        have := hR (Sum.inr x)
        simpa [Term.either] using this
  | @precomp X Y q T S hq _ ih =>
      intro hR
      refine precomp hq (ih ?_)
      intro y
      simpa using hR (q.den y)
  | @congr X T T' S S' h₁ h₂ _ ih =>
      intro hR
      refine congr h₁ h₂ (ih ?_)
      intro x
      have e₁ := congrFun (PEq.sound h₁) x
      have e₂ := congrFun (PEq.sound h₂) x
      rw [← e₁, ← e₂]
      exact hR x

/-- **Flattening a joint decomposition into an `n`-ary co-pairing.**  Every joint
decomposition becomes an `n`-ary co-pairing after a provable isomorphism of the input type,
all of whose summands have list nesting depth at most `d`. -/
theorem toCopair {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ} :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S →
      ∃ (C₀ : Ty) (Cs : List Ty) (q : Term (sumTyOf C₀ Cs) X), ProvableIso q ∧
        C₀.listDepth ≤ d ∧ (∀ C ∈ Cs, C.listDepth ≤ d) ∧
        ∃ (T₀ S₀ : Term C₀ B⋆) (Ts Ss : Cases B⋆ Cs), P T₀ S₀ ∧ Cases.All2 P Ts Ss ∧
          (q ⨟ T) ≡ₜ copair T₀ Ts ∧ (q ⨟ S) ≡ₜ copair S₀ Ss := by
  intro X T S h
  induction h with
  | @leaf X T S hX hP =>
      exact ⟨X, [], Term.id X, ProvableIso.id X, hX, by simp, T, S, Cases.nil, Cases.nil,
        hP, trivial, PEq.id_comp _, PEq.id_comp _⟩
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      obtain ⟨C₀, Cs, q₁, hq₁, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll, hT, hS⟩ := ih₁
      obtain ⟨D₀, Ds, q₂, hq₂, he₀, hes, U₀, V₀, Us, Vs, hQ, hAll2, hU, hV⟩ := ih₂
      refine ⟨C₀, Cs ++ D₀ :: Ds, sumSplitTy C₀ Cs D₀ Ds ⨟ Term.sumF q₁ q₂,
        ProvableIso.comp (provableIso_sumSplitTy C₀ Cs D₀ Ds) (ProvableIso.sumF hq₁ hq₂),
        hd₀, ?_, T₀, S₀, Ts.append (Cases.cons U₀ Us), Ss.append (Cases.cons V₀ Vs), hP,
        Cases.all2_append Ts Ss (Cases.cons U₀ Us) (Cases.cons V₀ Vs) hAll ⟨hQ, hAll2⟩,
        ?_, ?_⟩
      · intro C hC
        simp only [List.mem_append, List.mem_cons] at hC
        rcases hC with hC | hC | hC
        · exact hds C hC
        · subst hC; exact he₀
        · exact hes C hC
      · calc ((sumSplitTy C₀ Cs D₀ Ds ⨟ Term.sumF q₁ q₂) ⨟ Term.either T₁ T₂)
            ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ (Term.sumF q₁ q₂ ⨟ Term.either T₁ T₂)) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ Term.either (q₁ ⨟ T₁) (q₂ ⨟ T₂)) :=
              PEq.compR _ (Term.sumF_either _ _ _ _)
          _ ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ Term.either (copair T₀ Ts) (copair U₀ Us)) :=
              PEq.compR _ (Term.either_congr hT hU)
          _ ≡ₜ copair T₀ (Ts.append (Cases.cons U₀ Us)) :=
              sumSplitTy_copair C₀ Cs D₀ Ds T₀ Ts U₀ Us
      · calc ((sumSplitTy C₀ Cs D₀ Ds ⨟ Term.sumF q₁ q₂) ⨟ Term.either S₁ S₂)
            ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ (Term.sumF q₁ q₂ ⨟ Term.either S₁ S₂)) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ Term.either (q₁ ⨟ S₁) (q₂ ⨟ S₂)) :=
              PEq.compR _ (Term.sumF_either _ _ _ _)
          _ ≡ₜ (sumSplitTy C₀ Cs D₀ Ds ⨟ Term.either (copair S₀ Ss) (copair V₀ Vs)) :=
              PEq.compR _ (Term.either_congr hS hV)
          _ ≡ₜ copair S₀ (Ss.append (Cases.cons V₀ Vs)) :=
              sumSplitTy_copair C₀ Cs D₀ Ds S₀ Ss V₀ Vs
  | @precomp X Y q T S hq _ ih =>
      obtain ⟨C₀, Cs, q₀, hq₀, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll, hT, hS⟩ := ih
      exact ⟨C₀, Cs, q₀ ⨟ q, ProvableIso.comp hq₀ hq, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll,
        (PEq.comp_assoc _ _ _).trans hT, (PEq.comp_assoc _ _ _).trans hS⟩
  | @congr X T T' S S' h₁ h₂ _ ih =>
      obtain ⟨C₀, Cs, q₀, hq₀, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll, hT, hS⟩ := ih
      exact ⟨C₀, Cs, q₀, hq₀, hd₀, hds, T₀, S₀, Ts, Ss, hP, hAll,
        (PEq.compR _ h₁).trans hT, (PEq.compR _ h₂).trans hS⟩

/-- Transporting a joint decomposition along a provable isomorphism of the input type. -/
theorem transportIso {P : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ} {X Y : Ty}
    {q : Term Y X} (hq : ProvableIso q) {T S : Term X B⋆} {T' S' : Term Y B⋆}
    (hT : (q ⨟ T) ≡ₜ T') (hS : (q ⨟ S) ≡ₜ S') (h : JointCasesD B P d T' S') :
    JointCasesD B P d T S :=
  precomp hq (congr hT hS h)

/-- A joint decomposition is preserved by concatenating a fixed pair of terms on the left,
given a joint decomposition of every component after the concatenation.  The step may use
the bound on the list nesting depth of the type of the component. -/
theorem fdot_left {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d d' : ℕ} {W : Ty}
    (f g : Term W B⋆)
    (hstep : ∀ {Y : Ty} (T S : Term Y B⋆), Y.listDepth ≤ d → P T S →
      JointCasesD B P' d' (f ⊙ T) (g ⊙ S)) :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S →
      JointCasesD B P' d' (f ⊙ T) (g ⊙ S) := by
  intro X T S hTS
  induction hTS with
  | leaf hX hP => exact hstep _ _ hX hP
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      refine congr (Term.fdot_either_distR f T₁ T₂) (Term.fdot_either_distR g S₁ S₂) ?_
      refine precomp (ProvableIso.undistR W X₁ X₂) (congr ?_ ?_ (node ih₁ ih₂))
      · exact (PEq.comp_assoc _ _ _).symm.trans
          ((PEq.compL _ (PEq.undistR_distR W X₁ X₂)).trans (PEq.id_comp _))
      · exact (PEq.comp_assoc _ _ _).symm.trans
          ((PEq.compL _ (PEq.undistR_distR W X₁ X₂)).trans (PEq.id_comp _))
  | @precomp X Y q T S hq _ ih =>
      refine precomp (ProvableIso.prodF (ProvableIso.id W) hq) (congr ?_ ?_ ih)
      · exact Term.fdot_comp_right f q T
      · exact Term.fdot_comp_right g q S
  | congr h₁ h₂ _ ih =>
      exact congr (Term.fdot_congr (PEq.refl _) h₁) (Term.fdot_congr (PEq.refl _) h₂) ih

/-- A joint decomposition is preserved by concatenating a fixed pair of terms on the right,
given a joint decomposition of every component after the concatenation. -/
theorem fdot_right {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d d' : ℕ} {W : Ty}
    (f g : Term W B⋆)
    (hstep : ∀ {Y : Ty} (T S : Term Y B⋆), Y.listDepth ≤ d → P T S →
      JointCasesD B P' d' (T ⊙ f) (S ⊙ g)) :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S →
      JointCasesD B P' d' (T ⊙ f) (S ⊙ g) := by
  intro X T S hTS
  induction hTS with
  | leaf hX hP => exact hstep _ _ hX hP
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      refine congr (Term.fdot_either_distL T₁ T₂ f) (Term.fdot_either_distL S₁ S₂ g) ?_
      refine precomp (ProvableIso.undistL X₁ X₂ W) (congr ?_ ?_ (node ih₁ ih₂))
      · exact (PEq.comp_assoc _ _ _).symm.trans
          ((PEq.compL _ (PEq.undistL_distL X₁ X₂ W)).trans (PEq.id_comp _))
      · exact (PEq.comp_assoc _ _ _).symm.trans
          ((PEq.compL _ (PEq.undistL_distL X₁ X₂ W)).trans (PEq.id_comp _))
  | @precomp X Y q T S hq _ ih =>
      refine precomp (ProvableIso.prodF hq (ProvableIso.id W)) (congr ?_ ?_ ih)
      · exact Term.fdot_comp_left f q T
      · exact Term.fdot_comp_left g q S
  | congr h₁ h₂ _ ih =>
      exact congr (Term.fdot_congr h₁ (PEq.refl _)) (Term.fdot_congr h₂ (PEq.refl _)) ih

/-- A joint decomposition is preserved by concatenating values on both sides. -/
theorem dotLR {P P' : {Y : Ty} → Term Y B⋆ → Term Y B⋆ → Prop} {d : ℕ} (a b c e : Value B⋆)
    (hstep : ∀ {Y : Ty} (T S : Term Y B⋆), P T S →
      P' (Term.dotR (Term.dotL a T) b) (Term.dotR (Term.dotL c S) e)) :
    {X : Ty} → {T S : Term X B⋆} → JointCasesD B P d T S →
      JointCasesD B P' d (Term.dotR (Term.dotL a T) b) (Term.dotR (Term.dotL c S) e) := by
  intro X T S hTS
  induction hTS with
  | leaf hX hP => exact leaf hX (hstep _ _ hP)
  | @node X₁ X₂ T₁ S₁ T₂ S₂ _ _ ih₁ ih₂ =>
      have key : ∀ {Y₁ Y₂ : Ty} (u : Value B⋆) (u' : Value B⋆) (U₁ : Term Y₁ B⋆)
          (U₂ : Term Y₂ B⋆),
          Term.dotR (Term.dotL u (Term.either U₁ U₂)) u' ≡ₜ
            Term.either (Term.dotR (Term.dotL u U₁) u') (Term.dotR (Term.dotL u U₂) u') := by
        intro Y₁ Y₂ u u' U₁ U₂
        exact (Term.dotR_congr (Term.dotL_either u U₁ U₂) (PEq.refl _)).trans
          (Term.dotR_either _ _ _)
      exact congr (key a b T₁ T₂) (key c e S₁ S₂) (node ih₁ ih₂)
  | @precomp X Y q T S hq _ ih =>
      refine precomp hq (congr ?_ ?_ ih)
      · exact (Term.comp_dotR q (Term.dotL a T) b).trans
          (Term.dotR_congr (Term.comp_dotL q a T) (PEq.refl b))
      · exact (Term.comp_dotR q (Term.dotL c S) e).trans
          (Term.dotR_congr (Term.comp_dotL q c S) (PEq.refl e))
  | congr h₁ h₂ _ ih =>
      exact congr (Term.dotR_congr (Term.dotL_congr (PEq.refl _) h₁) (PEq.refl _))
        (Term.dotR_congr (Term.dotL_congr (PEq.refl _) h₂) (PEq.refl _)) ih

end JointCasesD

/-- A matching pair of co-pairings of `k`-guarded nonempty terms is a joint decomposition
into `k`-guarded nonempty components. -/
theorem KCopair2.toJointCasesD {B : Ty} {k : ℕ} :
    {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G →
      JointCasesD B (fun {Y} (T S : Term Y B⋆) => KGuarded k B T ∧ KGuarded k B S ∧
        NonemptyOutput T ∧ NonemptyOutput S) X.listDepth F G := by
  intro X F G h
  induction h with
  | leaf hf hg hnf hng => exact JointCasesD.leaf le_rfl ⟨hf, hg, hnf, hng⟩
  | @node X₁ X₂ f₁ g₁ f₂ g₂ _ _ ih₁ ih₂ =>
      refine JointCasesD.node (JointCasesD.mono_d ?_ ih₁) (JointCasesD.mono_d ?_ ih₂) <;>
        simp [Ty.listDepth]

end Lax149335Proofs

bridge_export Lax149335Proofs
