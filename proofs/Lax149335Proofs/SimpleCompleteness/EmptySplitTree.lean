import Lax149335Proofs.SimpleCompleteness.SumShuffle
import Lax149335Proofs.SimpleCompleteness.PeelIso

/-!
# Separating the empty summands of a joint decomposition

`Lax149335Proofs.empty_split` separates the empty summands of a pair of co-pairings of `k`-guarded
terms, but it only produces a retraction of the input type.  The proof of value extraction
needs a genuine provable isomorphism, and it needs the separation for a *tree* of joint
cases rather than for a flat co-pairing.  Both are provided by `Lax149335Proofs.SplitCopair` and
`Lax149335Proofs.JointCasesD.toSplitCopair` of this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- The bound on the list nesting depth of an optional summand. -/
def optListDepthLe : Option Ty → ℕ → Prop
  | none, _ => True
  | some E, d => E.listDepth ≤ d

/-- **The outcome of separating the empty summands.**  Either both terms are provably the
empty constant (and the input type is then provably isomorphic to a type of small list
nesting depth), or the input type is provably isomorphic to a co-product `E + N` of an
optional *empty* part `E`, on which both terms are the empty constant, and a *nonempty* part
`N`, on which they are matching co-pairings of `k`-guarded terms with nonempty outputs. -/
def SplitCopair (k : ℕ) (B : Ty) (d : ℕ) {X : Ty} (T S : Term X B⋆) : Prop :=
  (∃ (E : Ty) (rho : Term E X), ProvableIso rho ∧ E.listDepth ≤ d ∧
      T ≡ₜ nilconst B X ∧ S ≡ₜ nilconst B X) ∨
  (∃ (E : Option Ty) (N : Ty) (rho : Term (optSum E N) X), ProvableIso rho ∧
      optListDepthLe E d ∧ N.listDepth ≤ d ∧
      ∃ F F' : Term N B⋆, KCopair2 k B F F' ∧
        (rho ⨟ T) ≡ₜ optNilCase E N F ∧ (rho ⨟ S) ≡ₜ optNilCase E N F')

/-- Pre-composing the empty constant. -/
theorem Term.comp_nilconst {X Y B : Ty} (q : Term Y X) :
    (q ⨟ nilconst B X) ≡ₜ nilconst B Y :=
  (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- Pre-composing a term that is provably the empty constant. -/
theorem Term.comp_nilconst_of {X Y B : Ty} (q : Term Y X) {T : Term X B⋆}
    (h : T ≡ₜ nilconst B X) : (q ⨟ T) ≡ₜ nilconst B Y :=
  (PEq.compR _ h).trans (Term.comp_nilconst q)

/-- A term that becomes the empty constant after a provable isomorphism is the empty
constant. -/
theorem Term.nilconst_of_iso {X Y B : Ty} {q : Term Y X} (hq : ProvableIso q)
    {T : Term X B⋆} (h : (q ⨟ T) ≡ₜ nilconst B Y) : T ≡ₜ nilconst B X := by
  obtain ⟨q', -, hq'⟩ := hq
  calc T ≡ₜ (Term.id X ⨟ T) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((q' ⨟ q) ⨟ T) := PEq.compL _ (PEq.symm hq')
    _ ≡ₜ (q' ⨟ (q ⨟ T)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (q' ⨟ nilconst B Y) := PEq.compR _ h
    _ ≡ₜ nilconst B X := Term.comp_nilconst q'

namespace SplitCopair

variable {k : ℕ} {B : Ty} {d : ℕ}

/-- Transporting the outcome along a provable isomorphism of the input type. -/
theorem precomp {X Y : Ty} {q : Term Y X} (hq : ProvableIso q) {T S : Term X B⋆}
    (h : SplitCopair k B d (q ⨟ T) (q ⨟ S)) : SplitCopair k B d T S := by
  rcases h with ⟨E, r, hr, hd, h1, h2⟩ | ⟨E, N, r, hr, hE, hN, F, F', hK, h1, h2⟩
  · exact Or.inl ⟨E, r ⨟ q, ProvableIso.comp hr hq, hd,
      Term.nilconst_of_iso hq h1, Term.nilconst_of_iso hq h2⟩
  · exact Or.inr ⟨E, N, r ⨟ q, ProvableIso.comp hr hq, hE, hN, F, F', hK,
      (PEq.comp_assoc _ _ _).trans h1, (PEq.comp_assoc _ _ _).trans h2⟩

/-- The outcome only depends on the provable equivalence class of the two terms. -/
theorem congr {X : Ty} {T T' S S' : Term X B⋆} (hT : T ≡ₜ T') (hS : S ≡ₜ S')
    (h : SplitCopair k B d T' S') : SplitCopair k B d T S := by
  rcases h with ⟨E, r, hr, hd, h1, h2⟩ | ⟨E, N, r, hr, hE, hN, F, F', hK, h1, h2⟩
  · exact Or.inl ⟨E, r, hr, hd, hT.trans h1, hS.trans h2⟩
  · exact Or.inr ⟨E, N, r, hr, hE, hN, F, F', hK,
      (PEq.compR _ hT).trans h1, (PEq.compR _ hS).trans h2⟩

/-- **Combining the outcomes for the two cases of a co-pairing.** -/
theorem node {X₁ X₂ : Ty} {T₁ S₁ : Term X₁ B⋆} {T₂ S₂ : Term X₂ B⋆}
    (h₁ : SplitCopair k B d T₁ S₁) (h₂ : SplitCopair k B d T₂ S₂) :
    SplitCopair k B d (Term.either T₁ T₂) (Term.either S₁ S₂) := by
  rcases h₁ with ⟨E₁, r₁, hr₁, hd₁, hT₁, hS₁⟩ |
    ⟨E₁, N₁, r₁, hr₁, hE₁, hN₁, F₁, F₁', hK₁, hT₁, hS₁⟩
  · rcases h₂ with ⟨E₂, r₂, hr₂, hd₂, hT₂, hS₂⟩ |
      ⟨E₂, N₂, r₂, hr₂, hE₂, hN₂, F₂, F₂', hK₂, hT₂, hS₂⟩
    · -- both cases are empty
      refine Or.inl ⟨E₁ ⊕' E₂, Term.sumF r₁ r₂, ProvableIso.sumF hr₁ hr₂, ?_, ?_, ?_⟩
      · simp only [Ty.listDepth]; exact max_le hd₁ hd₂
      · exact (Term.either_congr hT₁ hT₂).trans (Term.either_nilconst X₁ X₂ B)
      · exact (Term.either_congr hS₁ hS₂).trans (Term.either_nilconst X₁ X₂ B)
    · -- the first case is empty, the second one splits
      cases E₂ with
      | none =>
          refine Or.inr ⟨some E₁, N₂, Term.sumF r₁ r₂, ProvableIso.sumF hr₁ hr₂, hd₁, hN₂,
            F₂, F₂', hK₂, ?_, ?_⟩
          · exact (Term.sumF_either _ _ _ _).trans
              (Term.either_congr (Term.comp_nilconst_of r₁ hT₁) hT₂)
          · exact (Term.sumF_either _ _ _ _).trans
              (Term.either_congr (Term.comp_nilconst_of r₁ hS₁) hS₂)
      | some A₂ =>
          refine Or.inr ⟨some (E₁ ⊕' A₂), N₂, Term.sumAssocR E₁ A₂ N₂ ⨟ Term.sumF r₁ r₂,
            ProvableIso.comp (ProvableIso.sumAssocR _ _ _) (ProvableIso.sumF hr₁ hr₂),
            ?_, hN₂, F₂, F₂', hK₂, ?_, ?_⟩
          · simp only [optListDepthLe, Ty.listDepth] at hE₂ ⊢
            exact max_le hd₁ hE₂
          · calc ((Term.sumAssocR E₁ A₂ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either T₁ T₂)
                ≡ₜ (Term.sumAssocR E₁ A₂ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either T₁ T₂)) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ (Term.sumAssocR E₁ A₂ N₂ ⨟
                    Term.either (nilconst B E₁) (Term.either (nilconst B A₂) F₂)) :=
                  PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                    (Term.either_congr (Term.comp_nilconst_of r₁ hT₁) hT₂))
              _ ≡ₜ Term.either (Term.either (nilconst B E₁) (nilconst B A₂)) F₂ :=
                  Term.sumAssocR_either _ _ _
              _ ≡ₜ Term.either (nilconst B (E₁ ⊕' A₂)) F₂ :=
                  Term.either_congr (Term.either_nilconst E₁ A₂ B) (PEq.refl _)
          · calc ((Term.sumAssocR E₁ A₂ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either S₁ S₂)
                ≡ₜ (Term.sumAssocR E₁ A₂ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either S₁ S₂)) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ (Term.sumAssocR E₁ A₂ N₂ ⨟
                    Term.either (nilconst B E₁) (Term.either (nilconst B A₂) F₂')) :=
                  PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                    (Term.either_congr (Term.comp_nilconst_of r₁ hS₁) hS₂))
              _ ≡ₜ Term.either (Term.either (nilconst B E₁) (nilconst B A₂)) F₂' :=
                  Term.sumAssocR_either _ _ _
              _ ≡ₜ Term.either (nilconst B (E₁ ⊕' A₂)) F₂' :=
                  Term.either_congr (Term.either_nilconst E₁ A₂ B) (PEq.refl _)
  · rcases h₂ with ⟨E₂, r₂, hr₂, hd₂, hT₂, hS₂⟩ |
      ⟨E₂, N₂, r₂, hr₂, hE₂, hN₂, F₂, F₂', hK₂, hT₂, hS₂⟩
    · -- the second case is empty, the first one splits
      cases E₁ with
      | none =>
          refine Or.inr ⟨some E₂, N₁, Term.comm E₂ N₁ ⨟ Term.sumF r₁ r₂,
            ProvableIso.comp (ProvableIso.comm _ _) (ProvableIso.sumF hr₁ hr₂),
            hd₂, hN₁, F₁, F₁', hK₁, ?_, ?_⟩
          · calc ((Term.comm E₂ N₁ ⨟ Term.sumF r₁ r₂) ⨟ Term.either T₁ T₂)
                ≡ₜ (Term.comm E₂ N₁ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either T₁ T₂)) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ (Term.comm E₂ N₁ ⨟ Term.either F₁ (nilconst B E₂)) :=
                  PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                    (Term.either_congr hT₁ (Term.comp_nilconst_of r₂ hT₂)))
              _ ≡ₜ Term.either (nilconst B E₂) F₁ := Term.comm_either _ _
          · calc ((Term.comm E₂ N₁ ⨟ Term.sumF r₁ r₂) ⨟ Term.either S₁ S₂)
                ≡ₜ (Term.comm E₂ N₁ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either S₁ S₂)) :=
                  PEq.comp_assoc _ _ _
              _ ≡ₜ (Term.comm E₂ N₁ ⨟ Term.either F₁' (nilconst B E₂)) :=
                  PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                    (Term.either_congr hS₁ (Term.comp_nilconst_of r₂ hS₂)))
              _ ≡ₜ Term.either (nilconst B E₂) F₁' := Term.comm_either _ _
      | some A₁ =>
          refine Or.inr ⟨some (A₁ ⊕' E₂), N₁,
            Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
              (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂)),
            ProvableIso.comp (ProvableIso.sumAssocR _ _ _)
              (ProvableIso.comp (ProvableIso.sumF (ProvableIso.id _) (ProvableIso.comm _ _))
                (ProvableIso.comp (ProvableIso.sumAssocL _ _ _)
                  (ProvableIso.sumF hr₁ hr₂))),
            ?_, hN₁, F₁, F₁', hK₁, ?_, ?_⟩
          · simp only [optListDepthLe, Ty.listDepth] at hE₁ ⊢
            exact max_le hE₁ hd₂
          · have hstep : ∀ (U₁ : Term X₁ B⋆) (U₂ : Term X₂ B⋆) (G : Term N₁ B⋆),
                (r₁ ⨟ U₁) ≡ₜ Term.either (nilconst B A₁) G → U₂ ≡ₜ nilconst B X₂ →
                (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                  (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂))) ⨟ Term.either U₁ U₂ ≡ₜ
                  Term.either (nilconst B (A₁ ⊕' E₂)) G := by
              intro U₁ U₂ G hU₁ hU₂
              have e0 : (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂) ≡ₜ
                  Term.either (Term.either (nilconst B A₁) G) (nilconst B E₂) :=
                (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr hU₁ (Term.comp_nilconst_of r₂ hU₂))
              have e1 : (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂)) ≡ₜ
                  Term.either (nilconst B A₁) (Term.either G (nilconst B E₂)) :=
                (PEq.compR _ e0).trans (Term.sumAssocL_either _ _ _)
              have e2 : (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                  (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂))) ≡ₜ
                  Term.either (nilconst B A₁) (Term.either (nilconst B E₂) G) := by
                refine (PEq.compR _ e1).trans ?_
                refine (Term.sumF_either _ _ _ _).trans ?_
                exact Term.either_congr (PEq.id_comp _) (Term.comm_either _ _)
              calc ((Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                    (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂))) ⨟ Term.either U₁ U₂)
                  ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ ((Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂)) ⨟ Term.either U₁ U₂)) :=
                    PEq.comp_assoc _ _ _
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      ((Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either U₁ U₂))) :=
                    PEq.compR _ (PEq.comp_assoc _ _ _)
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂)))) :=
                    PEq.compR _ (PEq.compR _ (PEq.comp_assoc _ _ _))
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟
                      Term.either (nilconst B A₁) (Term.either (nilconst B E₂) G)) :=
                    PEq.compR _ e2
                _ ≡ₜ Term.either (Term.either (nilconst B A₁) (nilconst B E₂)) G :=
                    Term.sumAssocR_either _ _ _
                _ ≡ₜ Term.either (nilconst B (A₁ ⊕' E₂)) G :=
                    Term.either_congr (Term.either_nilconst A₁ E₂ B) (PEq.refl _)
            exact hstep T₁ T₂ F₁ hT₁ hT₂
          · have hstep : ∀ (U₁ : Term X₁ B⋆) (U₂ : Term X₂ B⋆) (G : Term N₁ B⋆),
                (r₁ ⨟ U₁) ≡ₜ Term.either (nilconst B A₁) G → U₂ ≡ₜ nilconst B X₂ →
                (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                  (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂))) ⨟ Term.either U₁ U₂ ≡ₜ
                  Term.either (nilconst B (A₁ ⊕' E₂)) G := by
              intro U₁ U₂ G hU₁ hU₂
              have e0 : (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂) ≡ₜ
                  Term.either (Term.either (nilconst B A₁) G) (nilconst B E₂) :=
                (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr hU₁ (Term.comp_nilconst_of r₂ hU₂))
              have e1 : (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂)) ≡ₜ
                  Term.either (nilconst B A₁) (Term.either G (nilconst B E₂)) :=
                (PEq.compR _ e0).trans (Term.sumAssocL_either _ _ _)
              have e2 : (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                  (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂))) ≡ₜ
                  Term.either (nilconst B A₁) (Term.either (nilconst B E₂) G) := by
                refine (PEq.compR _ e1).trans ?_
                refine (Term.sumF_either _ _ _ _).trans ?_
                exact Term.either_congr (PEq.id_comp _) (Term.comm_either _ _)
              calc ((Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                    (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂))) ⨟ Term.either U₁ U₂)
                  ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ ((Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      (Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂)) ⨟ Term.either U₁ U₂)) :=
                    PEq.comp_assoc _ _ _
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      ((Term.sumAssocL A₁ N₁ E₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either U₁ U₂))) :=
                    PEq.compR _ (PEq.comp_assoc _ _ _)
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟ (Term.sumF (Term.id A₁) (Term.comm E₂ N₁) ⨟
                      (Term.sumAssocL A₁ N₁ E₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either U₁ U₂)))) :=
                    PEq.compR _ (PEq.compR _ (PEq.comp_assoc _ _ _))
                _ ≡ₜ (Term.sumAssocR A₁ E₂ N₁ ⨟
                      Term.either (nilconst B A₁) (Term.either (nilconst B E₂) G)) :=
                    PEq.compR _ e2
                _ ≡ₜ Term.either (Term.either (nilconst B A₁) (nilconst B E₂)) G :=
                    Term.sumAssocR_either _ _ _
                _ ≡ₜ Term.either (nilconst B (A₁ ⊕' E₂)) G :=
                    Term.either_congr (Term.either_nilconst A₁ E₂ B) (PEq.refl _)
            exact hstep S₁ S₂ F₁' hS₁ hS₂
    · -- both cases split
      cases E₁ with
      | none =>
          cases E₂ with
          | none =>
              refine Or.inr ⟨none, N₁ ⊕' N₂, Term.sumF r₁ r₂, ProvableIso.sumF hr₁ hr₂,
                trivial, ?_, Term.either F₁ F₂, Term.either F₁' F₂',
                KCopair2.node hK₁ hK₂, ?_, ?_⟩
              · simp only [Ty.listDepth]; exact max_le hN₁ hN₂
              · exact (Term.sumF_either _ _ _ _).trans (Term.either_congr hT₁ hT₂)
              · exact (Term.sumF_either _ _ _ _).trans (Term.either_congr hS₁ hS₂)
          | some A₂ =>
              refine Or.inr ⟨some A₂, N₁ ⊕' N₂, Term.sumRot A₂ N₁ N₂ ⨟ Term.sumF r₁ r₂,
                ProvableIso.comp (ProvableIso.sumRot _ _ _) (ProvableIso.sumF hr₁ hr₂),
                hE₂, ?_, Term.either F₁ F₂, Term.either F₁' F₂',
                KCopair2.node hK₁ hK₂, ?_, ?_⟩
              · simp only [Ty.listDepth]; exact max_le hN₁ hN₂
              · calc ((Term.sumRot A₂ N₁ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either T₁ T₂)
                    ≡ₜ (Term.sumRot A₂ N₁ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either T₁ T₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumRot A₂ N₁ N₂ ⨟
                        Term.either F₁ (Term.either (nilconst B A₂) F₂)) :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hT₁ hT₂))
                  _ ≡ₜ Term.either (nilconst B A₂) (Term.either F₁ F₂) :=
                      Term.sumRot_either _ _ _
              · calc ((Term.sumRot A₂ N₁ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either S₁ S₂)
                    ≡ₜ (Term.sumRot A₂ N₁ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either S₁ S₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumRot A₂ N₁ N₂ ⨟
                        Term.either F₁' (Term.either (nilconst B A₂) F₂')) :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hS₁ hS₂))
                  _ ≡ₜ Term.either (nilconst B A₂) (Term.either F₁' F₂') :=
                      Term.sumRot_either _ _ _
      | some A₁ =>
          cases E₂ with
          | none =>
              refine Or.inr ⟨some A₁, N₁ ⊕' N₂, Term.sumAssocL A₁ N₁ N₂ ⨟ Term.sumF r₁ r₂,
                ProvableIso.comp (ProvableIso.sumAssocL _ _ _) (ProvableIso.sumF hr₁ hr₂),
                hE₁, ?_, Term.either F₁ F₂, Term.either F₁' F₂',
                KCopair2.node hK₁ hK₂, ?_, ?_⟩
              · simp only [Ty.listDepth]; exact max_le hN₁ hN₂
              · calc ((Term.sumAssocL A₁ N₁ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either T₁ T₂)
                    ≡ₜ (Term.sumAssocL A₁ N₁ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either T₁ T₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumAssocL A₁ N₁ N₂ ⨟
                        Term.either (Term.either (nilconst B A₁) F₁) F₂) :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hT₁ hT₂))
                  _ ≡ₜ Term.either (nilconst B A₁) (Term.either F₁ F₂) :=
                      Term.sumAssocL_either _ _ _
              · calc ((Term.sumAssocL A₁ N₁ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either S₁ S₂)
                    ≡ₜ (Term.sumAssocL A₁ N₁ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either S₁ S₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumAssocL A₁ N₁ N₂ ⨟
                        Term.either (Term.either (nilconst B A₁) F₁') F₂') :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hS₁ hS₂))
                  _ ≡ₜ Term.either (nilconst B A₁) (Term.either F₁' F₂') :=
                      Term.sumAssocL_either _ _ _
          | some A₂ =>
              refine Or.inr ⟨some (A₁ ⊕' A₂), N₁ ⊕' N₂,
                Term.sumShuffle A₁ N₁ A₂ N₂ ⨟ Term.sumF r₁ r₂,
                ProvableIso.comp (ProvableIso.sumShuffle _ _ _ _) (ProvableIso.sumF hr₁ hr₂),
                ?_, ?_, Term.either F₁ F₂, Term.either F₁' F₂',
                KCopair2.node hK₁ hK₂, ?_, ?_⟩
              · simp only [optListDepthLe, Ty.listDepth] at hE₁ hE₂ ⊢
                exact max_le hE₁ hE₂
              · simp only [Ty.listDepth]; exact max_le hN₁ hN₂
              · calc ((Term.sumShuffle A₁ N₁ A₂ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either T₁ T₂)
                    ≡ₜ (Term.sumShuffle A₁ N₁ A₂ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either T₁ T₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumShuffle A₁ N₁ A₂ N₂ ⨟
                        Term.either (Term.either (nilconst B A₁) F₁)
                          (Term.either (nilconst B A₂) F₂)) :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hT₁ hT₂))
                  _ ≡ₜ Term.either (Term.either (nilconst B A₁) (nilconst B A₂))
                        (Term.either F₁ F₂) := Term.sumShuffle_either _ _ _ _
                  _ ≡ₜ Term.either (nilconst B (A₁ ⊕' A₂)) (Term.either F₁ F₂) :=
                      Term.either_congr (Term.either_nilconst A₁ A₂ B) (PEq.refl _)
              · calc ((Term.sumShuffle A₁ N₁ A₂ N₂ ⨟ Term.sumF r₁ r₂) ⨟ Term.either S₁ S₂)
                    ≡ₜ (Term.sumShuffle A₁ N₁ A₂ N₂ ⨟ (Term.sumF r₁ r₂ ⨟ Term.either S₁ S₂)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumShuffle A₁ N₁ A₂ N₂ ⨟
                        Term.either (Term.either (nilconst B A₁) F₁')
                          (Term.either (nilconst B A₂) F₂')) :=
                      PEq.compR _ ((Term.sumF_either _ _ _ _).trans
                        (Term.either_congr hS₁ hS₂))
                  _ ≡ₜ Term.either (Term.either (nilconst B A₁) (nilconst B A₂))
                        (Term.either F₁' F₂') := Term.sumShuffle_either _ _ _ _
                  _ ≡ₜ Term.either (nilconst B (A₁ ⊕' A₂)) (Term.either F₁' F₂') :=
                      Term.either_congr (Term.either_nilconst A₁ A₂ B) (PEq.refl _)

end SplitCopair

/-- **Separating the empty summands of a joint decomposition.**  A joint decomposition into
equationally `k`-guarded components which produce outputs of the same length splits into an
empty part and a matching pair of co-pairings of `k`-guarded terms with nonempty outputs. -/
theorem JointCasesD.toSplitCopair {B : Ty} {k : ℕ} (hk : 0 < k) {d : ℕ} :
    {X : Ty} → {T S : Term X B⋆} →
    JointCasesD B (fun {Y} (T S : Term Y B⋆) => KGuardedPair k B T S ∧
        ∀ x : ⟦Y⟧, (T.den x).length = (S.den x).length) d T S →
    SplitCopair k B d T S := by
  intro X T S h
  induction h with
  | @leaf X T S hX hP =>
      obtain ⟨⟨hT, hS⟩, hlen⟩ := hP
      obtain ⟨T', hTT', hKT'⟩ := hT.toKGuarded
      obtain ⟨S', hSS', hKS'⟩ := hS.toKGuarded
      have hdT : T.den = T'.den := PEq.sound hTT'
      have hdS : S.den = S'.den := PEq.sound hSS'
      have hlen' : ∀ x : ⟦X⟧, (T'.den x).length = (S'.den x).length := by
        intro x
        rw [← congrFun hdT x, ← congrFun hdS x]
        exact hlen x
      rcases kguarded_dichotomy hk hKT' with hne | ⟨hnil, hz⟩
      · refine Or.inr ⟨none, X, Term.id X, ProvableIso.id X, trivial, hX, T', S',
          KCopair2.leaf hKT' hKS' hne (nonempty_transfer hlen' hne), ?_, ?_⟩
        · exact (PEq.id_comp _).trans hTT'
        · exact (PEq.id_comp _).trans hSS'
      · have hzS : ∀ x : ⟦X⟧, S'.den x = [] := empty_transfer hlen' hz
        have hnilS : S' ≡ₜ nilconst B X := by
          rcases kguarded_dichotomy hk hKS' with hne | ⟨hS', -⟩
          · exact absurd (hzS (Ty.someElem X)) (hne _)
          · exact hS'
        exact Or.inl ⟨X, Term.id X, ProvableIso.id X, hX, hTT'.trans hnil, hSS'.trans hnilS⟩
  | node _ _ ih₁ ih₂ => exact SplitCopair.node ih₁ ih₂
  | precomp hq _ ih => exact SplitCopair.precomp hq ih
  | congr h₁ h₂ _ ih => exact SplitCopair.congr h₁ h₂ ih

end Lax149335Proofs

bridge_export Lax149335Proofs
