import Lax149335Proofs.Appendix.Drops.ShiftPairContent
import Lax149335Proofs.Appendix.Drops.SumShuffleLifts

/-!
# Empty and non-empty contents

The list node of the shift exchange lemma is proved by an induction in which the *empty*
components of the conclusion have to be kept apart from the non-empty ones: a list whose
elements all have a non-empty content can be handled by `shift` and `split` alone, whereas an
empty component has to be removed first.

This file introduces the three classes of contents that the induction distinguishes:

* `Lax149335Proofs.EC` — the contents provably equal to the constant empty word;
* `Lax149335Proofs.NEC` — the co-pairings, up to a lift, of contents of the shape
  `(snd ; x ; S-letter) ⊙ v` with `v` a tail content: every component starts with a letter of
  `S` and ends with a letter of `T`;
* `Lax149335Proofs.SC1` — a co-pairing, up to a lift, of an empty content and a non-empty one.

`Lax149335Proofs.QC` is the union of the last two, and `Lax149335Proofs.RC` the union of the three.  The
main result of the file is that every content of a shape of the conclusion is `RC`
(`Lax149335Proofs.IsShiftExchangeShape.rc`): the empty components of a shape can all be merged into
a single one, which is what the co-product shuffles of
`Lax149335Proofs.Appendix.Drops.SumShuffleLifts` are used for.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty} {r : ℕ}

/-! ### Non-empty contents -/

/-- `NEC S T r c` says that the content `c` is a co-pairing, up to a lift, of contents of the
shape `(snd ; x ; S-letter) ⊙ v` with `v` a tail content: each component is a word
`S T S T … S T`, starting with a letter of `S` and ending with a letter of `T`. -/
inductive NEC (S T : Ty) (r : ℕ) : {A : Ty} → Term A ((S ⊕' T)⋆) → Prop
  /-- A letter of `S` followed by a tail content. -/
  | head {W X E : Ty} {x : Term X S} {v : Term E ((S ⊕' T)⋆)} :
      IsDrop x → rank x ≤ r → TC S T r v →
      NEC S T r (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙ v)
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)} :
      NEC S T r c₁ → NEC S T r c₂ → NEC S T r (Term.either c₁ c₂)
  /-- Replacing a content by a provably equal one. -/
  | congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} : c ≡ₜ c' → NEC S T r c' → NEC S T r c
  /-- Pre-composing with a lift. -/
  | lift {A A' : Ty} {rho : Term A A'} {c : Term A' ((S ⊕' T)⋆)} :
      IsLift rho → NEC S T r c → NEC S T r (rho ⨟ c)

/-- A letter of `S` followed by a tail content is a content of the shape of the
conclusion. -/
theorem SC.of_head {W X E : Ty} {x : Term X S} {v : Term E ((S ⊕' T)⋆)} (hx : IsDrop x)
    (hrx : rank x ≤ r) (hv : TC S T r v) :
    SC S T r (((Term.snd W X ⨟ x) ⨟ sLetter S T) ⊙ v) := by
  induction hv with
  | @base M Y V m y hm hy hry => exact SC.inner_junk hx hrx hy hry hm
  | either _ _ ih₁ ih₂ =>
      exact SC.congr (fdot_either_distR _ _ _)
        (SC.lift_comp (IsLift.distR _ _ _) (SC.either ih₁ ih₂))
  | congr h _ ih => exact SC.congr (fdot_congr (PEq.refl _) h) ih
  | @lift A A' rho c hrho _ ih =>
      refine SC.congr ?_ (SC.lift_comp (IsLift.prodF (IsLift.id (W ⊗ X)) hrho) ih)
      exact PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.id_comp _) (PEq.refl _)))

namespace NEC

theorem of_liftEq {A A' : Ty} {c : Term A ((S ⊕' T)⋆)} {c' : Term A' ((S ⊕' T)⋆)}
    (h : LiftEq c c') (hc : NEC S T r c') : NEC S T r c :=
  let ⟨_, hr, he⟩ := h
  NEC.congr he (NEC.lift hr hc)

/-- A non-empty content is a content of the shape of the conclusion. -/
theorem sc {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : NEC S T r c) : SC S T r c := by
  induction h with
  | head hx hrx hv => exact SC.of_head hx hrx hv
  | either _ _ ih₁ ih₂ => exact SC.either ih₁ ih₂
  | congr h _ ih => exact SC.congr h ih
  | lift hrho _ ih => exact SC.lift_comp hrho ih

/-- Erasing, on the left, a factor that carries no letter. -/
theorem snd_comp {A : Ty} (W : Ty) {c : Term A ((S ⊕' T)⋆)} (h : NEC S T r c) :
    NEC S T r (Term.snd W A ⨟ c) := by
  induction h with
  | @head W' X E x v hx hrx hv =>
      have hju : (Term.snd W (W' ⊗ X) ⨟ ((Term.snd W' X ⨟ x) ⨟ sLetter S T)) ≡ₜ
          (assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) := by
        calc (Term.snd W (W' ⊗ X) ⨟ ((Term.snd W' X ⨟ x) ⨟ sLetter S T))
            ≡ₜ ((Term.snd W (W' ⊗ X) ⨟ (Term.snd W' X ⨟ x)) ⨟ sLetter S T) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (((Term.snd W (W' ⊗ X) ⨟ Term.snd W' X) ⨟ x) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (((assocL W W' X ⨟ Term.snd (W ⊗ W') X) ⨟ x) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.compL _ (snd_snd_assocL W W' X))
          _ ≡ₜ ((assocL W W' X ⨟ (Term.snd (W ⊗ W') X ⨟ x)) ⨟ sLetter S T) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ (assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) :=
              PEq.comp_assoc _ _ _
      refine NEC.congr ?_ (NEC.lift
        (IsLift.comp (IsLift.assocL W (W' ⊗ X) E)
          (IsLift.prodF (IsLift.assocL W W' X) (IsLift.id E)))
        (NEC.head (W := W ⊗ W') hx hrx hv))
      calc (Term.snd W ((W' ⊗ X) ⊗ E) ⨟ (((Term.snd W' X ⨟ x) ⨟ sLetter S T) ⊙ v))
          ≡ₜ (assocL W (W' ⊗ X) E ⨟
              ((Term.snd W (W' ⊗ X) ⨟ ((Term.snd W' X ⨟ x) ⨟ sLetter S T)) ⊙ v)) :=
            snd_fdot _ _
        _ ≡ₜ (assocL W (W' ⊗ X) E ⨟
              ((assocL W W' X ⨟ ((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T)) ⊙ v)) :=
            PEq.compR _ (fdot_congr hju (PEq.refl _))
        _ ≡ₜ (assocL W (W' ⊗ X) E ⨟ (prodF (assocL W W' X) (Term.id E) ⨟
              (((Term.snd (W ⊗ W') X ⨟ x) ⨟ sLetter S T) ⊙ v))) :=
            PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
              (fdot_congr (PEq.refl _) (PEq.id_comp _))))
        _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  | either _ _ ih₁ ih₂ =>
      exact NEC.congr (snd_either _ _) (NEC.lift (IsLift.distR W _ _) (NEC.either ih₁ ih₂))
  | congr h _ ih => exact NEC.congr (PEq.compR _ h) ih
  | @lift A A' rho c hrho _ ih =>
      refine NEC.congr ?_ (NEC.lift (IsLift.prodF (IsLift.id W) hrho) ih)
      calc (Term.snd W A ⨟ (rho ⨟ c))
          ≡ₜ ((Term.snd W A ⨟ rho) ⨟ c) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((prodF (Term.id W) rho ⨟ Term.snd W A') ⨟ c) :=
            PEq.compL _ (PEq.symm (PEq.nat_snd _ _))
        _ ≡ₜ (prodF (Term.id W) rho ⨟ (Term.snd W A' ⨟ c)) := PEq.comp_assoc _ _ _

/-- Erasing, on the right, a factor that carries no letter. -/
theorem fst_comp {A : Ty} (V : Ty) {c : Term A ((S ⊕' T)⋆)} (h : NEC S T r c) :
    NEC S T r (Term.fst A V ⨟ c) := by
  induction h with
  | @head W X E x v hx hrx hv =>
      exact NEC.congr (fst_fdot _ _)
        (NEC.lift (IsLift.assocR (W ⊗ X) E V) (NEC.head hx hrx (TC.fst_comp V hv)))
  | either _ _ ih₁ ih₂ =>
      exact NEC.congr (fst_either _ _) (NEC.lift (IsLift.distL _ _ V) (NEC.either ih₁ ih₂))
  | congr h _ ih => exact NEC.congr (PEq.compR _ h) ih
  | @lift A A' rho c hrho _ ih =>
      refine NEC.congr ?_ (NEC.lift (IsLift.prodF hrho (IsLift.id V)) ih)
      calc (Term.fst A V ⨟ (rho ⨟ c))
          ≡ₜ ((Term.fst A V ⨟ rho) ⨟ c) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((prodF rho (Term.id V) ⨟ Term.fst A' V) ⨟ c) :=
            PEq.compL _ (PEq.symm (PEq.nat_fst _ _))
        _ ≡ₜ (prodF rho (Term.id V) ⨟ (Term.fst A' V ⨟ c)) := PEq.comp_assoc _ _ _

/-- Non-empty contents are closed under concatenation. -/
theorem fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : NEC S T r c₁) (h₂ : NEC S T r c₂) : NEC S T r (c₁ ⊙ c₂) := by
  induction h₁ with
  | @head W X E x v hx hrx hv =>
      exact NEC.of_liftEq (LiftEq.assoc _ _ _)
        (NEC.head hx hrx (TC.fdot_sc hv (NEC.sc h₂)))
  | either _ _ ih₁ ih₂ =>
      exact NEC.congr (fdot_either_distL _ _ _)
        (NEC.lift (IsLift.distL _ _ _) (NEC.either ih₁ ih₂))
  | congr h _ ih => exact NEC.congr (fdot_congr h (PEq.refl _)) ih
  | @lift A A' rho c hrho _ ih =>
      refine NEC.congr ?_ (NEC.lift (IsLift.prodF hrho (IsLift.id A₂)) ih)
      exact PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.refl _) (PEq.id_comp _)))

end NEC

/-! ### Empty contents -/

/-- `EC S T c` says that the content `c` is provably the constant empty word. -/
def EC (S T : Ty) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  c ≡ₜ (Term.toUnit A ⨟ nilT (S ⊕' T))

namespace EC

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : EC S T c') : EC S T c :=
  h.trans hc

/-- Empty contents are closed under co-pairing. -/
theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : EC S T c₁) (h₂ : EC S T c₂) : EC S T (Term.either c₁ c₂) := by
  calc Term.either c₁ c₂
      ≡ₜ Term.either (Term.toUnit A₁ ⨟ nilT (S ⊕' T)) (Term.toUnit A₂ ⨟ nilT (S ⊕' T)) :=
        Term.either_congr h₁ h₂
    _ ≡ₜ (Term.either (Term.toUnit A₁) (Term.toUnit A₂) ⨟ nilT (S ⊕' T)) :=
        PEq.symm (Term.either_comp _ _ _)
    _ ≡ₜ (Term.toUnit (A₁ ⊕' A₂) ⨟ nilT (S ⊕' T)) := PEq.compL _ (PEq.unit_unique _ _)

/-- Empty contents are closed under concatenation. -/
theorem fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : EC S T c₁) (h₂ : EC S T c₂) : EC S T (c₁ ⊙ c₂) :=
  (fdot_congr h₁ h₂).trans (Term.nilconst_prodF_binconcat A₁ A₂ (S ⊕' T))

/-- Empty contents are closed under the homomorphism combinator. -/
theorem homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : EC S T c) : EC S T (Term.homT c) :=
  (homT_congr h).trans (Term.homT_nilconst A (S ⊕' T))

/-- An empty content is a content of the shape of the conclusion. -/
theorem sc {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : EC S T c) : SC S T r c :=
  SC.congr h (SC.empty S T r A)

/-- An empty content in front of a non-empty one may be erased. -/
theorem fdot_nec {A₁ A₂ : Ty} {e : Term A₁ ((S ⊕' T)⋆)} {n : Term A₂ ((S ⊕' T)⋆)}
    (he : EC S T e) (hn : NEC S T r n) : NEC S T r (e ⊙ n) :=
  NEC.congr ((fdot_congr he (PEq.refl n)).trans (Term.prodF_nilconst_binconcat_left n))
    (NEC.snd_comp A₁ hn)

end EC

/-- A non-empty content followed by an empty one: the empty one may be erased. -/
theorem NEC.fdot_ec {A₁ A₂ : Ty} {n : Term A₁ ((S ⊕' T)⋆)} {e : Term A₂ ((S ⊕' T)⋆)}
    (hn : NEC S T r n) (he : EC S T e) : NEC S T r (n ⊙ e) :=
  NEC.congr ((fdot_congr (PEq.refl n) he).trans (Term.prodF_nilconst_binconcat n))
    (NEC.fst_comp A₂ hn)

/-! ### Contents with at most one empty component -/

/-- `SC1 S T r c` says that the content `c` is, up to a lift, a co-pairing of an empty
content and a non-empty one.  This is the shape that the homomorphism combinator produces:
the empty component is the empty list. -/
def SC1 (S T : Ty) (r : ℕ) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (A₁ E : Ty) (rho : Term A (A₁ ⊕' E)) (e : Term A₁ ((S ⊕' T)⋆)) (n : Term E ((S ⊕' T)⋆)),
    IsLift rho ∧ EC S T e ∧ NEC S T r n ∧ c ≡ₜ (rho ⨟ Term.either e n)

namespace SC1

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : SC1 S T r c') :
    SC1 S T r c :=
  let ⟨A₁, E, rho, e, n, hrho, he, hn, hc⟩ := hc
  ⟨A₁, E, rho, e, n, hrho, he, hn, h.trans hc⟩

theorem lift_comp {A A' : Ty} {beta : Term A' A} (hb : IsLift beta) {c : Term A ((S ⊕' T)⋆)}
    (hc : SC1 S T r c) : SC1 S T r (beta ⨟ c) :=
  let ⟨A₁, E, rho, e, n, hrho, he, hn, hcc⟩ := hc
  ⟨A₁, E, beta ⨟ rho, e, n, IsLift.comp hb hrho, he, hn,
    (PEq.compR _ hcc).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem of_liftEq {A A' : Ty} {c : Term A ((S ⊕' T)⋆)} {c' : Term A' ((S ⊕' T)⋆)}
    (h : LiftEq c c') (hc : SC1 S T r c') : SC1 S T r c :=
  let ⟨_, hr, he⟩ := h
  SC1.congr he (SC1.lift_comp hr hc)

/-- The basic shape: a co-pairing of an empty content and a non-empty one. -/
theorem of_either {A₁ E : Ty} {e : Term A₁ ((S ⊕' T)⋆)} {n : Term E ((S ⊕' T)⋆)}
    (he : EC S T e) (hn : NEC S T r n) : SC1 S T r (Term.either e n) :=
  ⟨A₁, E, Term.id (A₁ ⊕' E), e, n, IsLift.id _, he, hn, PEq.symm (PEq.id_comp _)⟩

/-- A content with at most one empty component is a content of the shape of the
conclusion. -/
theorem sc {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SC1 S T r c) : SC S T r c :=
  let ⟨_, _, _, _, _, hrho, he, hn, hc⟩ := h
  SC.congr hc (SC.lift_comp hrho (SC.either (EC.sc he) (NEC.sc hn)))

end SC1

/-- `QC S T r c` says that the content `c` is non-empty, or a co-pairing of an empty content
and a non-empty one.  This is the class that the list node maintains. -/
def QC (S T : Ty) (r : ℕ) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  NEC S T r c ∨ SC1 S T r c

namespace QC

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : QC S T r c') :
    QC S T r c :=
  hc.imp (NEC.congr h) (SC1.congr h)

theorem sc {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : QC S T r c) : SC S T r c :=
  h.elim NEC.sc SC1.sc

end QC

/-- A non-empty content in front of a content with at most one empty component is
non-empty. -/
theorem NEC.fdot_sc1 {A₁ A₂ : Ty} {n : Term A₁ ((S ⊕' T)⋆)} {c : Term A₂ ((S ⊕' T)⋆)}
    (hn : NEC S T r n) (hc : SC1 S T r c) : NEC S T r (n ⊙ c) := by
  obtain ⟨B₁, E, rho, e, n', hrho, he, hn', hcc⟩ := hc
  refine NEC.of_liftEq (LiftEq.fdot (LiftEq.refl n) ⟨rho, hrho, hcc⟩) ?_
  exact NEC.congr (fdot_either_distR _ _ _)
    (NEC.lift (IsLift.distR _ _ _) (NEC.either (hn.fdot_ec he) (hn.fdot hn')))

/-- A content with at most one empty component in front of a non-empty one is non-empty. -/
theorem SC1.fdot_nec {A₁ A₂ : Ty} {c : Term A₁ ((S ⊕' T)⋆)} {n : Term A₂ ((S ⊕' T)⋆)}
    (hc : SC1 S T r c) (hn : NEC S T r n) : NEC S T r (c ⊙ n) := by
  obtain ⟨B₁, E, rho, e, n', hrho, he, hn', hcc⟩ := hc
  refine NEC.of_liftEq (LiftEq.fdot ⟨rho, hrho, hcc⟩ (LiftEq.refl n)) ?_
  exact NEC.congr (fdot_either_distL _ _ _)
    (NEC.lift (IsLift.distL _ _ _) (NEC.either (he.fdot_nec hn) (hn'.fdot hn)))

/-- An empty content in front of a content with at most one empty component. -/
theorem EC.fdot_sc1 {A₁ A₂ : Ty} {e : Term A₁ ((S ⊕' T)⋆)} {c : Term A₂ ((S ⊕' T)⋆)}
    (he : EC S T e) (hc : SC1 S T r c) : SC1 S T r (e ⊙ c) := by
  obtain ⟨B₁, E, rho, e', n', hrho, he', hn', hcc⟩ := hc
  refine SC1.of_liftEq (LiftEq.fdot (LiftEq.refl e) ⟨rho, hrho, hcc⟩) ?_
  exact SC1.congr (fdot_either_distR _ _ _)
    (SC1.lift_comp (IsLift.distR _ _ _) (SC1.of_either (he.fdot he') (he.fdot_nec hn')))

/-- Contents with at most one empty component are closed under concatenation. -/
theorem SC1.fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SC1 S T r c₁) (h₂ : SC1 S T r c₂) : SC1 S T r (c₁ ⊙ c₂) := by
  obtain ⟨B₁, E₁, rho₁, e₁, n₁, hrho₁, he₁, hn₁, hcc₁⟩ := h₁
  refine SC1.of_liftEq (LiftEq.fdot ⟨rho₁, hrho₁, hcc₁⟩ (LiftEq.refl c₂)) ?_
  refine SC1.congr (fdot_either_distL _ _ _) (SC1.lift_comp (IsLift.distL _ _ _) ?_)
  have hleft : SC1 S T r (e₁ ⊙ c₂) := he₁.fdot_sc1 h₂
  have hright : NEC S T r (n₁ ⊙ c₂) := hn₁.fdot_sc1 h₂
  obtain ⟨B₂, E₂, rho₂, e₂, n₂, hrho₂, he₂, hn₂, hcc₂⟩ := hleft
  refine SC1.of_liftEq (LiftEq.either ⟨rho₂, hrho₂, hcc₂⟩ (LiftEq.refl (n₁ ⊙ c₂))) ?_
  exact ⟨B₂, E₂ ⊕' _, sumAssocR B₂ E₂ _, e₂, Term.either n₂ (n₁ ⊙ c₂),
    IsLift.sumAssocR _ _ _, he₂, NEC.either hn₂ hright,
    PEq.symm (Term.sumAssocR_either _ _ _)⟩

/-- The class maintained by the list node is closed under concatenation. -/
theorem QC.fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : QC S T r c₁) (h₂ : QC S T r c₂) : QC S T r (c₁ ⊙ c₂) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (h₁.fdot h₂)
  · exact Or.inl (h₁.fdot_sc1 h₂)
  · exact Or.inl (h₁.fdot_nec h₂)
  · exact Or.inr (h₁.fdot h₂)

/-! ### Normalising the empty components of a shape -/

/-- `RC S T r c` says that the content `c` is empty, non-empty, or a co-pairing of an empty
content and a non-empty one: the normal form of a content of a shape of the conclusion, in
which all the empty components have been merged into one. -/
def RC (S T : Ty) (r : ℕ) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  EC S T c ∨ QC S T r c

namespace RC

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : RC S T r c') :
    RC S T r c :=
  hc.imp (EC.congr h) (QC.congr h)

/-- The normal form is closed under co-pairing: two empty components merge into one. -/
theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : RC S T r c₁) (h₂ : RC S T r c₂) : RC S T r (Term.either c₁ c₂) := by
  rcases h₁ with he₁ | (hn₁ | hs₁) <;> rcases h₂ with he₂ | (hn₂ | hs₂)
  -- empty, empty
  · exact Or.inl (he₁.either he₂)
  -- empty, non-empty
  · exact Or.inr (Or.inr (SC1.of_either he₁ hn₂))
  -- empty, one empty component
  · obtain ⟨B₂, E₂, rho₂, e₂, n₂, hrho₂, he₂, hn₂, hcc₂⟩ := hs₂
    refine Or.inr (Or.inr (SC1.of_liftEq
      (LiftEq.either (LiftEq.refl c₁) ⟨rho₂, hrho₂, hcc₂⟩) ?_))
    exact ⟨A₁ ⊕' B₂, E₂, sumAssocL A₁ B₂ E₂, Term.either c₁ e₂, n₂,
      IsLift.sumAssocL _ _ _, he₁.either he₂, hn₂, PEq.symm (Term.sumAssocL_either _ _ _)⟩
  -- non-empty, empty
  · refine Or.inr (Or.inr ⟨A₂, A₁, Term.comm A₁ A₂, c₂, c₁, IsLift.comm _ _, he₂, hn₁, ?_⟩)
    exact PEq.symm (Term.comm_either _ _)
  -- non-empty, non-empty
  · exact Or.inr (Or.inl (hn₁.either hn₂))
  -- non-empty, one empty component
  · obtain ⟨B₂, E₂, rho₂, e₂, n₂, hrho₂, he₂, hn₂, hcc₂⟩ := hs₂
    refine Or.inr (Or.inr (SC1.of_liftEq
      (LiftEq.either (LiftEq.refl c₁) ⟨rho₂, hrho₂, hcc₂⟩) ?_))
    exact ⟨B₂, A₁ ⊕' E₂, sumSwapMid' A₁ B₂ E₂, e₂, Term.either c₁ n₂,
      Term.isLift_sumSwapMid' _ _ _, he₂, NEC.either hn₁ hn₂,
      PEq.symm (Term.sumSwapMid'_either _ _ _)⟩
  -- one empty component, empty
  · obtain ⟨B₁, E₁, rho₁, e₁, n₁, hrho₁, he₁, hn₁, hcc₁⟩ := hs₁
    refine Or.inr (Or.inr (SC1.of_liftEq
      (LiftEq.either ⟨rho₁, hrho₁, hcc₁⟩ (LiftEq.refl c₂)) ?_))
    exact ⟨B₁ ⊕' A₂, E₁, sumSwapMid B₁ E₁ A₂, Term.either e₁ c₂, n₁,
      Term.isLift_sumSwapMid _ _ _, he₁.either he₂, hn₁,
      PEq.symm (Term.sumSwapMid_either _ _ _)⟩
  -- one empty component, non-empty
  · obtain ⟨B₁, E₁, rho₁, e₁, n₁, hrho₁, he₁, hn₁, hcc₁⟩ := hs₁
    refine Or.inr (Or.inr (SC1.of_liftEq
      (LiftEq.either ⟨rho₁, hrho₁, hcc₁⟩ (LiftEq.refl c₂)) ?_))
    exact ⟨B₁, E₁ ⊕' A₂, sumAssocR B₁ E₁ A₂, e₁, Term.either n₁ c₂,
      IsLift.sumAssocR _ _ _, he₁, NEC.either hn₁ hn₂,
      PEq.symm (Term.sumAssocR_either _ _ _)⟩
  -- one empty component, one empty component
  · obtain ⟨B₁, E₁, rho₁, e₁, n₁, hrho₁, he₁, hn₁, hcc₁⟩ := hs₁
    obtain ⟨B₂, E₂, rho₂, e₂, n₂, hrho₂, he₂, hn₂, hcc₂⟩ := hs₂
    refine Or.inr (Or.inr (SC1.of_liftEq
      (LiftEq.either ⟨rho₁, hrho₁, hcc₁⟩ ⟨rho₂, hrho₂, hcc₂⟩) ?_))
    exact ⟨B₁ ⊕' B₂, E₁ ⊕' E₂, sumInter B₁ E₁ B₂ E₂, Term.either e₁ e₂,
      Term.either n₁ n₂, Term.isLift_sumInter _ _ _ _, he₁.either he₂,
      NEC.either hn₁ hn₂, PEq.symm (Term.sumInter_either _ _ _ _)⟩

end RC

/-- **The content of a shape is in normal form**: its empty components can all be merged into
a single one. -/
theorem IsShiftExchangeShape.rc : {D : Ty} → {g : Term D (shiftCod S T)} →
    IsShiftExchangeShape S T r g → RC S T r (g ⨟ shiftContent S T)
  | _, _, .empty A => Or.inl (content_empty S T A)
  | _, _, @IsShiftExchangeShape.inner _ _ _ W X M Y V x y m hx hrx hy hry hm =>
      Or.inr (Or.inl (NEC.congr (content_inner x m y)
        (NEC.head hx hrx (TC.base hm hy hry))))
  | _, _, .either h₁ h₂ =>
      RC.congr (Term.either_comp _ _ _) (RC.either h₁.rc h₂.rc)

end Lax149335Proofs

bridge_export Lax149335Proofs
