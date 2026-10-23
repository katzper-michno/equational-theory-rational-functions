import Lax149335Proofs.Appendix.Drops.ShiftShapeContent

/-!
# Pair contents and tail contents

The list node of the shift exchange lemma (`Lax149335Proofs.shiftExch_homT`) needs two auxiliary
classes of contents, both read in `(S + T)*`:

* `Lax149335Proofs.PC` — the contents that are, after a lift, the content of an inner normal form,
  i.e. words of alternating letters `T S T S … T S`;
* `Lax149335Proofs.TC` — the contents that are, after a lift, a co-pairing of contents of the shape
  `(m ; paircontent) ⊙ (fst ; y ; T-letter)`, i.e. words `T S … T S T` ending with a letter
  of `T`.  These are the *tails* of the non-empty components of the conclusion of the lemma:
  a component of the conclusion is a letter of `S` followed by a tail.

The two classes are closed under the operations that the induction performs: `PC` under
concatenation, co-pairing and `hom` (the last one because inner normal forms are closed under
`hom`), and `TC` under concatenation with a `PC` on the left, under co-pairing, and under
concatenation with an arbitrary content of the conclusion on the right.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty} {r : ℕ}

/-! ### Two more cases of equality up to a lift -/

/-- Equality up to a lift is compatible with the homomorphism combinator. -/
theorem LiftEq.homT {A A' D : Ty} {c : Term A D⋆} {c' : Term A' D⋆} (h : LiftEq c c') :
    LiftEq (Term.homT c) (Term.homT c') :=
  let ⟨rho, hr, he⟩ := h
  ⟨listF rho, IsLift.listF hr, (homT_congr he).trans (homT_precomp _ _)⟩

/-- Equality up to a lift is compatible with co-pairing. -/
theorem LiftEq.either {A₁ A₂ A₁' A₂' D : Ty} {c₁ : Term A₁ D⋆} {c₂ : Term A₂ D⋆}
    {c₁' : Term A₁' D⋆} {c₂' : Term A₂' D⋆} (h₁ : LiftEq c₁ c₁') (h₂ : LiftEq c₂ c₂') :
    LiftEq (Term.either c₁ c₂) (Term.either c₁' c₂') :=
  let ⟨rho₁, hr₁, he₁⟩ := h₁
  let ⟨rho₂, hr₂, he₂⟩ := h₂
  ⟨sumF rho₁ rho₂, IsLift.sumF hr₁ hr₂,
    (Term.either_congr he₁ he₂).trans (PEq.symm (Term.sumF_either _ _ _ _))⟩

/-! ### Pair contents -/

/-- `PC S T r c` says that the content `c` is, after a lift, the content of an inner normal
form: a word `T S T S … T S` of pairs. -/
def PC (S T : Ty) (r : ℕ) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (M : Ty) (alpha : Term A M) (m : Term M ((T ⊗ S)⋆)),
    IsLift alpha ∧ IsShiftInnerForm S T r m ∧ c ≡ₜ (alpha ⨟ (m ⨟ pairContentTS S T))

namespace PC

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : PC S T r c') :
    PC S T r c :=
  let ⟨M, alpha, m, ha, hm, he⟩ := hc
  ⟨M, alpha, m, ha, hm, h.trans he⟩

theorem lift_comp {A A' : Ty} {beta : Term A' A} (hb : IsLift beta) {c : Term A ((S ⊕' T)⋆)}
    (hc : PC S T r c) : PC S T r (beta ⨟ c) :=
  let ⟨M, alpha, m, ha, hm, he⟩ := hc
  ⟨M, beta ⨟ alpha, m, IsLift.comp hb ha, hm,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem of_liftEq {A A' : Ty} {c : Term A ((S ⊕' T)⋆)} {c' : Term A' ((S ⊕' T)⋆)}
    (h : LiftEq c c') (hc : PC S T r c') : PC S T r c :=
  let ⟨_, hr, he⟩ := h
  PC.congr he (PC.lift_comp hr hc)

/-- The content of an inner normal form is a pair content. -/
theorem of_innerForm {M : Ty} {m : Term M ((T ⊗ S)⋆)} (hm : IsShiftInnerForm S T r m) :
    PC S T r (m ⨟ pairContentTS S T) :=
  ⟨M, Term.id M, m, IsLift.id M, hm, PEq.symm (PEq.id_comp _)⟩

/-- Pair contents are closed under concatenation. -/
theorem fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : PC S T r c₁) (h₂ : PC S T r c₂) : PC S T r (c₁ ⊙ c₂) := by
  obtain ⟨M₁, a₁, m₁, ha₁, hm₁, he₁⟩ := h₁
  obtain ⟨M₂, a₂, m₂, ha₂, hm₂, he₂⟩ := h₂
  refine ⟨M₁ ⊗ M₂, prodF a₁ a₂, m₁ ⊙ m₂, IsLift.prodF ha₁ ha₂, hm₁.fdot hm₂, ?_⟩
  calc (c₁ ⊙ c₂)
      ≡ₜ ((a₁ ⨟ (m₁ ⨟ pairContentTS S T)) ⊙ (a₂ ⨟ (m₂ ⨟ pairContentTS S T))) :=
        fdot_congr he₁ he₂
    _ ≡ₜ (prodF a₁ a₂ ⨟ ((m₁ ⨟ pairContentTS S T) ⊙ (m₂ ⨟ pairContentTS S T))) :=
        PEq.symm (fdot_precomp _ _ _ _)
    _ ≡ₜ (prodF a₁ a₂ ⨟ ((m₁ ⊙ m₂) ⨟ pairContentTS S T)) :=
        PEq.compR _ (PEq.symm (fdot_comp_homT _ _ _))

/-- Pair contents are closed under co-pairing. -/
theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : PC S T r c₁) (h₂ : PC S T r c₂) : PC S T r (Term.either c₁ c₂) := by
  obtain ⟨M₁, a₁, m₁, ha₁, hm₁, he₁⟩ := h₁
  obtain ⟨M₂, a₂, m₂, ha₂, hm₂, he₂⟩ := h₂
  refine ⟨M₁ ⊕' M₂, sumF a₁ a₂, Term.either m₁ m₂, IsLift.sumF ha₁ ha₂, hm₁.either hm₂, ?_⟩
  calc Term.either c₁ c₂
      ≡ₜ Term.either (a₁ ⨟ (m₁ ⨟ pairContentTS S T)) (a₂ ⨟ (m₂ ⨟ pairContentTS S T)) :=
        Term.either_congr he₁ he₂
    _ ≡ₜ (sumF a₁ a₂ ⨟
          Term.either (m₁ ⨟ pairContentTS S T) (m₂ ⨟ pairContentTS S T)) :=
        PEq.symm (Term.sumF_either _ _ _ _)
    _ ≡ₜ (sumF a₁ a₂ ⨟ (Term.either m₁ m₂ ⨟ pairContentTS S T)) :=
        PEq.compR _ (PEq.symm (Term.either_comp _ _ _))

/-- Pair contents are closed under the homomorphism combinator: inner normal forms are. -/
theorem homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : PC S T r c) :
    PC S T r (Term.homT c) := by
  obtain ⟨M, alpha, m, ha, hm, he⟩ := h
  refine ⟨M⋆, listF alpha, Term.homT m, IsLift.listF ha, hm.homT, ?_⟩
  calc Term.homT c
      ≡ₜ Term.homT (alpha ⨟ (m ⨟ pairContentTS S T)) := homT_congr he
    _ ≡ₜ (listF alpha ⨟ Term.homT (m ⨟ pairContentTS S T)) := homT_precomp _ _
    _ ≡ₜ (listF alpha ⨟ (Term.homT m ⨟ pairContentTS S T)) :=
        PEq.compR _ (PEq.symm (homT_comp _ _))

/-- A letter of `T` followed by a letter of `S` is a pair content, whatever the factors that
are erased between them. -/
theorem pairJunk {Y V W X : Ty} {y : Term Y T} {x : Term X S} (hy : IsDrop y)
    (hry : rank y ≤ r) (hx : IsDrop x) (hrx : rank x ≤ r) :
    PC S T r (((Term.fst Y V ⨟ y) ⨟ tLetter S T) ⊙ ((Term.snd W X ⨟ x) ⨟ sLetter S T)) := by
  have hrk : rank (prodF y x) ≤ r := by
    have h : rank (prodF y x) = max (rank y) (rank x) := rfl
    omega
  have hleafc :
      (((prodF (Term.fst Y (V ⊗ W)) (Term.id X) ⨟ prodF y x) ⨟ pureT (T ⊗ S)) ⨟
          pairContentTS S T) ≡ₜ
        ((Term.fst Y (V ⊗ W) ⨟ (y ⨟ tLetter S T)) ⊙ (x ⨟ sLetter S T)) := by
    calc (((prodF (Term.fst Y (V ⊗ W)) (Term.id X) ⨟ prodF y x) ⨟ pureT (T ⊗ S)) ⨟
          Term.homT (tLetter S T ⊙ sLetter S T))
        ≡ₜ ((prodF (Term.fst Y (V ⊗ W)) (Term.id X) ⨟ prodF y x) ⨟
            (pureT (T ⊗ S) ⨟ Term.homT (tLetter S T ⊙ sLetter S T))) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((prodF (Term.fst Y (V ⊗ W)) (Term.id X) ⨟ prodF y x) ⨟
            (tLetter S T ⊙ sLetter S T)) := PEq.compR _ (homT_pure _)
      _ ≡ₜ (prodF (Term.fst Y (V ⊗ W) ⨟ y) (Term.id X ⨟ x) ⨟
            (tLetter S T ⊙ sLetter S T)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (((Term.fst Y (V ⊗ W) ⨟ y) ⨟ tLetter S T) ⊙ ((Term.id X ⨟ x) ⨟ sLetter S T)) :=
          fdot_precomp _ _ _ _
      _ ≡ₜ ((Term.fst Y (V ⊗ W) ⨟ (y ⨟ tLetter S T)) ⊙ (x ⨟ sLetter S T)) :=
          fdot_congr (PEq.comp_assoc _ _ _) (PEq.compL _ (PEq.id_comp _))
  have hPC : PC S T r ((Term.fst Y (V ⊗ W) ⨟ (y ⨟ tLetter S T)) ⊙ (x ⨟ sLetter S T)) :=
    ⟨_, Term.id _, _, IsLift.id _,
      IsShiftInnerForm.leaf (IsShiftInnerLeaf.sing (IsDrop.prodF hy hx) hrk),
      (PEq.symm hleafc).trans (PEq.symm (PEq.id_comp _))⟩
  exact PC.of_liftEq
    (LiftEq.congr_left (fdot_congr (PEq.comp_assoc _ _ _) (PEq.comp_assoc _ _ _))
      (liftEq_mergeJunk (y ⨟ tLetter S T) (x ⨟ sLetter S T))) hPC

end PC

/-! ### Tail contents -/

/-- `TC S T r c` says that the content `c` is a co-pairing, up to a lift, of contents of the
shape `(m ; paircontent) ⊙ (fst ; y ; T-letter)`: words `T S … T S T` that end with a letter
of `T`.  These are the tails of the non-empty components of the conclusion of the shift
exchange lemma. -/
inductive TC (S T : Ty) (r : ℕ) : {A : Ty} → Term A ((S ⊕' T)⋆) → Prop
  /-- An inner normal form followed by a letter of `T`. -/
  | base {M Y V : Ty} {m : Term M ((T ⊗ S)⋆)} {y : Term Y T} :
      IsShiftInnerForm S T r m → IsDrop y → rank y ≤ r →
      TC S T r ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))
  /-- One more case of the co-pairing. -/
  | either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)} :
      TC S T r c₁ → TC S T r c₂ → TC S T r (Term.either c₁ c₂)
  /-- Replacing a content by a provably equal one. -/
  | congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} : c ≡ₜ c' → TC S T r c' → TC S T r c
  /-- Pre-composing with a lift. -/
  | lift {A A' : Ty} {rho : Term A A'} {c : Term A' ((S ⊕' T)⋆)} :
      IsLift rho → TC S T r c → TC S T r (rho ⨟ c)

namespace TC

theorem of_liftEq {A A' : Ty} {c : Term A ((S ⊕' T)⋆)} {c' : Term A' ((S ⊕' T)⋆)}
    (h : LiftEq c c') (hc : TC S T r c') : TC S T r c :=
  let ⟨_, hr, he⟩ := h
  TC.congr he (TC.lift hr hc)

/-- A pair content followed by a letter of `T` is a tail content. -/
theorem base_pc {K Y V : Ty} {p : Term K ((S ⊕' T)⋆)} {y : Term Y T} (hp : PC S T r p)
    (hy : IsDrop y) (hry : rank y ≤ r) :
    TC S T r (p ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T)) := by
  obtain ⟨M, alpha, m, ha, hm, he⟩ := hp
  refine TC.congr ?_ (TC.lift (IsLift.prodF ha (IsLift.id (Y ⊗ V))) (TC.base hm hy hry))
  calc (p ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))
      ≡ₜ ((alpha ⨟ (m ⨟ pairContentTS S T)) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T)) :=
        fdot_congr he (PEq.refl _)
    _ ≡ₜ ((alpha ⨟ (m ⨟ pairContentTS S T)) ⊙
          (Term.id (Y ⊗ V) ⨟ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))) :=
        fdot_congr (PEq.refl _) (PEq.symm (PEq.id_comp _))
    _ ≡ₜ (prodF alpha (Term.id (Y ⊗ V)) ⨟
          ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V ⨟ y) ⨟ tLetter S T))) :=
        PEq.symm (fdot_precomp _ _ _ _)

/-- A pair content in front of a tail content is a tail content. -/
theorem pc_fdot {K A : Ty} {p : Term K ((S ⊕' T)⋆)} {v : Term A ((S ⊕' T)⋆)}
    (hp : PC S T r p) (hv : TC S T r v) : TC S T r (p ⊙ v) := by
  induction hv with
  | @base M Y V m y hm hy hry =>
      exact TC.of_liftEq (LiftEq.assoc' p _ _)
        (TC.base_pc (PC.fdot hp (PC.of_innerForm hm)) hy hry)
  | either _ _ ih₁ ih₂ =>
      exact TC.congr (fdot_either_distR _ _ _) (TC.lift (IsLift.distR _ _ _) (ih₁.either ih₂))
  | congr h _ ih => exact TC.congr (fdot_congr (PEq.refl _) h) ih
  | @lift A A' rho c hrho _ ih =>
      refine TC.congr ?_ (TC.lift (IsLift.prodF (IsLift.id K) hrho) ih)
      exact PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.id_comp _) (PEq.refl _)))

/-- A tail content followed by a letter of `S` is a pair content. -/
theorem fdot_sLetter {A W X : Ty} {v : Term A ((S ⊕' T)⋆)} {x : Term X S} (hv : TC S T r v)
    (hx : IsDrop x) (hrx : rank x ≤ r) :
    PC S T r (v ⊙ ((Term.snd W X ⨟ x) ⨟ sLetter S T)) := by
  induction hv with
  | @base M Y V m y hm hy hry =>
      exact PC.of_liftEq (LiftEq.assoc _ _ _)
        (PC.fdot (PC.of_innerForm hm) (PC.pairJunk hy hry hx hrx))
  | either _ _ ih₁ ih₂ =>
      exact PC.congr (fdot_either_distL _ _ _)
        (PC.lift_comp (IsLift.distL _ _ _) (PC.either ih₁ ih₂))
  | congr h _ ih => exact PC.congr (fdot_congr h (PEq.refl _)) ih
  | @lift A A' rho c hrho _ ih =>
      refine PC.congr ?_ (PC.lift_comp (IsLift.prodF hrho (IsLift.id (W ⊗ X))) ih)
      exact PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.refl _) (PEq.id_comp _)))

/-- Erasing, on the right, a factor that carries no letter. -/
theorem fst_comp {A : Ty} (V : Ty) {v : Term A ((S ⊕' T)⋆)} (hv : TC S T r v) :
    TC S T r (Term.fst A V ⨟ v) := by
  induction hv with
  | @base M Y V' m y hm hy hry =>
      have hjy : (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)) ≡ₜ
          (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)) := by
        calc (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T))
            ≡ₜ ((Term.fst (Y ⊗ V') V ⨟ (Term.fst Y V' ⨟ y)) ⨟ tLetter S T) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (((Term.fst (Y ⊗ V') V ⨟ Term.fst Y V') ⨟ y) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (((assocR Y V' V ⨟ Term.fst Y (V' ⊗ V)) ⨟ y) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.compL _ (fst_fst_assocR Y V' V))
          _ ≡ₜ ((assocR Y V' V ⨟ (Term.fst Y (V' ⊗ V) ⨟ y)) ⨟ tLetter S T) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)) :=
              PEq.comp_assoc _ _ _
      refine TC.congr ?_ (TC.lift
        (IsLift.comp (IsLift.assocR M (Y ⊗ V') V)
          (IsLift.prodF (IsLift.id M) (IsLift.assocR Y V' V)))
        (TC.base (V := V' ⊗ V) hm hy hry))
      calc (Term.fst (M ⊗ (Y ⊗ V')) V ⨟
            ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)))
          ≡ₜ (assocR M (Y ⊗ V') V ⨟ ((m ⨟ pairContentTS S T) ⊙
              (Term.fst (Y ⊗ V') V ⨟ ((Term.fst Y V' ⨟ y) ⨟ tLetter S T)))) := fst_fdot _ _
        _ ≡ₜ (assocR M (Y ⊗ V') V ⨟ ((m ⨟ pairContentTS S T) ⊙
              (assocR Y V' V ⨟ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)))) :=
            PEq.compR _ (fdot_congr (PEq.refl _) hjy)
        _ ≡ₜ (assocR M (Y ⊗ V') V ⨟ (prodF (Term.id M) (assocR Y V' V) ⨟
              ((m ⨟ pairContentTS S T) ⊙ ((Term.fst Y (V' ⊗ V) ⨟ y) ⨟ tLetter S T)))) :=
            PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
              (fdot_congr (PEq.id_comp _) (PEq.refl _))))
        _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  | either _ _ ih₁ ih₂ =>
      exact TC.congr (fst_either _ _) (TC.lift (IsLift.distL _ _ _) (ih₁.either ih₂))
  | congr h _ ih => exact TC.congr (PEq.compR _ h) ih
  | @lift A A' rho c hrho _ ih =>
      refine TC.congr ?_ (TC.lift (IsLift.prodF hrho (IsLift.id V)) ih)
      calc (Term.fst A V ⨟ (rho ⨟ c))
          ≡ₜ ((Term.fst A V ⨟ rho) ⨟ c) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((prodF rho (Term.id V) ⨟ Term.fst A' V) ⨟ c) :=
            PEq.compL _ (PEq.symm (PEq.nat_fst _ _))
        _ ≡ₜ (prodF rho (Term.id V) ⨟ (Term.fst A' V ⨟ c)) := PEq.comp_assoc _ _ _

/-- A tail content followed by the content of a shape is a tail content. -/
theorem fdot_shape {A : Ty} {v : Term A ((S ⊕' T)⋆)} (hv : TC S T r v) :
    {D : Ty} → {g : Term D (shiftCod S T)} → IsShiftExchangeShape S T r g →
      TC S T r (v ⊙ (g ⨟ shiftContent S T))
  | _, _, .empty A' => by
      refine TC.congr ?_ (TC.fst_comp A' hv)
      calc (v ⊙ ((Term.toUnit A' ⨟ Term.inl Ty.unit (S ⊗ (((T ⊗ S)⋆) ⊗ T))) ⨟
            shiftContent S T))
          ≡ₜ (v ⊙ (Term.toUnit A' ⨟ nilT (S ⊕' T))) :=
            fdot_congr (PEq.refl _) (content_empty S T A')
        _ ≡ₜ _ := prodF_nilconst_binconcat _
  | _, _, @IsShiftExchangeShape.inner _ _ _ W X M Y V x y m hx hrx hy hry hm => by
      refine TC.congr (fdot_congr (PEq.refl _) (content_inner x m y)) ?_
      exact TC.of_liftEq (LiftEq.assoc' _ _ _)
        (TC.pc_fdot (TC.fdot_sLetter hv hx hrx) (TC.base hm hy hry))
  | _, _, .either h₁ h₂ => by
      refine TC.congr ?_ (TC.lift (IsLift.distR _ _ _)
        (TC.either (TC.fdot_shape hv h₁) (TC.fdot_shape hv h₂)))
      calc (v ⊙ (Term.either _ _ ⨟ shiftContent S T))
          ≡ₜ (v ⊙ Term.either (_ ⨟ shiftContent S T) (_ ⨟ shiftContent S T)) :=
            fdot_congr (PEq.refl _) (Term.either_comp _ _ _)
        _ ≡ₜ _ := fdot_either_distR _ _ _

/-- A tail content followed by a content of the shape of the conclusion is a tail
content. -/
theorem fdot_sc {A K : Ty} {v : Term A ((S ⊕' T)⋆)} {w : Term K ((S ⊕' T)⋆)}
    (hv : TC S T r v) (hw : SC S T r w) : TC S T r (v ⊙ w) := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := hw
  refine TC.congr ?_ (TC.lift (IsLift.prodF (IsLift.id A) ha) (TC.fdot_shape hv hg))
  calc (v ⊙ w)
      ≡ₜ (v ⊙ (alpha ⨟ (g ⨟ shiftContent S T))) := fdot_congr (PEq.refl _) he
    _ ≡ₜ (prodF (Term.id A) alpha ⨟ (v ⊙ (g ⨟ shiftContent S T))) :=
        PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.id_comp _) (PEq.refl _)))

end TC

end Lax149335Proofs

bridge_export Lax149335Proofs
