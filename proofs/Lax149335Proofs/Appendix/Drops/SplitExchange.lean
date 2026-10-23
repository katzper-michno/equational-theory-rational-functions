import Lax149335Proofs.Appendix.Drops.SplitNaturality
import Mathlib.Tactic.Set

/-!
# The case *Split* of the exchange lemma (appendix, *Proof of Exchange Lemma*)

`Lax149335Proofs.Appendix.Drops.ExchangeProof` reduces the exchange lemma (Lemma 7.5) to the two
prime lifts `shift` and `split`, and `Lax149335Proofs.Appendix.Drops.ExchangeShiftSplit` proves the
case *Shift*.  This file proves the case *Split*: every drop `f : A ⇒ (S+T)*` followed by the
prime lift `split` has a lift-drop factorisation (`Lax149335Proofs.admitsExchange_split`).

Since `split` and `unsplit` are mutually inverse (Axiom 4), this amounts to showing that
every drop `f` is *split-collectable* (`Lax149335Proofs.SplitColl`, in
`Lax149335Proofs.Appendix.Drops.SplitCollect`): provably equal to a lift, followed by a drop into
the co-domain `S* × (T × S*)*` of `split`, followed by `unsplit`.  The proof is the induction
of the appendix on a normal form of the drop with list codomain
(`Lax149335Proofs.drop_normListable`):

* the three shapes of leaves are treated in `Lax149335Proofs.Appendix.Drops.SplitCollect`
  (`Lax149335Proofs.splitColl_of_leaf`);
* the co-pairing node is `Lax149335Proofs.SplitColl.either`, already available there;
* the concatenation node is `Lax149335Proofs.SplitColl.fdot` below.  Two split pairs merge into one
  as soon as one knows whether the first one ends with a block, which is what the peeling
  lift of `Lax149335Proofs.Appendix.Drops.SplitPeel` provides, and the merge laws of
  `Lax149335Proofs.Appendix.Drops.SplitMerge` then apply;
* the star node is `Lax149335Proofs.SplitColl.homT` below.  The content of a split pair, peeled, is
  either a word `a` of letters of `S` or a content with a last block (`Lax149335Proofs.SplitWB`),
  and a *list* of such contents is grouped by `split` into the leading words and the blocks
  that follow them; the instance of the exchange lemma for `split` that this needs is
  `Lax149335Proofs.liftDrop_listF_split`, proved in `Lax149335Proofs.Appendix.Drops.SplitNaturality`, and
  the two star laws are `Lax149335Proofs.Term.homT_sWord` and `Lax149335Proofs.Term.homT_unsplitB`.

All the auxiliary statements are formulated for a content *pre-composed with an arbitrary
drop* (`Lax149335Proofs.SplitPost`, `Lax149335Proofs.SplitWBPost`), because the lifts produced by the
normalisation lemmas have to be moved to the front; every lift that occurs in the argument
admits exchange, either because it is one of the prime lifts already treated in
`Lax149335Proofs.Appendix.Drops.ExchangeProof`, or because it is the instance of `split` above.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

/-- A co-pairing of two drops is a drop: `either f g = (f + g) ; codiag`. -/
theorem isDrop_either {A₁ A₂ B : Ty} {f : Term A₁ B} {g : Term A₂ B} (hf : IsDrop f)
    (hg : IsDrop g) : IsDrop (Term.either f g) :=
  IsDrop.comp (IsDrop.sumF hf hg) (IsDrop.codiag B)

/-! ### Split-collectable contents pre-composed with a drop -/

/-- Every drop into the domain of `X`, followed by `X`, is split-collectable. -/
def SplitPost (S T : Ty) {A : Ty} (X : Term A ((S ⊕' T)⋆)) : Prop :=
  ∀ {E : Ty} {e : Term E A}, IsDrop e → SplitColl S T (e ⨟ X)

namespace SplitPost

/-- A drop that is only provably a drop may be pre-composed as well. -/
theorem eqDrop {A E : Ty} {X : Term A ((S ⊕' T)⋆)} (h : SplitPost S T X) {e : Term E A}
    (he : IsEqDrop e) : SplitColl S T (e ⨟ X) := by
  obtain ⟨d, hd, hed⟩ := he
  exact SplitColl.congr (PEq.compL _ hed) (h hd)

theorem congr {A : Ty} {X X' : Term A ((S ⊕' T)⋆)} (h : X ≡ₜ X') (hX : SplitPost S T X') :
    SplitPost S T X := fun he => SplitColl.congr (PEq.compR _ h) (hX he)

/-- Pre-composing with a drop. -/
theorem comp_left {A B : Ty} {d : Term A B} (hd : IsEqDrop d) {X : Term B ((S ⊕' T)⋆)}
    (h : SplitPost S T X) : SplitPost S T (d ⨟ X) := by
  intro E e he
  refine SplitColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  exact h.eqDrop ((IsEqDrop.of_isDrop he).comp hd)

/-- Pre-composing with a lift that admits exchange. -/
theorem lift_comp {A B : Ty} {l : Term A B} (hl : AdmitsExchange l) {X : Term B ((S ⊕' T)⋆)}
    (h : SplitPost S T X) : SplitPost S T (l ⨟ X) := by
  intro E e he
  obtain ⟨D, mu, d, hmu, hd, hfac⟩ := hl he
  refine SplitColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine SplitColl.congr (PEq.compL _ hfac) ?_
  exact SplitColl.congr (PEq.comp_assoc _ _ _) (SplitColl.lift_comp hmu (h hd))

end SplitPost

/-- A co-pairing of two contents, pre-composed with a drop in normal form. -/
theorem splitColl_sumTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊕' B₂)} →
    IsNormalSumTree r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      SplitPost S T X₁ → SplitPost S T X₂ → SplitColl S T (g ⨟ Term.either X₁ X₂)
  | _, _, _, _, .inl hg₀ _, _, _, h₁, _ =>
      SplitColl.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either _ _))) (h₁ hg₀)
  | _, _, _, _, .inr hg₀ _, _, _, _, h₂ =>
      SplitColl.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inr_either _ _))) (h₂ hg₀)
  | _, _, _, _, .sumF hg₁ hg₂ _ _, _, _, h₁, h₂ =>
      SplitColl.congr (sumF_either _ _ _ _) ((h₁ hg₁).either (h₂ hg₂))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      SplitColl.congr (either_comp _ _ _)
        ((splitColl_sumTree t₁ h₁ h₂).either (splitColl_sumTree t₂ h₁ h₂))

/-- A co-pairing of two such contents. -/
theorem SplitPost.either {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitPost S T X₁) (h₂ : SplitPost S T X₂) :
    SplitPost S T (Term.either X₁ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_sum_codomain_tree e he
  refine SplitColl.congr (PEq.compL _ hfac) ?_
  exact SplitColl.congr (PEq.comp_assoc _ _ _)
    (SplitColl.lift_comp ha (splitColl_sumTree hg h₁ h₂))

/-! ### The word and the block shapes -/

/-- A word of letters of `S`, pre-composed with a drop, is split-collectable. -/
theorem splitPost_sWord : SplitPost S T (Term.sWord S T) := fun he =>
  SplitColl.sword (IsEqDrop.of_isDrop he)

/-- The empty content, pre-composed with a drop, is split-collectable. -/
theorem splitPost_nilT : SplitPost S T (nilT (S ⊕' T)) :=
  SplitPost.congr (PEq.symm Term.nilT_sWord)
    (SplitPost.comp_left (isEqDrop_nilT S) splitPost_sWord)

/-- A split pair, pre-composed with a drop, is split-collectable. -/
theorem splitPost_unsplit : SplitPost S T (Term.unsplit S T) := fun he =>
  ⟨_, Term.id _, _, IsLift.id _, IsEqDrop.of_isDrop he, PEq.id_comp _⟩

/-- A split pair with a last block is a split pair. -/
theorem splitPost_unsplitB : SplitPost S T (Term.unsplitB S T) :=
  SplitPost.congr (PEq.symm (Term.appendBlock_unsplit S T))
    (SplitPost.comp_left (IsEqDrop.of_isDrop (Term.isDrop_appendBlock S T)) splitPost_unsplit)

/-! ### The canonical shape of a split-collectable content -/

/-- The domain of the canonical content: either a word of letters of `S`, or a split pair
with a last block. -/
abbrev wbCod (S T : Ty) : Ty := S⋆ ⊕' (splitCod S T ⊗ ZTy S T)

/-- The canonical content: a word of letters of `S`, or a split pair with a last block. -/
def wbContent (S T : Ty) : Term (wbCod S T) ((S ⊕' T)⋆) :=
  Term.either (Term.sWord S T) (Term.unsplitB S T)

theorem inl_wbContent (S T : Ty) :
    (inl (S⋆) (splitCod S T ⊗ ZTy S T) ⨟ wbContent S T) ≡ₜ Term.sWord S T :=
  inl_either _ _

theorem inr_wbContent (S T : Ty) :
    (inr (S⋆) (splitCod S T ⊗ ZTy S T) ⨟ wbContent S T) ≡ₜ Term.unsplitB S T :=
  inr_either _ _

/-- **The canonical shape of a split-collectable content.**  After a lift, the content is a
drop into `S* + (S* × (T × S*)* × (T × S*))` followed by the canonical content. -/
def SplitWB (S T : Ty) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (D : Ty) (beta : Term A D) (k : Term D (wbCod S T)),
    IsLift beta ∧ IsDrop k ∧ c ≡ₜ (beta ⨟ (k ⨟ wbContent S T))

namespace SplitWB

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : SplitWB S T c') :
    SplitWB S T c := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := hc
  exact ⟨D, beta, k, hb, hk, h.trans he⟩

theorem lift_comp {A A' : Ty} {gamma : Term A' A} (hg : IsLift gamma)
    {c : Term A ((S ⊕' T)⋆)} (hc : SplitWB S T c) : SplitWB S T (gamma ⨟ c) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := hc
  exact ⟨D, gamma ⨟ beta, k, IsLift.comp hg hb, hk,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitWB S T c₁) (h₂ : SplitWB S T c₂) : SplitWB S T (Term.either c₁ c₂) := by
  obtain ⟨D₁, b₁, k₁, hb₁, hk₁, he₁⟩ := h₁
  obtain ⟨D₂, b₂, k₂, hb₂, hk₂, he₂⟩ := h₂
  refine ⟨D₁ ⊕' D₂, sumF b₁ b₂, Term.either k₁ k₂, IsLift.sumF hb₁ hb₂,
    isDrop_either hk₁ hk₂, ?_⟩
  calc Term.either c₁ c₂
      ≡ₜ Term.either (b₁ ⨟ (k₁ ⨟ wbContent S T)) (b₂ ⨟ (k₂ ⨟ wbContent S T)) :=
        Term.either_congr he₁ he₂
    _ ≡ₜ (sumF b₁ b₂ ⨟ Term.either (k₁ ⨟ wbContent S T) (k₂ ⨟ wbContent S T)) :=
        PEq.symm (Term.sumF_either _ _ _ _)
    _ ≡ₜ (sumF b₁ b₂ ⨟ (Term.either k₁ k₂ ⨟ wbContent S T)) :=
        PEq.compR _ (PEq.symm (Term.either_comp _ _ _))

end SplitWB

/-- Every drop into the domain of `X`, followed by `X`, has the canonical shape. -/
def SplitWBPost (S T : Ty) {A : Ty} (X : Term A ((S ⊕' T)⋆)) : Prop :=
  ∀ {E : Ty} {e : Term E A}, IsDrop e → SplitWB S T (e ⨟ X)

namespace SplitWBPost

theorem congr {A : Ty} {X X' : Term A ((S ⊕' T)⋆)} (h : X ≡ₜ X') (hX : SplitWBPost S T X') :
    SplitWBPost S T X := fun he => SplitWB.congr (PEq.compR _ h) (hX he)

/-- Pre-composing with a drop. -/
theorem comp_left {A B : Ty} {d : Term A B} (hd : IsDrop d) {X : Term B ((S ⊕' T)⋆)}
    (h : SplitWBPost S T X) : SplitWBPost S T (d ⨟ X) := by
  intro E e he
  exact SplitWB.congr (PEq.symm (PEq.comp_assoc _ _ _)) (h (he.comp hd))

/-- Pre-composing with a lift that admits exchange. -/
theorem lift_comp {A B : Ty} {l : Term A B} (hl : AdmitsExchange l) {X : Term B ((S ⊕' T)⋆)}
    (h : SplitWBPost S T X) : SplitWBPost S T (l ⨟ X) := by
  intro E e he
  obtain ⟨D, mu, d, hmu, hd, hfac⟩ := hl he
  refine SplitWB.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine SplitWB.congr (PEq.compL _ hfac) ?_
  exact SplitWB.congr (PEq.comp_assoc _ _ _) (SplitWB.lift_comp hmu (h hd))

end SplitWBPost

/-- A co-pairing of two canonical contents, pre-composed with a drop in normal form. -/
theorem splitWB_sumTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊕' B₂)} →
    IsNormalSumTree r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      SplitWBPost S T X₁ → SplitWBPost S T X₂ → SplitWB S T (g ⨟ Term.either X₁ X₂)
  | _, _, _, _, .inl hg₀ _, _, _, h₁, _ =>
      SplitWB.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either _ _))) (h₁ hg₀)
  | _, _, _, _, .inr hg₀ _, _, _, _, h₂ =>
      SplitWB.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inr_either _ _))) (h₂ hg₀)
  | _, _, _, _, .sumF hg₁ hg₂ _ _, _, _, h₁, h₂ =>
      SplitWB.congr (sumF_either _ _ _ _) ((h₁ hg₁).either (h₂ hg₂))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      SplitWB.congr (either_comp _ _ _)
        ((splitWB_sumTree t₁ h₁ h₂).either (splitWB_sumTree t₂ h₁ h₂))

/-- A co-pairing of two contents that have the canonical shape after any drop. -/
theorem SplitWBPost.either {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitWBPost S T X₁) (h₂ : SplitWBPost S T X₂) :
    SplitWBPost S T (Term.either X₁ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_sum_codomain_tree e he
  refine SplitWB.congr (PEq.compL _ hfac) ?_
  exact SplitWB.congr (PEq.comp_assoc _ _ _)
    (SplitWB.lift_comp ha (splitWB_sumTree hg h₁ h₂))

/-- The two shapes of the canonical content. -/
theorem splitWBPost_sWord : SplitWBPost S T (Term.sWord S T) := by
  intro E e he
  refine ⟨E, Term.id E, e ⨟ inl (S⋆) (splitCod S T ⊗ ZTy S T), IsLift.id E,
    he.comp (IsDrop.inl _ _), ?_⟩
  calc (e ⨟ Term.sWord S T)
      ≡ₜ (e ⨟ (inl (S⋆) (splitCod S T ⊗ ZTy S T) ⨟ wbContent S T)) :=
        PEq.compR _ (PEq.symm (inl_wbContent S T))
    _ ≡ₜ ((e ⨟ inl (S⋆) (splitCod S T ⊗ ZTy S T)) ⨟ wbContent S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id E ⨟ ((e ⨟ inl (S⋆) (splitCod S T ⊗ ZTy S T)) ⨟ wbContent S T)) :=
        PEq.symm (PEq.id_comp _)

theorem splitWBPost_unsplitB : SplitWBPost S T (Term.unsplitB S T) := by
  intro E e he
  refine ⟨E, Term.id E, e ⨟ inr (S⋆) (splitCod S T ⊗ ZTy S T), IsLift.id E,
    he.comp (IsDrop.inr _ _), ?_⟩
  calc (e ⨟ Term.unsplitB S T)
      ≡ₜ (e ⨟ (inr (S⋆) (splitCod S T ⊗ ZTy S T) ⨟ wbContent S T)) :=
        PEq.compR _ (PEq.symm (inr_wbContent S T))
    _ ≡ₜ ((e ⨟ inr (S⋆) (splitCod S T ⊗ ZTy S T)) ⨟ wbContent S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id E ⨟ ((e ⨟ inr (S⋆) (splitCod S T ⊗ ZTy S T)) ⨟ wbContent S T)) :=
        PEq.symm (PEq.id_comp _)

/-- A word of letters of `S` followed by a list of blocks with a last block. -/
theorem Term.fdot_sWord_zWordB (S T : Ty) :
    (Term.sWord S T ⊙ Term.zWordB S T) ≡ₜ
      (assocL (S⋆) ((ZTy S T)⋆) (ZTy S T) ⨟ Term.unsplitB S T) :=
  fdot_assoc' _ _ _

/-- The peeled content of a word followed by an empty list of blocks. -/
theorem splitWBPost_sWord_fdot_nilT :
    SplitWBPost S T (Term.sWord S T ⊙ nilT (S ⊕' T)) :=
  SplitWBPost.congr (Term.fdot_nil_right _)
    (splitWBPost_sWord.comp_left (IsDrop.fst (S⋆) Ty.unit))

/-- The peeled content of a word followed by a non-empty list of blocks. -/
theorem splitWBPost_sWord_fdot_peelContentR :
    SplitWBPost S T (Term.sWord S T ⊙ Term.peelContentR S T) := by
  set Z := ZTy S T with hZ
  have hstep : (Term.sWord S T ⊙ Term.peelContentR S T) ≡ₜ
      (prodF (Term.id (S⋆)) (snd Ty.unit (((Z ⊗ Ty.unit)⋆) ⊗ Z)) ⨟
        (prodF (Term.id (S⋆)) (prodF (listF (fst Z Ty.unit)) (Term.id Z)) ⨟
          (assocL (S⋆) (Z⋆) Z ⨟ Term.unsplitB S T))) := by
    calc (Term.sWord S T ⊙ Term.peelContentR S T)
        ≡ₜ (prodF (Term.id (S⋆)) (snd Ty.unit (((Z ⊗ Ty.unit)⋆) ⊗ Z)) ⨟
            (Term.sWord S T ⊙ ((listF (fst Z Ty.unit) ⨟ Term.zWord S T) ⊙
              Term.zBlock S T))) := Term.fdot_precompR _ _ _
      _ ≡ₜ (prodF (Term.id (S⋆)) (snd Ty.unit (((Z ⊗ Ty.unit)⋆) ⊗ Z)) ⨟
            (Term.sWord S T ⊙ (prodF (listF (fst Z Ty.unit)) (Term.id Z) ⨟
              Term.zWordB S T))) :=
          PEq.compR _ (Term.fdot_congr (PEq.refl _) (Term.fdot_precompL _ _ _))
      _ ≡ₜ (prodF (Term.id (S⋆)) (snd Ty.unit (((Z ⊗ Ty.unit)⋆) ⊗ Z)) ⨟
            (prodF (Term.id (S⋆)) (prodF (listF (fst Z Ty.unit)) (Term.id Z)) ⨟
              (Term.sWord S T ⊙ Term.zWordB S T))) :=
          PEq.compR _ (Term.fdot_precompR _ _ _)
      _ ≡ₜ _ := PEq.compR _ (PEq.compR _ (Term.fdot_sWord_zWordB S T))
  intro E e he
  exact SplitWBPost.congr hstep
    (SplitWBPost.comp_left (IsDrop.prodF (IsDrop.id _) (IsDrop.snd _ _))
      (SplitWBPost.comp_left
        (IsDrop.prodF (IsDrop.id _)
          (IsDrop.prodF (IsDrop.listF (IsDrop.fst _ _)) (IsDrop.id _)))
        (splitWBPost_unsplitB.comp_left (IsDrop.assocL _ _ _)))) he

/-- **The peeled content of a split pair.**  A word of letters of `S` followed by a peeled
list of blocks has the canonical shape. -/
theorem splitWBPost_sWord_fdot_peelContent :
    SplitWBPost S T (Term.sWord S T ⊙ Term.peelContent S T) := by
  exact SplitWBPost.congr (Term.fdot_either_distR _ _ _)
    (SplitWBPost.lift_comp (admitsExchange_distR _ _ _)
      (splitWBPost_sWord_fdot_nilT.either splitWBPost_sWord_fdot_peelContentR))

/-- A split pair given by a pair of drops has the canonical shape: the list of blocks is
peeled, which distinguishes a word from a content with a last block. -/
theorem splitWB_prodF_unsplit {X Y : Ty} {x : Term X (S⋆)} {y : Term Y ((ZTy S T)⋆)}
    (hx : IsDrop x) (hy : IsDrop y) : SplitWB S T (prodF x y ⨟ Term.unsplit S T) := by
  obtain ⟨E, mu, h, hmu, hh, hey⟩ := peel_last hy
  have key : (prodF x y ⨟ Term.unsplit S T) ≡ₜ
      (prodF (Term.id X) mu ⨟
        (prodF x h ⨟ (Term.sWord S T ⊙ Term.peelContent S T))) := by
    calc (prodF x y ⨟ Term.unsplit S T)
        ≡ₜ ((x ⨟ Term.sWord S T) ⊙ (y ⨟ Term.zWord S T)) := Term.prodF_unsplit _ _
      _ ≡ₜ ((x ⨟ Term.sWord S T) ⊙
            ((mu ⨟ (h ⨟ Term.peelDrop (ZTy S T))) ⨟ Term.zWord S T)) :=
          Term.fdot_congr (PEq.refl _) (PEq.compL _ hey)
      _ ≡ₜ ((x ⨟ Term.sWord S T) ⊙
            (mu ⨟ ((h ⨟ Term.peelDrop (ZTy S T)) ⨟ Term.zWord S T))) :=
          Term.fdot_congr (PEq.refl _) (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((x ⨟ Term.sWord S T) ⊙
            (mu ⨟ (h ⨟ (Term.peelDrop (ZTy S T) ⨟ Term.zWord S T)))) :=
          Term.fdot_congr (PEq.refl _) (PEq.compR _ (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((x ⨟ Term.sWord S T) ⊙ (mu ⨟ (h ⨟ Term.peelContent S T))) :=
          Term.fdot_congr (PEq.refl _) (PEq.compR _ (PEq.compR _ (Term.peelDrop_zWord S T)))
      _ ≡ₜ (prodF (Term.id X) mu ⨟
            ((x ⨟ Term.sWord S T) ⊙ (h ⨟ Term.peelContent S T))) :=
          Term.fdot_precompR _ _ _
      _ ≡ₜ _ := PEq.compR _ (PEq.symm (Term.fdot_precomp _ _ _ _))
  exact SplitWB.congr key (SplitWB.lift_comp (IsLift.prodF (IsLift.id X) hmu)
    (splitWBPost_sWord_fdot_peelContent (hx.prodF hh)))

/-- A split pair given by a drop in normal form has the canonical shape. -/
theorem splitWB_prodTree {r : ℕ} : {D : Ty} → {g : Term D (splitCod S T)} →
    IsNormalProdLe r g → SplitWB S T (g ⨟ Term.unsplit S T)
  | _, _, .prodF hx hy _ _ => splitWB_prodF_unsplit hx hy
  | _, _, .either t₁ t₂ =>
      SplitWB.congr (either_comp _ _ _)
        ((splitWB_prodTree t₁).either (splitWB_prodTree t₂))

/-- **A split pair given by a drop has the canonical shape.** -/
theorem splitWB_comp_unsplit {U : Ty} {u : Term U (splitCod S T)} (hu : IsDrop u) :
    SplitWB S T (u ⨟ Term.unsplit S T) := by
  obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_prod_codomain_of_rank u hu
  refine SplitWB.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact SplitWB.lift_comp ha (splitWB_prodTree hg)

/-- **Every split-collectable content has the canonical shape**: the block list of the split
pair is peeled, which distinguishes the case of a word from the case of a content with a last
block. -/
theorem splitWB_of_splitColl {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SplitColl S T c) :
    SplitWB S T c := by
  obtain ⟨D, beta, q, hb, hq, he⟩ := h
  obtain ⟨d, hd, hqd⟩ := hq
  refine SplitWB.congr (PEq.symm he) (SplitWB.lift_comp hb ?_)
  exact SplitWB.congr (PEq.compL _ hqd) (splitWB_comp_unsplit hd)

/-! ### The concatenation node -/

/-- A canonical content followed by a split pair is, after a lift, a split pair. -/
theorem splitPost_wbContent_fdot_unsplit :
    SplitPost S T (wbContent S T ⊙ Term.unsplit S T) := by
  have h₁ : SplitPost S T (Term.sWord S T ⊙ Term.unsplit S T) := by
    refine SplitPost.congr (Term.fdot_sWord_unsplit S T) ?_
    exact SplitPost.comp_left
      (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.assocL _ _ _)
        (IsDrop.prodF (IsDrop.binconcat _) (IsDrop.id _)))) splitPost_unsplit
  have h₂ : SplitPost S T (Term.unsplitB S T ⊙ Term.unsplit S T) := by
    obtain ⟨d, hd, he⟩ := Term.fdot_unsplitB_unsplit S T
    exact SplitPost.congr he
      (SplitPost.comp_left (IsEqDrop.of_isDrop hd) splitPost_unsplit)
  intro E e he
  exact SplitPost.congr (Term.fdot_either_distL _ _ _)
    (SplitPost.lift_comp (admitsExchange_distL _ _ _) (h₁.either h₂)) he

/-- The concatenation of two split pairs given by drops is split-collectable. -/
theorem splitColl_prodF_unsplit_unsplit {U V : Ty} {u : Term U (splitCod S T)}
    {v : Term V (splitCod S T)} (hu : IsDrop u) (hv : IsDrop v) :
    SplitColl S T (prodF u v ⨟ (Term.unsplit S T ⊙ Term.unsplit S T)) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := splitWB_comp_unsplit hu
  have key : (prodF u v ⨟ (Term.unsplit S T ⊙ Term.unsplit S T)) ≡ₜ
      (prodF beta (Term.id V) ⨟
        (prodF k v ⨟ (wbContent S T ⊙ Term.unsplit S T))) := by
    calc (prodF u v ⨟ (Term.unsplit S T ⊙ Term.unsplit S T))
        ≡ₜ ((u ⨟ Term.unsplit S T) ⊙ (v ⨟ Term.unsplit S T)) := Term.fdot_precomp _ _ _ _
      _ ≡ₜ ((beta ⨟ (k ⨟ wbContent S T)) ⊙ (v ⨟ Term.unsplit S T)) :=
          Term.fdot_congr he (PEq.refl _)
      _ ≡ₜ (prodF beta (Term.id V) ⨟
            ((k ⨟ wbContent S T) ⊙ (v ⨟ Term.unsplit S T))) := Term.fdot_precompL _ _ _
      _ ≡ₜ _ := PEq.compR _ (PEq.symm (Term.fdot_precomp _ _ _ _))
  exact SplitColl.congr key (SplitColl.lift_comp (IsLift.prodF hb (IsLift.id V))
    (splitPost_wbContent_fdot_unsplit (hk.prodF hv)))

/-- The concatenation of two split pairs, pre-composed with a drop in normal form. -/
theorem splitColl_unsplit_prodTree {r : ℕ} : {D : Ty} →
    {g : Term D (splitCod S T ⊗ splitCod S T)} → IsNormalProdLe r g →
      SplitColl S T (g ⨟ (Term.unsplit S T ⊙ Term.unsplit S T))
  | _, _, .prodF hu hv _ _ => splitColl_prodF_unsplit_unsplit hu hv
  | _, _, .either t₁ t₂ =>
      SplitColl.congr (either_comp _ _ _)
        ((splitColl_unsplit_prodTree t₁).either (splitColl_unsplit_prodTree t₂))

/-- **The merge law.**  The concatenation of two split pairs is, after a lift, a split
pair. -/
theorem splitPost_unsplit_fdot_unsplit :
    SplitPost S T (Term.unsplit S T ⊙ Term.unsplit S T) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_prod_codomain_of_rank e he
  refine SplitColl.congr (PEq.compL _ hfac) ?_
  exact SplitColl.congr (PEq.comp_assoc _ _ _)
    (SplitColl.lift_comp ha (splitColl_unsplit_prodTree hg))

/-- **Split-collectable contents are closed under concatenation.** -/
theorem SplitColl.fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitColl S T c₁) (h₂ : SplitColl S T c₂) : SplitColl S T (c₁ ⊙ c₂) := by
  obtain ⟨D₁, b₁, q₁, hb₁, hq₁, he₁⟩ := h₁
  obtain ⟨D₂, b₂, q₂, hb₂, hq₂, he₂⟩ := h₂
  refine SplitColl.congr (Term.fdot_congr (PEq.symm he₁) (PEq.symm he₂)) ?_
  refine SplitColl.congr (PEq.symm (Term.fdot_precomp b₁ b₂ _ _)) ?_
  refine SplitColl.lift_comp (IsLift.prodF hb₁ hb₂) ?_
  refine SplitColl.congr (PEq.symm (Term.fdot_precomp q₁ q₂ _ _)) ?_
  exact splitPost_unsplit_fdot_unsplit.eqDrop (hq₁.prodF hq₂)

/-- A concatenation of two contents, pre-composed with a drop in normal form. -/
theorem splitColl_prodTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊗ B₂)} →
    IsNormalProdLe r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      SplitPost S T X₁ → SplitPost S T X₂ → SplitColl S T (g ⨟ (X₁ ⊙ X₂))
  | _, _, _, _, .prodF hx hy _ _, _, _, h₁, h₂ =>
      SplitColl.congr (Term.fdot_precomp _ _ _ _) ((h₁ hx).fdot (h₂ hy))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      SplitColl.congr (either_comp _ _ _)
        ((splitColl_prodTree t₁ h₁ h₂).either (splitColl_prodTree t₂ h₁ h₂))

/-- A concatenation of two contents that are split-collectable after any drop. -/
theorem SplitPost.fdot {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : SplitPost S T X₁) (h₂ : SplitPost S T X₂) : SplitPost S T (X₁ ⊙ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_prod_codomain_of_rank e he
  refine SplitColl.congr (PEq.compL _ hfac) ?_
  exact SplitColl.congr (PEq.comp_assoc _ _ _)
    (SplitColl.lift_comp ha (splitColl_prodTree hg h₁ h₂))

/-! ### The star node -/

/-- A list of words of letters of `S` is a word of letters of `S`. -/
theorem splitPost_homT_sWord : SplitPost S T (Term.homT (Term.sWord S T)) :=
  SplitPost.congr (Term.homT_sWord S T)
    (SplitPost.comp_left (IsEqDrop.of_isDrop (IsDrop.concat S)) splitPost_sWord)

/-- A list of split pairs with a last block is empty or again such a content. -/
theorem splitPost_homT_unsplitB : SplitPost S T (Term.homT (Term.unsplitB S T)) := by
  obtain ⟨e, he, hfac⟩ := Term.homT_unsplitB S T
  refine SplitPost.congr hfac ?_
  refine SplitPost.lift_comp (admitsExchange_shift _ _) ?_
  exact splitPost_nilT.either
    (SplitPost.comp_left (IsEqDrop.of_isDrop he) splitPost_unsplitB)

/-- A list of contents `(block-ended pair) (word)*` is split-collectable after a drop. -/
theorem splitPost_homT_unsplitB_fdot_homT_sWord :
    SplitPost S T (Term.homT (Term.unsplitB S T ⊙ Term.homT (Term.sWord S T))) := by
  obtain ⟨d, hd, hfd⟩ := Term.fdot_unsplitB_sWord S T
  have hin : (Term.unsplitB S T ⊙ Term.homT (Term.sWord S T)) ≡ₜ
      ((prodF (Term.id (splitCod S T ⊗ ZTy S T)) (concat S) ⨟ d) ⨟ Term.unsplitB S T) := by
    calc (Term.unsplitB S T ⊙ Term.homT (Term.sWord S T))
        ≡ₜ (Term.unsplitB S T ⊙ (concat S ⨟ Term.sWord S T)) :=
          Term.fdot_congr (PEq.refl _) (Term.homT_sWord S T)
      _ ≡ₜ (prodF (Term.id (splitCod S T ⊗ ZTy S T)) (concat S) ⨟
            (Term.unsplitB S T ⊙ Term.sWord S T)) := Term.fdot_precompR _ _ _
      _ ≡ₜ (prodF (Term.id (splitCod S T ⊗ ZTy S T)) (concat S) ⨟
            (d ⨟ Term.unsplitB S T)) := PEq.compR _ hfd
      _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  intro E e he
  exact SplitPost.congr (Term.homT_congr hin)
    (SplitPost.congr (Term.homT_precomp _ _)
      (SplitPost.comp_left (IsEqDrop.of_isDrop (IsDrop.listF
        (IsDrop.comp (IsDrop.prodF (IsDrop.id _) (IsDrop.concat S)) hd)))
        splitPost_homT_unsplitB)) he

/-- **The star law.**  A list of canonical contents, indexed by the homomorphic image of a
drop, is split-collectable: `split` groups the list into the leading words of letters of `S`
and the contents with a last block that follow them. -/
theorem splitColl_listF_homT_wbContent {K : Ty} {k : Term K (wbCod S T)} (hk : IsDrop k) :
    SplitColl S T (listF k ⨟ Term.homT (wbContent S T)) := by
  obtain ⟨C, l, d, hl, hd, hfac⟩ :=
    liftDrop_listF_split (P := S⋆) (Q := splitCod S T ⊗ ZTy S T) hk
  have hY : Term.homT (wbContent S T) ≡ₜ
      (Term.split (S⋆) (splitCod S T ⊗ ZTy S T) ⨟
        (Term.homT (Term.sWord S T) ⊙
          Term.homT (Term.unsplitB S T ⊙ Term.homT (Term.sWord S T)))) :=
    PEq.symm (split_content _ _)
  refine SplitColl.congr (PEq.compR _ hY) ?_
  refine SplitColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine SplitColl.congr (PEq.compL _ hfac) ?_
  refine SplitColl.congr (PEq.comp_assoc _ _ _) (SplitColl.lift_comp hl ?_)
  exact (splitPost_homT_sWord.fdot splitPost_homT_unsplitB_fdot_homT_sWord) hd

/-- **Split-collectable contents are closed under homomorphic images.** -/
theorem SplitColl.homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : SplitColl S T c) :
    SplitColl S T (Term.homT c) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := splitWB_of_splitColl h
  refine SplitColl.congr (Term.homT_congr he) ?_
  refine SplitColl.congr (Term.homT_precomp _ _) ?_
  refine SplitColl.lift_comp (IsLift.listF hb) ?_
  refine SplitColl.congr (Term.homT_precomp _ _) ?_
  exact splitColl_listF_homT_wbContent hk

/-! ### The induction on a normal form with list codomain -/

/-- Every drop in normal form with codomain `(S+T)*` is split-collectable. -/
theorem splitColl_of_normalForm {r : ℕ} : {A : Ty} → {g : Term A ((S ⊕' T)⋆)} →
    IsListNormalForm (S ⊕' T) r g → SplitColl S T g
  | _, _, .leaf hl => splitColl_of_leaf hl.isNormalListLeaf
  | _, _, .nil => SplitColl.congr (PEq.symm Term.nilT_sWord)
      (SplitColl.sword (isEqDrop_nilT S))
  | _, _, .fdot h₁ h₂ => (splitColl_of_normalForm h₁).fdot (splitColl_of_normalForm h₂)
  | _, _, .either h₁ h₂ => (splitColl_of_normalForm h₁).either (splitColl_of_normalForm h₂)
  | _, _, .homT h => (splitColl_of_normalForm h).homT

/-- **Every drop with codomain `(S+T)*` is split-collectable.** -/
theorem splitColl_of_drop {A : Ty} {f : Term A ((S ⊕' T)⋆)} (hf : IsDrop f) :
    SplitColl S T f := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := drop_normListable f hf
  exact SplitColl.congr he (SplitColl.lift_comp ha (splitColl_of_normalForm hg))

/-- **The case *Split* of the exchange lemma** (appendix).  Every drop with codomain
`(S+T)*`, followed by the prime lift `split`, has a lift-drop factorisation. -/
theorem admitsExchange_split (S T : Ty) : AdmitsExchange (Term.split S T) := by
  intro A d hd
  obtain ⟨D, beta, q, hb, hq, he⟩ := splitColl_of_drop (S := S) (T := T) hd
  refine IsLiftDrop.congr (PEq.compL _ (PEq.symm he)) ?_
  refine IsLiftDrop.congr (PEq.comp_assoc _ _ _) (IsLiftDrop.comp_left hb ?_)
  refine IsLiftDrop.congr (PEq.comp_assoc _ _ _) ?_
  refine IsLiftDrop.of_isEqDrop (IsEqDrop.congr ?_ hq)
  exact (PEq.compR _ (PEq.unsplit_split S T)).trans (PEq.comp_id _)

end Lax149335Proofs

bridge_export Lax149335Proofs
