import Lax149335Proofs.Appendix.Drops.BlockNaturality
import Mathlib.Tactic.Set

/-!
# The case *Block* of the exchange lemma (appendix, *Proof of Exchange Lemma*)

`Lax149335Proofs.Appendix.Drops.ExchangeProof` reduces the exchange lemma (Lemma 7.5) to the two
prime lifts `shift` and `block`, and `Lax149335Proofs.Appendix.Drops.ExchangeShiftBlock` proves the
case *Shift*.  This file proves the case *Block*: every drop `f : A ⇒ (S+T)*` followed by the
prime lift `block` has a lift-drop factorisation (`Lax149335Proofs.admitsExchange_block`).

Since `block` and `unblock` are mutually inverse (Axiom 4), this amounts to showing that
every drop `f` is *block-collectable* (`Lax149335Proofs.BlockColl`, in
`Lax149335Proofs.Appendix.Drops.BlockCollect`): provably equal to a lift, followed by a drop into
the co-domain `S* × (T × S*)*` of `block`, followed by `unblock`.  The proof is the induction
of the appendix on a normal form of the drop with list codomain
(`Lax149335Proofs.drop_normListable`):

* the three shapes of leaves are treated in `Lax149335Proofs.Appendix.Drops.BlockCollect`
  (`Lax149335Proofs.blockColl_of_leaf`);
* the co-pairing node is `Lax149335Proofs.BlockColl.either`, already available there;
* the concatenation node is `Lax149335Proofs.BlockColl.fdot` below.  Two block pairs merge into one
  as soon as one knows whether the first one ends with a block, which is what the peeling
  lift of `Lax149335Proofs.Appendix.Drops.BlockPeel` provides, and the merge laws of
  `Lax149335Proofs.Appendix.Drops.BlockMerge` then apply;
* the star node is `Lax149335Proofs.BlockColl.homT` below.  The content of a block pair, peeled, is
  either a word `a` of letters of `S` or a content with a last block (`Lax149335Proofs.BlockWB`),
  and a *list* of such contents is grouped by `block` into the leading words and the blocks
  that follow them; the instance of the exchange lemma for `block` that this needs is
  `Lax149335Proofs.liftDrop_listF_block`, proved in `Lax149335Proofs.Appendix.Drops.BlockNaturality`, and
  the two star laws are `Lax149335Proofs.Term.homT_sWord` and `Lax149335Proofs.Term.homT_unblockB`.

All the auxiliary statements are formulated for a content *pre-composed with an arbitrary
drop* (`Lax149335Proofs.BlockPost`, `Lax149335Proofs.BlockWBPost`), because the lifts produced by the
normalisation lemmas have to be moved to the front; every lift that occurs in the argument
admits exchange, either because it is one of the prime lifts already treated in
`Lax149335Proofs.Appendix.Drops.ExchangeProof`, or because it is the instance of `block` above.
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

/-- Every drop into the domain of `X`, followed by `X`, is block-collectable. -/
def BlockPost (S T : Ty) {A : Ty} (X : Term A ((S ⊕' T)⋆)) : Prop :=
  ∀ {E : Ty} {e : Term E A}, IsDrop e → BlockColl S T (e ⨟ X)

namespace BlockPost

/-- A drop that is only provably a drop may be pre-composed as well. -/
theorem eqDrop {A E : Ty} {X : Term A ((S ⊕' T)⋆)} (h : BlockPost S T X) {e : Term E A}
    (he : IsEqDrop e) : BlockColl S T (e ⨟ X) := by
  obtain ⟨d, hd, hed⟩ := he
  exact BlockColl.congr (PEq.compL _ hed) (h hd)

theorem congr {A : Ty} {X X' : Term A ((S ⊕' T)⋆)} (h : X ≡ₜ X') (hX : BlockPost S T X') :
    BlockPost S T X := fun he => BlockColl.congr (PEq.compR _ h) (hX he)

/-- Pre-composing with a drop. -/
theorem comp_left {A B : Ty} {d : Term A B} (hd : IsEqDrop d) {X : Term B ((S ⊕' T)⋆)}
    (h : BlockPost S T X) : BlockPost S T (d ⨟ X) := by
  intro E e he
  refine BlockColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  exact h.eqDrop ((IsEqDrop.of_isDrop he).comp hd)

/-- Pre-composing with a lift that admits exchange. -/
theorem lift_comp {A B : Ty} {l : Term A B} (hl : AdmitsExchange l) {X : Term B ((S ⊕' T)⋆)}
    (h : BlockPost S T X) : BlockPost S T (l ⨟ X) := by
  intro E e he
  obtain ⟨D, mu, d, hmu, hd, hfac⟩ := hl he
  refine BlockColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine BlockColl.congr (PEq.compL _ hfac) ?_
  exact BlockColl.congr (PEq.comp_assoc _ _ _) (BlockColl.lift_comp hmu (h hd))

end BlockPost

/-- A co-pairing of two contents, pre-composed with a drop in normal form. -/
theorem blockColl_sumTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊕' B₂)} →
    IsNormalSumTree r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      BlockPost S T X₁ → BlockPost S T X₂ → BlockColl S T (g ⨟ Term.either X₁ X₂)
  | _, _, _, _, .inl hg₀ _, _, _, h₁, _ =>
      BlockColl.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either _ _))) (h₁ hg₀)
  | _, _, _, _, .inr hg₀ _, _, _, _, h₂ =>
      BlockColl.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inr_either _ _))) (h₂ hg₀)
  | _, _, _, _, .sumF hg₁ hg₂ _ _, _, _, h₁, h₂ =>
      BlockColl.congr (sumF_either _ _ _ _) ((h₁ hg₁).either (h₂ hg₂))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      BlockColl.congr (either_comp _ _ _)
        ((blockColl_sumTree t₁ h₁ h₂).either (blockColl_sumTree t₂ h₁ h₂))

/-- A co-pairing of two such contents. -/
theorem BlockPost.either {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : BlockPost S T X₁) (h₂ : BlockPost S T X₂) :
    BlockPost S T (Term.either X₁ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_sum_codomain_tree e he
  refine BlockColl.congr (PEq.compL _ hfac) ?_
  exact BlockColl.congr (PEq.comp_assoc _ _ _)
    (BlockColl.lift_comp ha (blockColl_sumTree hg h₁ h₂))

/-! ### The word and the block shapes -/

/-- A word of letters of `S`, pre-composed with a drop, is block-collectable. -/
theorem blockPost_sWord : BlockPost S T (Term.sWord S T) := fun he =>
  BlockColl.sword (IsEqDrop.of_isDrop he)

/-- The empty content, pre-composed with a drop, is block-collectable. -/
theorem blockPost_nilT : BlockPost S T (nilT (S ⊕' T)) :=
  BlockPost.congr (PEq.symm Term.nilT_sWord)
    (BlockPost.comp_left (isEqDrop_nilT S) blockPost_sWord)

/-- A block pair, pre-composed with a drop, is block-collectable. -/
theorem blockPost_unblock : BlockPost S T (Term.unblock S T) := fun he =>
  ⟨_, Term.id _, _, IsLift.id _, IsEqDrop.of_isDrop he, PEq.id_comp _⟩

/-- A block pair with a last block is a block pair. -/
theorem blockPost_unblockB : BlockPost S T (Term.unblockB S T) :=
  BlockPost.congr (PEq.symm (Term.appendBlock_unblock S T))
    (BlockPost.comp_left (IsEqDrop.of_isDrop (Term.isDrop_appendBlock S T)) blockPost_unblock)

/-! ### The canonical shape of a block-collectable content -/

/-- The domain of the canonical content: either a word of letters of `S`, or a block pair
with a last block. -/
abbrev wbCod (S T : Ty) : Ty := S⋆ ⊕' (blockCod S T ⊗ ZTy S T)

/-- The canonical content: a word of letters of `S`, or a block pair with a last block. -/
def wbContent (S T : Ty) : Term (wbCod S T) ((S ⊕' T)⋆) :=
  Term.either (Term.sWord S T) (Term.unblockB S T)

theorem inl_wbContent (S T : Ty) :
    (inl (S⋆) (blockCod S T ⊗ ZTy S T) ⨟ wbContent S T) ≡ₜ Term.sWord S T :=
  inl_either _ _

theorem inr_wbContent (S T : Ty) :
    (inr (S⋆) (blockCod S T ⊗ ZTy S T) ⨟ wbContent S T) ≡ₜ Term.unblockB S T :=
  inr_either _ _

/-- **The canonical shape of a block-collectable content.**  After a lift, the content is a
drop into `S* + (S* × (T × S*)* × (T × S*))` followed by the canonical content. -/
def BlockWB (S T : Ty) {A : Ty} (c : Term A ((S ⊕' T)⋆)) : Prop :=
  ∃ (D : Ty) (beta : Term A D) (k : Term D (wbCod S T)),
    IsLift beta ∧ IsDrop k ∧ c ≡ₜ (beta ⨟ (k ⨟ wbContent S T))

namespace BlockWB

theorem congr {A : Ty} {c c' : Term A ((S ⊕' T)⋆)} (h : c ≡ₜ c') (hc : BlockWB S T c') :
    BlockWB S T c := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := hc
  exact ⟨D, beta, k, hb, hk, h.trans he⟩

theorem lift_comp {A A' : Ty} {gamma : Term A' A} (hg : IsLift gamma)
    {c : Term A ((S ⊕' T)⋆)} (hc : BlockWB S T c) : BlockWB S T (gamma ⨟ c) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := hc
  exact ⟨D, gamma ⨟ beta, k, IsLift.comp hg hb, hk,
    (PEq.compR _ he).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

theorem either {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : BlockWB S T c₁) (h₂ : BlockWB S T c₂) : BlockWB S T (Term.either c₁ c₂) := by
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

end BlockWB

/-- Every drop into the domain of `X`, followed by `X`, has the canonical shape. -/
def BlockWBPost (S T : Ty) {A : Ty} (X : Term A ((S ⊕' T)⋆)) : Prop :=
  ∀ {E : Ty} {e : Term E A}, IsDrop e → BlockWB S T (e ⨟ X)

namespace BlockWBPost

theorem congr {A : Ty} {X X' : Term A ((S ⊕' T)⋆)} (h : X ≡ₜ X') (hX : BlockWBPost S T X') :
    BlockWBPost S T X := fun he => BlockWB.congr (PEq.compR _ h) (hX he)

/-- Pre-composing with a drop. -/
theorem comp_left {A B : Ty} {d : Term A B} (hd : IsDrop d) {X : Term B ((S ⊕' T)⋆)}
    (h : BlockWBPost S T X) : BlockWBPost S T (d ⨟ X) := by
  intro E e he
  exact BlockWB.congr (PEq.symm (PEq.comp_assoc _ _ _)) (h (he.comp hd))

/-- Pre-composing with a lift that admits exchange. -/
theorem lift_comp {A B : Ty} {l : Term A B} (hl : AdmitsExchange l) {X : Term B ((S ⊕' T)⋆)}
    (h : BlockWBPost S T X) : BlockWBPost S T (l ⨟ X) := by
  intro E e he
  obtain ⟨D, mu, d, hmu, hd, hfac⟩ := hl he
  refine BlockWB.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine BlockWB.congr (PEq.compL _ hfac) ?_
  exact BlockWB.congr (PEq.comp_assoc _ _ _) (BlockWB.lift_comp hmu (h hd))

end BlockWBPost

/-- A co-pairing of two canonical contents, pre-composed with a drop in normal form. -/
theorem blockWB_sumTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊕' B₂)} →
    IsNormalSumTree r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      BlockWBPost S T X₁ → BlockWBPost S T X₂ → BlockWB S T (g ⨟ Term.either X₁ X₂)
  | _, _, _, _, .inl hg₀ _, _, _, h₁, _ =>
      BlockWB.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either _ _))) (h₁ hg₀)
  | _, _, _, _, .inr hg₀ _, _, _, _, h₂ =>
      BlockWB.congr ((PEq.comp_assoc _ _ _).trans (PEq.compR _ (inr_either _ _))) (h₂ hg₀)
  | _, _, _, _, .sumF hg₁ hg₂ _ _, _, _, h₁, h₂ =>
      BlockWB.congr (sumF_either _ _ _ _) ((h₁ hg₁).either (h₂ hg₂))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      BlockWB.congr (either_comp _ _ _)
        ((blockWB_sumTree t₁ h₁ h₂).either (blockWB_sumTree t₂ h₁ h₂))

/-- A co-pairing of two contents that have the canonical shape after any drop. -/
theorem BlockWBPost.either {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : BlockWBPost S T X₁) (h₂ : BlockWBPost S T X₂) :
    BlockWBPost S T (Term.either X₁ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_sum_codomain_tree e he
  refine BlockWB.congr (PEq.compL _ hfac) ?_
  exact BlockWB.congr (PEq.comp_assoc _ _ _)
    (BlockWB.lift_comp ha (blockWB_sumTree hg h₁ h₂))

/-- The two shapes of the canonical content. -/
theorem blockWBPost_sWord : BlockWBPost S T (Term.sWord S T) := by
  intro E e he
  refine ⟨E, Term.id E, e ⨟ inl (S⋆) (blockCod S T ⊗ ZTy S T), IsLift.id E,
    he.comp (IsDrop.inl _ _), ?_⟩
  calc (e ⨟ Term.sWord S T)
      ≡ₜ (e ⨟ (inl (S⋆) (blockCod S T ⊗ ZTy S T) ⨟ wbContent S T)) :=
        PEq.compR _ (PEq.symm (inl_wbContent S T))
    _ ≡ₜ ((e ⨟ inl (S⋆) (blockCod S T ⊗ ZTy S T)) ⨟ wbContent S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id E ⨟ ((e ⨟ inl (S⋆) (blockCod S T ⊗ ZTy S T)) ⨟ wbContent S T)) :=
        PEq.symm (PEq.id_comp _)

theorem blockWBPost_unblockB : BlockWBPost S T (Term.unblockB S T) := by
  intro E e he
  refine ⟨E, Term.id E, e ⨟ inr (S⋆) (blockCod S T ⊗ ZTy S T), IsLift.id E,
    he.comp (IsDrop.inr _ _), ?_⟩
  calc (e ⨟ Term.unblockB S T)
      ≡ₜ (e ⨟ (inr (S⋆) (blockCod S T ⊗ ZTy S T) ⨟ wbContent S T)) :=
        PEq.compR _ (PEq.symm (inr_wbContent S T))
    _ ≡ₜ ((e ⨟ inr (S⋆) (blockCod S T ⊗ ZTy S T)) ⨟ wbContent S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id E ⨟ ((e ⨟ inr (S⋆) (blockCod S T ⊗ ZTy S T)) ⨟ wbContent S T)) :=
        PEq.symm (PEq.id_comp _)

/-- A word of letters of `S` followed by a list of blocks with a last block. -/
theorem Term.fdot_sWord_zWordB (S T : Ty) :
    (Term.sWord S T ⊙ Term.zWordB S T) ≡ₜ
      (assocL (S⋆) ((ZTy S T)⋆) (ZTy S T) ⨟ Term.unblockB S T) :=
  fdot_assoc' _ _ _

/-- The peeled content of a word followed by an empty list of blocks. -/
theorem blockWBPost_sWord_fdot_nilT :
    BlockWBPost S T (Term.sWord S T ⊙ nilT (S ⊕' T)) :=
  BlockWBPost.congr (Term.fdot_nil_right _)
    (blockWBPost_sWord.comp_left (IsDrop.fst (S⋆) Ty.unit))

/-- The peeled content of a word followed by a non-empty list of blocks. -/
theorem blockWBPost_sWord_fdot_peelContentR :
    BlockWBPost S T (Term.sWord S T ⊙ Term.peelContentR S T) := by
  set Z := ZTy S T with hZ
  have hstep : (Term.sWord S T ⊙ Term.peelContentR S T) ≡ₜ
      (prodF (Term.id (S⋆)) (snd Ty.unit (((Z ⊗ Ty.unit)⋆) ⊗ Z)) ⨟
        (prodF (Term.id (S⋆)) (prodF (listF (fst Z Ty.unit)) (Term.id Z)) ⨟
          (assocL (S⋆) (Z⋆) Z ⨟ Term.unblockB S T))) := by
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
  exact BlockWBPost.congr hstep
    (BlockWBPost.comp_left (IsDrop.prodF (IsDrop.id _) (IsDrop.snd _ _))
      (BlockWBPost.comp_left
        (IsDrop.prodF (IsDrop.id _)
          (IsDrop.prodF (IsDrop.listF (IsDrop.fst _ _)) (IsDrop.id _)))
        (blockWBPost_unblockB.comp_left (IsDrop.assocL _ _ _)))) he

/-- **The peeled content of a block pair.**  A word of letters of `S` followed by a peeled
list of blocks has the canonical shape. -/
theorem blockWBPost_sWord_fdot_peelContent :
    BlockWBPost S T (Term.sWord S T ⊙ Term.peelContent S T) := by
  exact BlockWBPost.congr (Term.fdot_either_distR _ _ _)
    (BlockWBPost.lift_comp (admitsExchange_distR _ _ _)
      (blockWBPost_sWord_fdot_nilT.either blockWBPost_sWord_fdot_peelContentR))

/-- A block pair given by a pair of drops has the canonical shape: the list of blocks is
peeled, which distinguishes a word from a content with a last block. -/
theorem blockWB_prodF_unblock {X Y : Ty} {x : Term X (S⋆)} {y : Term Y ((ZTy S T)⋆)}
    (hx : IsDrop x) (hy : IsDrop y) : BlockWB S T (prodF x y ⨟ Term.unblock S T) := by
  obtain ⟨E, mu, h, hmu, hh, hey⟩ := peel_last hy
  have key : (prodF x y ⨟ Term.unblock S T) ≡ₜ
      (prodF (Term.id X) mu ⨟
        (prodF x h ⨟ (Term.sWord S T ⊙ Term.peelContent S T))) := by
    calc (prodF x y ⨟ Term.unblock S T)
        ≡ₜ ((x ⨟ Term.sWord S T) ⊙ (y ⨟ Term.zWord S T)) := Term.prodF_unblock _ _
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
  exact BlockWB.congr key (BlockWB.lift_comp (IsLift.prodF (IsLift.id X) hmu)
    (blockWBPost_sWord_fdot_peelContent (hx.prodF hh)))

/-- A block pair given by a drop in normal form has the canonical shape. -/
theorem blockWB_prodTree {r : ℕ} : {D : Ty} → {g : Term D (blockCod S T)} →
    IsNormalProdLe r g → BlockWB S T (g ⨟ Term.unblock S T)
  | _, _, .prodF hx hy _ _ => blockWB_prodF_unblock hx hy
  | _, _, .either t₁ t₂ =>
      BlockWB.congr (either_comp _ _ _)
        ((blockWB_prodTree t₁).either (blockWB_prodTree t₂))

/-- **A block pair given by a drop has the canonical shape.** -/
theorem blockWB_comp_unblock {U : Ty} {u : Term U (blockCod S T)} (hu : IsDrop u) :
    BlockWB S T (u ⨟ Term.unblock S T) := by
  obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_prod_codomain_of_rank u hu
  refine BlockWB.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact BlockWB.lift_comp ha (blockWB_prodTree hg)

/-- **Every block-collectable content has the canonical shape**: the block list of the split
pair is peeled, which distinguishes the case of a word from the case of a content with a last
block. -/
theorem blockWB_of_blockColl {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : BlockColl S T c) :
    BlockWB S T c := by
  obtain ⟨D, beta, q, hb, hq, he⟩ := h
  obtain ⟨d, hd, hqd⟩ := hq
  refine BlockWB.congr (PEq.symm he) (BlockWB.lift_comp hb ?_)
  exact BlockWB.congr (PEq.compL _ hqd) (blockWB_comp_unblock hd)

/-! ### The concatenation node -/

/-- A canonical content followed by a block pair is, after a lift, a block pair. -/
theorem blockPost_wbContent_fdot_unblock :
    BlockPost S T (wbContent S T ⊙ Term.unblock S T) := by
  have h₁ : BlockPost S T (Term.sWord S T ⊙ Term.unblock S T) := by
    refine BlockPost.congr (Term.fdot_sWord_unblock S T) ?_
    exact BlockPost.comp_left
      (IsEqDrop.of_isDrop (IsDrop.comp (IsDrop.assocL _ _ _)
        (IsDrop.prodF (IsDrop.binconcat _) (IsDrop.id _)))) blockPost_unblock
  have h₂ : BlockPost S T (Term.unblockB S T ⊙ Term.unblock S T) := by
    obtain ⟨d, hd, he⟩ := Term.fdot_unblockB_unblock S T
    exact BlockPost.congr he
      (BlockPost.comp_left (IsEqDrop.of_isDrop hd) blockPost_unblock)
  intro E e he
  exact BlockPost.congr (Term.fdot_either_distL _ _ _)
    (BlockPost.lift_comp (admitsExchange_distL _ _ _) (h₁.either h₂)) he

/-- The concatenation of two block pairs given by drops is block-collectable. -/
theorem blockColl_prodF_unblock_unblock {U V : Ty} {u : Term U (blockCod S T)}
    {v : Term V (blockCod S T)} (hu : IsDrop u) (hv : IsDrop v) :
    BlockColl S T (prodF u v ⨟ (Term.unblock S T ⊙ Term.unblock S T)) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := blockWB_comp_unblock hu
  have key : (prodF u v ⨟ (Term.unblock S T ⊙ Term.unblock S T)) ≡ₜ
      (prodF beta (Term.id V) ⨟
        (prodF k v ⨟ (wbContent S T ⊙ Term.unblock S T))) := by
    calc (prodF u v ⨟ (Term.unblock S T ⊙ Term.unblock S T))
        ≡ₜ ((u ⨟ Term.unblock S T) ⊙ (v ⨟ Term.unblock S T)) := Term.fdot_precomp _ _ _ _
      _ ≡ₜ ((beta ⨟ (k ⨟ wbContent S T)) ⊙ (v ⨟ Term.unblock S T)) :=
          Term.fdot_congr he (PEq.refl _)
      _ ≡ₜ (prodF beta (Term.id V) ⨟
            ((k ⨟ wbContent S T) ⊙ (v ⨟ Term.unblock S T))) := Term.fdot_precompL _ _ _
      _ ≡ₜ _ := PEq.compR _ (PEq.symm (Term.fdot_precomp _ _ _ _))
  exact BlockColl.congr key (BlockColl.lift_comp (IsLift.prodF hb (IsLift.id V))
    (blockPost_wbContent_fdot_unblock (hk.prodF hv)))

/-- The concatenation of two block pairs, pre-composed with a drop in normal form. -/
theorem blockColl_unblock_prodTree {r : ℕ} : {D : Ty} →
    {g : Term D (blockCod S T ⊗ blockCod S T)} → IsNormalProdLe r g →
      BlockColl S T (g ⨟ (Term.unblock S T ⊙ Term.unblock S T))
  | _, _, .prodF hu hv _ _ => blockColl_prodF_unblock_unblock hu hv
  | _, _, .either t₁ t₂ =>
      BlockColl.congr (either_comp _ _ _)
        ((blockColl_unblock_prodTree t₁).either (blockColl_unblock_prodTree t₂))

/-- **The merge law.**  The concatenation of two block pairs is, after a lift, a split
pair. -/
theorem blockPost_unblock_fdot_unblock :
    BlockPost S T (Term.unblock S T ⊙ Term.unblock S T) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_prod_codomain_of_rank e he
  refine BlockColl.congr (PEq.compL _ hfac) ?_
  exact BlockColl.congr (PEq.comp_assoc _ _ _)
    (BlockColl.lift_comp ha (blockColl_unblock_prodTree hg))

/-- **Split-collectable contents are closed under concatenation.** -/
theorem BlockColl.fdot {A₁ A₂ : Ty} {c₁ : Term A₁ ((S ⊕' T)⋆)} {c₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : BlockColl S T c₁) (h₂ : BlockColl S T c₂) : BlockColl S T (c₁ ⊙ c₂) := by
  obtain ⟨D₁, b₁, q₁, hb₁, hq₁, he₁⟩ := h₁
  obtain ⟨D₂, b₂, q₂, hb₂, hq₂, he₂⟩ := h₂
  refine BlockColl.congr (Term.fdot_congr (PEq.symm he₁) (PEq.symm he₂)) ?_
  refine BlockColl.congr (PEq.symm (Term.fdot_precomp b₁ b₂ _ _)) ?_
  refine BlockColl.lift_comp (IsLift.prodF hb₁ hb₂) ?_
  refine BlockColl.congr (PEq.symm (Term.fdot_precomp q₁ q₂ _ _)) ?_
  exact blockPost_unblock_fdot_unblock.eqDrop (hq₁.prodF hq₂)

/-- A concatenation of two contents, pre-composed with a drop in normal form. -/
theorem blockColl_prodTree {r : ℕ} : {D B₁ B₂ : Ty} → {g : Term D (B₁ ⊗ B₂)} →
    IsNormalProdLe r g → {X₁ : Term B₁ ((S ⊕' T)⋆)} → {X₂ : Term B₂ ((S ⊕' T)⋆)} →
      BlockPost S T X₁ → BlockPost S T X₂ → BlockColl S T (g ⨟ (X₁ ⊙ X₂))
  | _, _, _, _, .prodF hx hy _ _, _, _, h₁, h₂ =>
      BlockColl.congr (Term.fdot_precomp _ _ _ _) ((h₁ hx).fdot (h₂ hy))
  | _, _, _, _, .either t₁ t₂, _, _, h₁, h₂ =>
      BlockColl.congr (either_comp _ _ _)
        ((blockColl_prodTree t₁ h₁ h₂).either (blockColl_prodTree t₂ h₁ h₂))

/-- A concatenation of two contents that are block-collectable after any drop. -/
theorem BlockPost.fdot {A₁ A₂ : Ty} {X₁ : Term A₁ ((S ⊕' T)⋆)} {X₂ : Term A₂ ((S ⊕' T)⋆)}
    (h₁ : BlockPost S T X₁) (h₂ : BlockPost S T X₂) : BlockPost S T (X₁ ⊙ X₂) := by
  intro E e he
  obtain ⟨D, alpha, g, ha, -, hg, hfac⟩ := drops_with_prod_codomain_of_rank e he
  refine BlockColl.congr (PEq.compL _ hfac) ?_
  exact BlockColl.congr (PEq.comp_assoc _ _ _)
    (BlockColl.lift_comp ha (blockColl_prodTree hg h₁ h₂))

/-! ### The star node -/

/-- A list of words of letters of `S` is a word of letters of `S`. -/
theorem blockPost_homT_sWord : BlockPost S T (Term.homT (Term.sWord S T)) :=
  BlockPost.congr (Term.homT_sWord S T)
    (BlockPost.comp_left (IsEqDrop.of_isDrop (IsDrop.concat S)) blockPost_sWord)

/-- A list of block pairs with a last block is empty or again such a content. -/
theorem blockPost_homT_unblockB : BlockPost S T (Term.homT (Term.unblockB S T)) := by
  obtain ⟨e, he, hfac⟩ := Term.homT_unblockB S T
  refine BlockPost.congr hfac ?_
  refine BlockPost.lift_comp (admitsExchange_shift _ _) ?_
  exact blockPost_nilT.either
    (BlockPost.comp_left (IsEqDrop.of_isDrop he) blockPost_unblockB)

/-- A list of contents `(block-ended pair) (word)*` is block-collectable after a drop. -/
theorem blockPost_homT_unblockB_fdot_homT_sWord :
    BlockPost S T (Term.homT (Term.unblockB S T ⊙ Term.homT (Term.sWord S T))) := by
  obtain ⟨d, hd, hfd⟩ := Term.fdot_unblockB_sWord S T
  have hin : (Term.unblockB S T ⊙ Term.homT (Term.sWord S T)) ≡ₜ
      ((prodF (Term.id (blockCod S T ⊗ ZTy S T)) (concat S) ⨟ d) ⨟ Term.unblockB S T) := by
    calc (Term.unblockB S T ⊙ Term.homT (Term.sWord S T))
        ≡ₜ (Term.unblockB S T ⊙ (concat S ⨟ Term.sWord S T)) :=
          Term.fdot_congr (PEq.refl _) (Term.homT_sWord S T)
      _ ≡ₜ (prodF (Term.id (blockCod S T ⊗ ZTy S T)) (concat S) ⨟
            (Term.unblockB S T ⊙ Term.sWord S T)) := Term.fdot_precompR _ _ _
      _ ≡ₜ (prodF (Term.id (blockCod S T ⊗ ZTy S T)) (concat S) ⨟
            (d ⨟ Term.unblockB S T)) := PEq.compR _ hfd
      _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  intro E e he
  exact BlockPost.congr (Term.homT_congr hin)
    (BlockPost.congr (Term.homT_precomp _ _)
      (BlockPost.comp_left (IsEqDrop.of_isDrop (IsDrop.listF
        (IsDrop.comp (IsDrop.prodF (IsDrop.id _) (IsDrop.concat S)) hd)))
        blockPost_homT_unblockB)) he

/-- **The star law.**  A list of canonical contents, indexed by the homomorphic image of a
drop, is block-collectable: `block` groups the list into the leading words of letters of `S`
and the contents with a last block that follow them. -/
theorem blockColl_listF_homT_wbContent {K : Ty} {k : Term K (wbCod S T)} (hk : IsDrop k) :
    BlockColl S T (listF k ⨟ Term.homT (wbContent S T)) := by
  obtain ⟨C, l, d, hl, hd, hfac⟩ :=
    liftDrop_listF_block (P := S⋆) (Q := blockCod S T ⊗ ZTy S T) hk
  have hY : Term.homT (wbContent S T) ≡ₜ
      (Term.block (S⋆) (blockCod S T ⊗ ZTy S T) ⨟
        (Term.homT (Term.sWord S T) ⊙
          Term.homT (Term.unblockB S T ⊙ Term.homT (Term.sWord S T)))) :=
    PEq.symm (block_content _ _)
  refine BlockColl.congr (PEq.compR _ hY) ?_
  refine BlockColl.congr (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine BlockColl.congr (PEq.compL _ hfac) ?_
  refine BlockColl.congr (PEq.comp_assoc _ _ _) (BlockColl.lift_comp hl ?_)
  exact (blockPost_homT_sWord.fdot blockPost_homT_unblockB_fdot_homT_sWord) hd

/-- **Split-collectable contents are closed under homomorphic images.** -/
theorem BlockColl.homT {A : Ty} {c : Term A ((S ⊕' T)⋆)} (h : BlockColl S T c) :
    BlockColl S T (Term.homT c) := by
  obtain ⟨D, beta, k, hb, hk, he⟩ := blockWB_of_blockColl h
  refine BlockColl.congr (Term.homT_congr he) ?_
  refine BlockColl.congr (Term.homT_precomp _ _) ?_
  refine BlockColl.lift_comp (IsLift.listF hb) ?_
  refine BlockColl.congr (Term.homT_precomp _ _) ?_
  exact blockColl_listF_homT_wbContent hk

/-! ### The induction on a normal form with list codomain -/

/-- Every drop in normal form with codomain `(S+T)*` is block-collectable. -/
theorem blockColl_of_normalForm {r : ℕ} : {A : Ty} → {g : Term A ((S ⊕' T)⋆)} →
    IsListNormalForm (S ⊕' T) r g → BlockColl S T g
  | _, _, .leaf hl => blockColl_of_leaf hl.isNormalListLeaf
  | _, _, .nil => BlockColl.congr (PEq.symm Term.nilT_sWord)
      (BlockColl.sword (isEqDrop_nilT S))
  | _, _, .fdot h₁ h₂ => (blockColl_of_normalForm h₁).fdot (blockColl_of_normalForm h₂)
  | _, _, .either h₁ h₂ => (blockColl_of_normalForm h₁).either (blockColl_of_normalForm h₂)
  | _, _, .homT h => (blockColl_of_normalForm h).homT

/-- **Every drop with codomain `(S+T)*` is block-collectable.** -/
theorem blockColl_of_drop {A : Ty} {f : Term A ((S ⊕' T)⋆)} (hf : IsDrop f) :
    BlockColl S T f := by
  obtain ⟨D, alpha, g, ha, hg, he⟩ := drop_normListable f hf
  exact BlockColl.congr he (BlockColl.lift_comp ha (blockColl_of_normalForm hg))

/-- **The case *Block* of the exchange lemma** (appendix).  Every drop with codomain
`(S+T)*`, followed by the prime lift `block`, has a lift-drop factorisation. -/
theorem admitsExchange_block (S T : Ty) : AdmitsExchange (Term.block S T) := by
  intro A d hd
  obtain ⟨D, beta, q, hb, hq, he⟩ := blockColl_of_drop (S := S) (T := T) hd
  refine IsLiftDrop.congr (PEq.compL _ (PEq.symm he)) ?_
  refine IsLiftDrop.congr (PEq.comp_assoc _ _ _) (IsLiftDrop.comp_left hb ?_)
  refine IsLiftDrop.congr (PEq.comp_assoc _ _ _) ?_
  refine IsLiftDrop.of_isEqDrop (IsEqDrop.congr ?_ hq)
  exact (PEq.compR _ (PEq.unblock_block S T)).trans (PEq.comp_id _)

end Lax149335Proofs

bridge_export Lax149335Proofs
