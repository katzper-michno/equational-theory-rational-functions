import Lax149335Proofs.Appendix.Drops.UnshiftNormalForm
import Lax149335Proofs.Appendix.Drops.UnshiftListNormal

/-!
# The list normalisation lemma (appendix, *Normalisation with list codomain*)

This file proves the third normalisation lemma for drops: every drop with a list codomain is
provably equal to a lift followed by a drop in the normal form `F(f₁,…,fₙ); genconc`, whose
leaves are constants, singletons or homomorphic images
(`Lax149335Proofs.drops_with_list_codomain`).

The proof is the one of the appendix: an induction on the composition rank.  A drop is either
one of the atoms of `Lax149335Proofs.IsDropAtom`, or provably equal to a drop of smaller rank
followed by an atom, and the atoms with a list codomain are

`id`, `h*`, `fst`, `snd`, `codiag`, `pure`, `binconcat`, `concat` and `unshift`.

The cases of `fst`, `snd`, `codiag` and `binconcat` are handled by the normalisation lemmas
for drops with a product, respectively a co-product, codomain
(`Lax149335Proofs.Appendix.Drops.SumProdNormalisation`), the cases of `h*` and of `concat` by
pushing the atom into the leaves of the normal form obtained for the first factor, and the
case of `unshift` is the one that needs the shift exchange lemma of the appendix section on
`shift`; it is proved in `Lax149335Proofs.Appendix.Drops.UnshiftListNormal`
(`Lax149335Proofs.normListable_comp_unshift`).

The normal shapes and the predicate `Lax149335Proofs.NormListable` maintained by the induction are
defined in `Lax149335Proofs.Appendix.Drops.ListNormalForm`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The induction hypothesis

The induction is on the composition rank, so the statement proved for the terms of smaller
rank is passed around explicitly. -/

/-- The list normalisation lemma for drops of rank at most `r`. -/
def ListNormalisable (r : ℕ) : Prop :=
  ∀ {A B : Ty} (g : Term A B⋆), IsDrop g → rank g ≤ r → NormListable B (rank g) g

/-- The instance of the induction hypothesis that the case distinctions use: a drop of rank
at most `r` is normalisable with the bound `r`. -/
theorem ListNormalisable.le {r : ℕ} (H : ListNormalisable r) {A B : Ty} (g : Term A B⋆)
    (hg : IsDrop g) (hr : rank g ≤ r) : NormListable B r g :=
  (H g hg hr).mono hr

/-! ### Co-pairing trees -/

/-- A co-pairing of drops with a list codomain is normalisable. -/
theorem normListable_copairTree {B : Ty} {r : ℕ} (H : ListNormalisable r) :
    {A : Ty} → {f : Term A B⋆} → CopairTree r f → NormListable B r f
  | _, _, .leaf hd hr he => NormListable.congr he (H.le _ hd hr)
  | _, _, .either t₁ t₂ he =>
      NormListable.congr he
        (NormListable.either (normListable_copairTree H t₁) (normListable_copairTree H t₂))

/-! ### Pushing an atom into the leaves of a normal shape -/

/-- A normal shape followed by a homomorphic image is normalisable: the map is pushed into
the leaves. -/
theorem normListable_shape_listF {X B : Ty} {r : ℕ} {h : Term X B} (hh : IsDrop h) {A : Ty}
    {g : Term A X⋆} (hg : IsListNormalForm X r g) :
    NormListable B (r + rank h + 1) (g ⨟ listF h) := by
  induction hg with
  | @leaf A' u hl =>
      cases hl with
      | const v =>
          exact NormListable.congr (PEq.comp_assoc _ _ _)
            (NormListable.of_leaf (.const (v ⨟ listF h)))
      | @sing A'' g' hd hr =>
          refine NormListable.congr ?_
            (NormListable.of_leaf (.sing (IsDrop.comp hd hh)
              (by have := rank_comp_le g' h; omega)))
          calc ((g' ⨟ pureT X) ⨟ listF h) ≡ₜ (g' ⨟ (pureT X ⨟ listF h)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (g' ⨟ (h ⨟ pureT B)) := PEq.compR _ (PEq.symm (Term.pureT_natural h))
            _ ≡ₜ ((g' ⨟ h) ⨟ pureT B) := PEq.symm (PEq.comp_assoc _ _ _)
      | @map A'' g' hd hr =>
          exact NormListable.congr (PEq.list_comp _ _)
            (NormListable.of_leaf (.map (IsDrop.comp hd hh)
              (by have := rank_comp_le g' h; omega)))
  | nil =>
      exact NormListable.congr (Term.nilT_natural h) (NormListable.of_isListNormalForm .nil)
  | @fdot A₁ A₂ u₁ u₂ _ _ ih₁ ih₂ =>
      exact NormListable.congr (Term.fdot_natural u₁ u₂ h) (NormListable.fdot ih₁ ih₂)
  | @either A₁ A₂ u₁ u₂ _ _ ih₁ ih₂ =>
      exact NormListable.congr (Term.either_comp u₁ u₂ (listF h))
        (NormListable.either ih₁ ih₂)
  | @homT A' u _ ih =>
      refine NormListable.congr ?_ (NormListable.homT ih)
      calc ((listF u ⨟ concat X) ⨟ listF h) ≡ₜ (listF u ⨟ (concat X ⨟ listF h)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (listF u ⨟ (listF (listF h) ⨟ concat B)) :=
            PEq.compR _ (PEq.symm (PEq.nat_concat h))
        _ ≡ₜ ((listF u ⨟ listF (listF h)) ⨟ concat B) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (listF (u ⨟ listF h) ⨟ concat B) := PEq.compL _ (PEq.list_comp _ _)

/-- A normal shape with codomain `B**` followed by `concat` is normalisable. -/
theorem normListable_shape_concat {B : Ty} {r : ℕ} (H : ListNormalisable r) {A : Ty}
    {g : Term A (B⋆)⋆} (hg : IsListNormalForm B⋆ r g) : NormListable B r (g ⨟ concat B) := by
  induction hg with
  | @leaf A' u hl =>
      cases hl with
      | const v =>
          exact NormListable.congr (PEq.comp_assoc _ _ _)
            (NormListable.of_leaf (.const (v ⨟ concat B)))
      | @sing A'' g' hd hr =>
          refine NormListable.congr ?_ (H.le g' hd hr)
          calc ((g' ⨟ pureT B⋆) ⨟ concat B) ≡ₜ (g' ⨟ (pureT B⋆ ⨟ concat B)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (g' ⨟ Term.id B⋆) := PEq.compR _ (PEq.pure_concat B)
            _ ≡ₜ g' := PEq.comp_id _
      | @map A'' g' hd hr => exact NormListable.homT (H.le g' hd hr)
  | nil => exact NormListable.congr (PEq.nil_concat B) (NormListable.of_isListNormalForm .nil)
  | @fdot A₁ A₂ u₁ u₂ _ _ ih₁ ih₂ =>
      refine NormListable.congr ?_ (NormListable.fdot ih₁ ih₂)
      calc ((prodF u₁ u₂ ⨟ binconcat B⋆) ⨟ concat B)
          ≡ₜ (prodF u₁ u₂ ⨟ (binconcat B⋆ ⨟ concat B)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (prodF u₁ u₂ ⨟ (prodF (concat B) (concat B) ⨟ binconcat B)) :=
            PEq.compR _ (PEq.binconcat_concat B)
        _ ≡ₜ ((prodF u₁ u₂ ⨟ prodF (concat B) (concat B)) ⨟ binconcat B) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (prodF (u₁ ⨟ concat B) (u₂ ⨟ concat B) ⨟ binconcat B) :=
            PEq.compL _ (PEq.prod_comp _ _ _ _)
  | @either A₁ A₂ u₁ u₂ _ _ ih₁ ih₂ =>
      exact NormListable.congr (Term.either_comp u₁ u₂ (concat B))
        (NormListable.either ih₁ ih₂)
  | @homT A' u _ ih =>
      refine NormListable.congr ?_ (NormListable.homT ih)
      calc ((listF u ⨟ concat B⋆) ⨟ concat B) ≡ₜ (listF u ⨟ (concat B⋆ ⨟ concat B)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (listF u ⨟ (listF (concat B) ⨟ concat B)) :=
            PEq.compR _ (PEq.symm (PEq.concat_concat B))
        _ ≡ₜ ((listF u ⨟ listF (concat B)) ⨟ concat B) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (listF (u ⨟ concat B) ⨟ concat B) := PEq.compL _ (PEq.list_comp _ _)

/-! ### The cases that use the product normalisation lemma -/

/-- A drop in normal form with product codomain, followed by the first projection onto a list
type, is normalisable: the second component is erased by a constantly empty leaf. -/
theorem normListable_normalProd_fst {B Y : Ty} {r : ℕ} (H : ListNormalisable r) :
    {A : Ty} → {g : Term A (B⋆ ⊗ Y)} → IsNormalProdLe r g →
      NormListable B r (g ⨟ Term.fst B⋆ Y)
  | _, _, @IsNormalProdLe.prodF _ _ _ _ _ x y hx _ hrx _ =>
      NormListable.congr ((PEq.nat_fst x y).trans
          (PEq.symm (Term.prodF_nilconst_binconcat x)))
        (NormListable.fdot (H.le x hx hrx) (NormListable.of_leaf (.const (nilT B))))
  | _, _, @IsNormalProdLe.either _ _ _ _ _ g₁ g₂ h₁ h₂ =>
      NormListable.congr (Term.either_comp g₁ g₂ _)
        (NormListable.either (normListable_normalProd_fst H h₁)
          (normListable_normalProd_fst H h₂))

/-- A drop in normal form with product codomain, followed by the second projection onto a
list type, is normalisable. -/
theorem normListable_normalProd_snd {B Y : Ty} {r : ℕ} (H : ListNormalisable r) :
    {A : Ty} → {g : Term A (Y ⊗ B⋆)} → IsNormalProdLe r g →
      NormListable B r (g ⨟ Term.snd Y B⋆)
  | _, _, @IsNormalProdLe.prodF _ _ _ _ _ x y _ hy _ hry =>
      NormListable.congr ((PEq.nat_snd x y).trans
          (PEq.symm (Term.prodF_nilconst_binconcat_left y)))
        (NormListable.fdot (NormListable.of_leaf (.const (nilT B))) (H.le y hy hry))
  | _, _, @IsNormalProdLe.either _ _ _ _ _ g₁ g₂ h₁ h₂ =>
      NormListable.congr (Term.either_comp g₁ g₂ _)
        (NormListable.either (normListable_normalProd_snd H h₁)
          (normListable_normalProd_snd H h₂))

/-- A drop in normal form with a product of two list types as codomain, followed by binary
concatenation, is normalisable. -/
theorem normListable_normalProd_binconcat {B : Ty} {r : ℕ} (H : ListNormalisable r) :
    {A : Ty} → {g : Term A (B⋆ ⊗ B⋆)} → IsNormalProdLe r g →
      NormListable B r (g ⨟ Term.binconcat B)
  | _, _, @IsNormalProdLe.prodF _ _ _ _ _ x y hx hy hrx hry =>
      NormListable.fdot (H.le x hx hrx) (H.le y hy hry)
  | _, _, @IsNormalProdLe.either _ _ _ _ _ g₁ g₂ h₁ h₂ =>
      NormListable.congr (Term.either_comp g₁ g₂ _)
        (NormListable.either (normListable_normalProd_binconcat H h₁)
          (normListable_normalProd_binconcat H h₂))

/-! ### The atoms with a list codomain

The nine atoms with a list codomain, each with the bound `0`: their leaves are identities,
constants, or the drop of a homomorphic image. -/

theorem normListable_id (B : Ty) : NormListable B 0 (Term.id B⋆) :=
  NormListable.congr (PEq.symm (PEq.list_id B))
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl))

theorem normListable_listF {X B : Ty} {h : Term X B} (hh : IsDrop h) :
    NormListable B (rank h) (listF h) :=
  NormListable.of_leaf (.map hh le_rfl)

theorem normListable_fst (B Y : Ty) : NormListable B 0 (Term.fst B⋆ Y) := by
  refine NormListable.congr ?_ (NormListable.fdot
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl))
    (NormListable.of_leaf (.const (nilT B))))
  calc Term.fst B⋆ Y ≡ₜ (Term.fst B⋆ Y ⨟ Term.id B⋆) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (prodF (Term.id B⋆) (toUnit Y ⨟ nilT B) ⨟ binconcat B) :=
        PEq.symm (Term.prodF_nilconst_binconcat (Term.id B⋆))
    _ ≡ₜ (prodF (listF (Term.id B)) (toUnit Y ⨟ nilT B) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.list_id B)) (PEq.refl _))

theorem normListable_snd (Y B : Ty) : NormListable B 0 (Term.snd Y B⋆) := by
  refine NormListable.congr ?_ (NormListable.fdot
    (NormListable.of_leaf (.const (nilT B)))
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl)))
  calc Term.snd Y B⋆ ≡ₜ (Term.snd Y B⋆ ⨟ Term.id B⋆) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (prodF (toUnit Y ⨟ nilT B) (Term.id B⋆) ⨟ binconcat B) :=
        PEq.symm (Term.prodF_nilconst_binconcat_left (Term.id B⋆))
    _ ≡ₜ (prodF (toUnit Y ⨟ nilT B) (listF (Term.id B)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.list_id B)))

theorem normListable_codiag (B : Ty) : NormListable B 0 (Term.codiag B⋆) := by
  refine NormListable.congr ?_ (NormListable.either
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl))
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl)))
  calc Term.codiag B⋆ ≡ₜ (Term.id (B⋆ ⊕' B⋆) ⨟ Term.codiag B⋆) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ (sumF (Term.id B⋆) (Term.id B⋆) ⨟ Term.codiag B⋆) :=
        PEq.compL _ (PEq.symm (PEq.sum_id _ _))
    _ ≡ₜ (sumF (listF (Term.id B)) (listF (Term.id B)) ⨟ Term.codiag B⋆) :=
        PEq.compL _ (PEq.congr_sumF (PEq.symm (PEq.list_id B)) (PEq.symm (PEq.list_id B)))

theorem normListable_pureT (B : Ty) : NormListable B 0 (Term.pureT B) :=
  NormListable.congr (PEq.symm (PEq.id_comp _))
    (NormListable.of_leaf (.sing (IsDrop.id B) le_rfl))

theorem normListable_binconcat (B : Ty) : NormListable B 0 (Term.binconcat B) := by
  refine NormListable.congr ?_ (NormListable.fdot
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl))
    (NormListable.of_leaf (.map (IsDrop.id B) le_rfl)))
  calc Term.binconcat B ≡ₜ (Term.id (B⋆ ⊗ B⋆) ⨟ Term.binconcat B) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ (prodF (Term.id B⋆) (Term.id B⋆) ⨟ Term.binconcat B) :=
        PEq.compL _ (PEq.symm (PEq.prod_id _ _))
    _ ≡ₜ (prodF (listF (Term.id B)) (listF (Term.id B)) ⨟ Term.binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.list_id B)) (PEq.symm (PEq.list_id B)))

theorem normListable_concat (B : Ty) : NormListable B 0 (Term.concat B) := by
  refine NormListable.congr ?_
    (NormListable.homT (NormListable.of_leaf (.map (IsDrop.id B) le_rfl)))
  calc Term.concat B ≡ₜ (Term.id (B⋆)⋆ ⨟ Term.concat B) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ (listF (Term.id B⋆) ⨟ Term.concat B) := PEq.compL _ (PEq.symm (PEq.list_id B⋆))
    _ ≡ₜ (listF (listF (Term.id B)) ⨟ Term.concat B) :=
        PEq.compL _ (PEq.congr_listF (PEq.symm (PEq.list_id B)))

theorem normListable_unshift (S T : Ty) : NormListable (S ⊗ T) 0 (Term.unshift S T) :=
  normListable_unshift_atom S T

/-- Every atom with a list codomain is normalisable, with the bound `rank f`. -/
theorem normListable_atom {A B : Ty} {f : Term A B⋆} (hf : IsDropAtom f) :
    NormListable B (rank f) f := by
  cases hf with
  | listF hh => exact normListable_listF hh
  | bangV A v => exact NormListable.of_leaf (.const v)
  | id _ => exact (normListable_id B).mono (Nat.zero_le _)
  | fst _ Y => exact (normListable_fst B Y).mono (Nat.zero_le _)
  | snd Y _ => exact (normListable_snd Y B).mono (Nat.zero_le _)
  | codiag _ => exact (normListable_codiag B).mono (Nat.zero_le _)
  | pureT _ => exact (normListable_pureT _).mono (Nat.zero_le _)
  | binconcat _ => exact (normListable_binconcat _).mono (Nat.zero_le _)
  | concat _ => exact (normListable_concat _).mono (Nat.zero_le _)
  | unshift S T => exact (normListable_unshift S T).mono (Nat.zero_le _)

/-! ### The induction -/

/-- Every drop with a list codomain of rank at most `m` is normalisable, by induction on the
composition rank. -/
theorem listNormalisable (m : ℕ) : ListNormalisable m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A B f hf hm
    -- the induction hypothesis, for the terms of rank smaller than that of `f`
    have IH : ∀ (k : ℕ), k < rank f → ListNormalisable k :=
      fun k hk _ _ g hg hr => ih k (lt_of_lt_of_le hk hm) g hg hr
    rcases hf.spine with ⟨f', hatom, hle, heq⟩ | ⟨C, f₁, f₂, hf₁, hf₂, hrank, heq⟩
    · exact NormListable.congr heq ((normListable_atom hatom).mono hle)
    · have H₁ : ListNormalisable (rank f₁) := IH (rank f₁) (by omega)
      refine NormListable.congr heq ?_
      cases hf₂ with
      | @listF X Y h hh =>
          obtain ⟨D, alpha, g, ha, hg, he⟩ := H₁ f₁ hf₁ le_rfl
          have hrl : rank (Term.listF h) = rank h := rfl
          refine NormListable.mono (show rank f₁ + rank h + 1 ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_shape_listF hh hg))
          calc (f₁ ⨟ listF h) ≡ₜ ((alpha ⨟ g) ⨟ listF h) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ listF h)) := PEq.comp_assoc _ _ _
      | id _ =>
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          exact NormListable.congr (PEq.comp_id f₁) (H₁ f₁ hf₁ le_rfl)
      | fst _ Y =>
          obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_prod_codomain_of_rank f₁ hf₁
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_normalProd_fst H₁ hg))
          calc (f₁ ⨟ Term.fst _ Y) ≡ₜ ((alpha ⨟ g) ⨟ Term.fst _ Y) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ Term.fst _ Y)) := PEq.comp_assoc _ _ _
      | snd Y _ =>
          obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_prod_codomain_of_rank f₁ hf₁
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_normalProd_snd H₁ hg))
          calc (f₁ ⨟ Term.snd Y _) ≡ₜ ((alpha ⨟ g) ⨟ Term.snd Y _) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ Term.snd Y _)) := PEq.comp_assoc _ _ _
      | codiag _ =>
          obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_sum_codomain_tree f₁ hf₁
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_copairTree H₁ hg.codiagPost))
          calc (f₁ ⨟ Term.codiag _) ≡ₜ ((alpha ⨟ g) ⨟ Term.codiag _) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ Term.codiag _)) := PEq.comp_assoc _ _ _
      | pureT _ => exact NormListable.of_leaf (.sing hf₁ (by omega))
      | binconcat _ =>
          obtain ⟨D, alpha, g, ha, -, hg, he⟩ := drops_with_prod_codomain_of_rank f₁ hf₁
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_normalProd_binconcat H₁ hg))
          calc (f₁ ⨟ Term.binconcat _) ≡ₜ ((alpha ⨟ g) ⨟ Term.binconcat _) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ Term.binconcat _)) := PEq.comp_assoc _ _ _
      | concat _ =>
          obtain ⟨D, alpha, g, ha, hg, he⟩ := H₁ f₁ hf₁ le_rfl
          refine NormListable.mono (show rank f₁ ≤ rank f by omega) ?_
          refine NormListable.congr ?_
            (NormListable.lift_comp ha (normListable_shape_concat H₁ hg))
          calc (f₁ ⨟ Term.concat _) ≡ₜ ((alpha ⨟ g) ⨟ Term.concat _) := PEq.compL _ he
            _ ≡ₜ (alpha ⨟ (g ⨟ Term.concat _)) := PEq.comp_assoc _ _ _
      | unshift S T =>
          refine NormListable.mono (show rank f₁ + 1 ≤ rank f by omega) ?_
          exact normListable_comp_unshift f₁ hf₁ (fun m hm hr => H₁.le m hm hr)
      | bangV C v =>
          refine NormListable.congr ?_ (NormListable.of_leaf (.const v))
          exact (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- Every drop with a list codomain is provably equal to a lift followed by a normal
shape. -/
theorem drop_normListable {A B : Ty} (f : Term A B⋆) (hf : IsDrop f) :
    NormListable B (rank f) f :=
  listNormalisable (rank f) f hf le_rfl

/-- **Lemma (List normalisation)** (appendix).  Every drop with a list codomain is provably
equivalent to a lift followed by a drop in the normal form `F(f₁,…,fₙ); genconc`, where each
leaf `fᵢ` is a constant, a singleton `[g]` or a homomorphic image `g⋆` whose component `g`
has at most the rank of the original drop.

This is the corrected form of the statement of the appendix: the rank condition has to be
read on the components of the leaves, see the discussion in
`Lax149335Proofs.Appendix.Drops.DropNormalisation`. -/
theorem drops_with_list_codomain {A B : Ty} (f : Term A B⋆) (hf : IsDrop f) :
    ∃ (F : TyFn) (As : ℕ → Ty) (alpha : Term A (F.app As))
      (fs : (i : ℕ) → Term (As i) B⋆),
      IsLift alpha ∧ (∀ i, F.usesParam i → IsNormalListLeafLe B (rank f) (fs i)) ∧
        f ≡ₜ (alpha ⨟ normalListShape B F As fs) := by
  obtain ⟨F, L, alpha, ha, hl, he⟩ := (drop_normListable f hf).shaped
  exact ⟨F, leafTy L, alpha, leafTm L, ha, hl, he⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
