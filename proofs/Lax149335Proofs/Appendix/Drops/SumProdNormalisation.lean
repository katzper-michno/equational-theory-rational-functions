import Lax149335Proofs.Appendix.Drops.SumProdNormalisationBase

/-!
# Normalisation of drops with sum or product codomain

This file contains the appendix section *Normalisation with sum or product codomain*
(appendix, `sum-and-product-codomain`), i.e. the two lemmas

* **sum normalisation** (`Lax149335Proofs.drops_with_sum_codomain`): a drop with a co-product
  codomain is a lift followed by a co-pairing, of arbitrary arity and associated to the
  right, of components of the form `gᵢ ; Left` or `gᵢ ; Right`, and
* **product normalisation** (`Lax149335Proofs.drops_with_prod_codomain_of_rank`): a drop with a
  product codomain is a lift followed by an `n`-ary co-pairing of products `xᵢ × yᵢ`,

both with the paper's condition that the components of the normal form have at most the rank
of the original drop.

The two lemmas are proved by the mutual induction on the rank of the drop that the appendix
describes, the case analysis being on the last prime function of the drop
(`Lax149335Proofs.IsDrop.spine`).  The induction produces the normal form with sum codomain as a
*case tree* (`Lax149335Proofs.IsNormalSumTree`), i.e. an arbitrarily nested co-pairing which may
also have leaves of the shape `g₁ + g₂`; the last section of the file turns such a tree into
the right-associated co-pairing of the paper (`Lax149335Proofs.IsNormalSumTree.toVec`), using the
prime lift `sumAssocR` for the re-association.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Pushing a prime drop through a normal form

The following lemmas push a prime drop through a normal form, either from the right (`Post`)
or from the left (`Pre`).  They are the computational content of the two normalisation
lemmas; none of them needs the induction hypothesis. -/

/-- Composing a case tree in normal form with the co-diagonal gives a co-pairing of drops of
the same rank. -/
theorem IsNormalSumTree.codiagPost {r : ℕ} : {D Z : Ty} → {N : Term D (Z ⊕' Z)} →
    IsNormalSumTree r N → CopairTree r (N ⨟ Term.codiag Z)
  | _, Z, _, .inl hg hr =>
      .leaf hg hr ((PEq.comp_assoc _ _ _).trans
        ((PEq.compR _ (PEq.inl_codiag Z)).trans (PEq.comp_id _)))
  | _, Z, _, .inr hg hr =>
      .leaf hg hr ((PEq.comp_assoc _ _ _).trans
        ((PEq.compR _ (PEq.inr_codiag Z)).trans (PEq.comp_id _)))
  | _, _, _, .sumF hg₁ hg₂ r₁ r₂ =>
      .either (.leaf hg₁ r₁ (PEq.refl _)) (.leaf hg₂ r₂ (PEq.refl _)) (PEq.refl _)
  | _, _, _, .either t₁ t₂ =>
      .either t₁.codiagPost t₂.codiagPost (either_comp _ _ _)

/-- Composing a case tree in normal form with a co-product of two drops gives again a case
tree in normal form. -/
theorem IsNormalSumTree.sumFPost {r t : ℕ} {C₁ C₂ E₁ E₂ : Ty} {h₁ : Term C₁ E₁}
    {h₂ : Term C₂ E₂} (hh₁ : IsDrop h₁) (hh₂ : IsDrop h₂) (ht₁ : rank h₁ ≤ t)
    (ht₂ : rank h₂ ≤ t) : {D : Ty} → {N : Term D (C₁ ⊕' C₂)} → IsNormalSumTree r N →
    ∃ N' : Term D (E₁ ⊕' E₂), IsNormalSumTree (r + t + 1) N' ∧ (N ⨟ Term.sumF h₁ h₂) ≡ₜ N'
  | _, _, @IsNormalSumTree.inl _ _ _ _ g hg hr =>
      ⟨(g ⨟ h₁) ⨟ Term.inl E₁ E₂,
        .inl (IsDrop.comp hg hh₁) (by simp only [rank]; split_ifs <;> omega),
        by
          calc ((g ⨟ Term.inl C₁ C₂) ⨟ Term.sumF h₁ h₂)
              ≡ₜ (g ⨟ (Term.inl C₁ C₂ ⨟ Term.sumF h₁ h₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (g ⨟ (h₁ ⨟ Term.inl E₁ E₂)) := PEq.compR _ (PEq.nat_inl h₁ h₂)
            _ ≡ₜ ((g ⨟ h₁) ⨟ Term.inl E₁ E₂) := PEq.symm (PEq.comp_assoc _ _ _)⟩
  | _, _, @IsNormalSumTree.inr _ _ _ _ g hg hr =>
      ⟨(g ⨟ h₂) ⨟ Term.inr E₁ E₂,
        .inr (IsDrop.comp hg hh₂) (by simp only [rank]; split_ifs <;> omega),
        by
          calc ((g ⨟ Term.inr C₁ C₂) ⨟ Term.sumF h₁ h₂)
              ≡ₜ (g ⨟ (Term.inr C₁ C₂ ⨟ Term.sumF h₁ h₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (g ⨟ (h₂ ⨟ Term.inr E₁ E₂)) :=
                PEq.compR _ (PEq.nat_inr h₁ h₂)
            _ ≡ₜ ((g ⨟ h₂) ⨟ Term.inr E₁ E₂) := PEq.symm (PEq.comp_assoc _ _ _)⟩
  | _, _, @IsNormalSumTree.sumF _ _ _ _ _ g₁ g₂ hg₁ hg₂ r₁ r₂ =>
      ⟨Term.sumF (g₁ ⨟ h₁) (g₂ ⨟ h₂),
        .sumF (IsDrop.comp hg₁ hh₁) (IsDrop.comp hg₂ hh₂)
          (by simp only [rank]; split_ifs <;> omega) (by simp only [rank]; split_ifs <;> omega),
        PEq.sum_comp _ _ _ _⟩
  | _, _, .either s₁ s₂ =>
      let ⟨N₁, hN₁, e₁⟩ := IsNormalSumTree.sumFPost hh₁ hh₂ ht₁ ht₂ s₁
      let ⟨N₂, hN₂, e₂⟩ := IsNormalSumTree.sumFPost hh₁ hh₂ ht₁ ht₂ s₂
      ⟨Term.either N₁ N₂, .either hN₁ hN₂,
        (either_comp _ _ _).trans (either_congr e₁ e₂)⟩

/-- Composing a normal form with product codomain with a product of two drops gives again a
normal form. -/
theorem IsNormalProdLe.prodFPost {r t : ℕ} {C₁ C₂ E₁ E₂ : Ty} {h₁ : Term C₁ E₁}
    {h₂ : Term C₂ E₂} (hh₁ : IsDrop h₁) (hh₂ : IsDrop h₂) (ht₁ : rank h₁ ≤ t)
    (ht₂ : rank h₂ ≤ t) : {D : Ty} → {M : Term D (C₁ ⊗ C₂)} → IsNormalProdLe r M →
    ∃ M' : Term D (E₁ ⊗ E₂), IsNormalProdLe (r + t + 1) M' ∧ (M ⨟ Term.prodF h₁ h₂) ≡ₜ M'
  | _, _, @IsNormalProdLe.prodF _ _ _ _ _ x y hx hy rx ry =>
      ⟨Term.prodF (x ⨟ h₁) (y ⨟ h₂),
        .prodF (IsDrop.comp hx hh₁) (IsDrop.comp hy hh₂)
          (by simp only [rank]; split_ifs <;> omega) (by simp only [rank]; split_ifs <;> omega),
        PEq.prod_comp _ _ _ _⟩
  | _, _, .either s₁ s₂ =>
      let ⟨M₁, hM₁, e₁⟩ := IsNormalProdLe.prodFPost hh₁ hh₂ ht₁ ht₂ s₁
      let ⟨M₂, hM₂, e₂⟩ := IsNormalProdLe.prodFPost hh₁ hh₂ ht₁ ht₂ s₂
      ⟨Term.either M₁ M₂, .either hM₁ hM₂,
        (either_comp _ _ _).trans (either_congr e₁ e₂)⟩

/-- Pre-composing a case tree in normal form with the first projection. -/
theorem IsNormalSumTree.fstPre {r : ℕ} (Y : Ty) : {E B₁ B₂ : Ty} → {N : Term E (B₁ ⊕' B₂)} →
    IsNormalSumTree r N → NormSum (r + 1) (Term.fst E Y ⨟ N)
  | E, _, _, _, @IsNormalSumTree.inl _ _ _ _ g hg hr =>
      NormSum.of_eq (PEq.symm (PEq.comp_assoc _ _ _))
        (NormSum.tree (.inl (IsDrop.comp (IsDrop.fst E Y) hg) (by simp only [rank]; split_ifs <;> omega)))
  | E, _, _, _, @IsNormalSumTree.inr _ _ _ _ g hg hr =>
      NormSum.of_eq (PEq.symm (PEq.comp_assoc _ _ _))
        (NormSum.tree (.inr (IsDrop.comp (IsDrop.fst E Y) hg) (by simp only [rank]; split_ifs <;> omega)))
  | _, _, _, _, @IsNormalSumTree.sumF _ E₁ E₂ _ _ g₁ g₂ hg₁ hg₂ r₁ r₂ =>
      ⟨(E₁ ⊗ Y) ⊕' (E₂ ⊗ Y), Term.distL E₁ E₂ Y,
        Term.sumF (Term.fst E₁ Y ⨟ g₁) (Term.fst E₂ Y ⨟ g₂), IsLift.distL _ _ _,
        .sumF (IsDrop.comp (IsDrop.fst _ _) hg₁) (IsDrop.comp (IsDrop.fst _ _) hg₂)
          (by simp only [rank]; split_ifs <;> omega) (by simp only [rank]; split_ifs <;> omega),
        by
          calc (Term.fst (E₁ ⊕' E₂) Y ⨟ Term.sumF g₁ g₂)
              ≡ₜ ((Term.distL E₁ E₂ Y ⨟ Term.sumF (Term.fst E₁ Y) (Term.fst E₂ Y)) ⨟
                  Term.sumF g₁ g₂) := PEq.compL _ (PEq.symm (Term.distL_fst E₁ E₂ Y))
            _ ≡ₜ (Term.distL E₁ E₂ Y ⨟ (Term.sumF (Term.fst E₁ Y) (Term.fst E₂ Y) ⨟
                  Term.sumF g₁ g₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distL E₁ E₂ Y ⨟
                  Term.sumF (Term.fst E₁ Y ⨟ g₁) (Term.fst E₂ Y ⨟ g₂)) :=
                PEq.compR _ (PEq.sum_comp _ _ _ _)⟩
  | _, _, _, _, @IsNormalSumTree.either _ E₁ E₂ _ _ M₁ M₂ s₁ s₂ =>
      NormSum.of_eq
        (by
          calc (Term.fst (E₁ ⊕' E₂) Y ⨟ Term.either M₁ M₂)
              ≡ₜ ((Term.distL E₁ E₂ Y ⨟ Term.sumF (Term.fst E₁ Y) (Term.fst E₂ Y)) ⨟
                  Term.either M₁ M₂) := PEq.compL _ (PEq.symm (Term.distL_fst E₁ E₂ Y))
            _ ≡ₜ (Term.distL E₁ E₂ Y ⨟ (Term.sumF (Term.fst E₁ Y) (Term.fst E₂ Y) ⨟
                  Term.either M₁ M₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distL E₁ E₂ Y ⨟
                  Term.either (Term.fst E₁ Y ⨟ M₁) (Term.fst E₂ Y ⨟ M₂)) :=
                PEq.compR _ (sumF_either _ _ _ _))
        (NormSum.lift_comp (IsLift.distL _ _ _)
          (NormSum.either (s₁.fstPre Y) (s₂.fstPre Y)))

/-- Pre-composing a case tree in normal form with the second projection. -/
theorem IsNormalSumTree.sndPre {r : ℕ} (Y : Ty) : {E B₁ B₂ : Ty} → {N : Term E (B₁ ⊕' B₂)} →
    IsNormalSumTree r N → NormSum (r + 1) (Term.snd Y E ⨟ N)
  | E, _, _, _, @IsNormalSumTree.inl _ _ _ _ g hg hr =>
      NormSum.of_eq (PEq.symm (PEq.comp_assoc _ _ _))
        (NormSum.tree (.inl (IsDrop.comp (IsDrop.snd Y E) hg) (by simp only [rank]; split_ifs <;> omega)))
  | E, _, _, _, @IsNormalSumTree.inr _ _ _ _ g hg hr =>
      NormSum.of_eq (PEq.symm (PEq.comp_assoc _ _ _))
        (NormSum.tree (.inr (IsDrop.comp (IsDrop.snd Y E) hg) (by simp only [rank]; split_ifs <;> omega)))
  | _, _, _, _, @IsNormalSumTree.sumF _ E₁ E₂ _ _ g₁ g₂ hg₁ hg₂ r₁ r₂ =>
      ⟨(Y ⊗ E₁) ⊕' (Y ⊗ E₂), Term.distR Y E₁ E₂,
        Term.sumF (Term.snd Y E₁ ⨟ g₁) (Term.snd Y E₂ ⨟ g₂), IsLift.distR _ _ _,
        .sumF (IsDrop.comp (IsDrop.snd _ _) hg₁) (IsDrop.comp (IsDrop.snd _ _) hg₂)
          (by simp only [rank]; split_ifs <;> omega) (by simp only [rank]; split_ifs <;> omega),
        by
          calc (Term.snd Y (E₁ ⊕' E₂) ⨟ Term.sumF g₁ g₂)
              ≡ₜ ((Term.distR Y E₁ E₂ ⨟ Term.sumF (Term.snd Y E₁) (Term.snd Y E₂)) ⨟
                  Term.sumF g₁ g₂) := PEq.compL _ (PEq.symm (Term.distR_snd Y E₁ E₂))
            _ ≡ₜ (Term.distR Y E₁ E₂ ⨟ (Term.sumF (Term.snd Y E₁) (Term.snd Y E₂) ⨟
                  Term.sumF g₁ g₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distR Y E₁ E₂ ⨟
                  Term.sumF (Term.snd Y E₁ ⨟ g₁) (Term.snd Y E₂ ⨟ g₂)) :=
                PEq.compR _ (PEq.sum_comp _ _ _ _)⟩
  | _, _, _, _, @IsNormalSumTree.either _ E₁ E₂ _ _ M₁ M₂ s₁ s₂ =>
      NormSum.of_eq
        (by
          calc (Term.snd Y (E₁ ⊕' E₂) ⨟ Term.either M₁ M₂)
              ≡ₜ ((Term.distR Y E₁ E₂ ⨟ Term.sumF (Term.snd Y E₁) (Term.snd Y E₂)) ⨟
                  Term.either M₁ M₂) := PEq.compL _ (PEq.symm (Term.distR_snd Y E₁ E₂))
            _ ≡ₜ (Term.distR Y E₁ E₂ ⨟ (Term.sumF (Term.snd Y E₁) (Term.snd Y E₂) ⨟
                  Term.either M₁ M₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distR Y E₁ E₂ ⨟
                  Term.either (Term.snd Y E₁ ⨟ M₁) (Term.snd Y E₂ ⨟ M₂)) :=
                PEq.compR _ (sumF_either _ _ _ _))
        (NormSum.lift_comp (IsLift.distR _ _ _)
          (NormSum.either (s₁.sndPre Y) (s₂.sndPre Y)))

/-- Pre-composing a normal form with product codomain with the first projection. -/
theorem IsNormalProdLe.fstPre {r : ℕ} (Z : Ty) : {E B₁ B₂ : Ty} → {M : Term E (B₁ ⊗ B₂)} →
    IsNormalProdLe r M → NormProd (r + 1) (Term.fst E Z ⨟ M)
  | _, _, _, _, @IsNormalProdLe.prodF _ E₁ E₂ _ _ a b ha hb ra rb =>
      ⟨E₁ ⊗ (E₂ ⊗ Z), Term.assocR E₁ E₂ Z, Term.prodF a (Term.fst E₂ Z ⨟ b),
        IsLift.assocR _ _ _,
        .prodF ha (IsDrop.comp (IsDrop.fst _ _) hb) (by omega) (by simp only [rank]; split_ifs <;> omega),
        Term.fst_prodF_assocR a b⟩
  | _, _, _, _, @IsNormalProdLe.either _ E₁ E₂ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq
        (by
          calc (Term.fst (E₁ ⊕' E₂) Z ⨟ Term.either N₁ N₂)
              ≡ₜ ((Term.distL E₁ E₂ Z ⨟ Term.sumF (Term.fst E₁ Z) (Term.fst E₂ Z)) ⨟
                  Term.either N₁ N₂) := PEq.compL _ (PEq.symm (Term.distL_fst E₁ E₂ Z))
            _ ≡ₜ (Term.distL E₁ E₂ Z ⨟ (Term.sumF (Term.fst E₁ Z) (Term.fst E₂ Z) ⨟
                  Term.either N₁ N₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distL E₁ E₂ Z ⨟
                  Term.either (Term.fst E₁ Z ⨟ N₁) (Term.fst E₂ Z ⨟ N₂)) :=
                PEq.compR _ (sumF_either _ _ _ _))
        (NormProd.lift_comp (IsLift.distL _ _ _)
          (NormProd.either (s₁.fstPre Z) (s₂.fstPre Z)))

/-- Pre-composing a normal form with product codomain with the second projection. -/
theorem IsNormalProdLe.sndPre {r : ℕ} (Z : Ty) : {E B₁ B₂ : Ty} → {M : Term E (B₁ ⊗ B₂)} →
    IsNormalProdLe r M → NormProd (r + 1) (Term.snd Z E ⨟ M)
  | _, _, _, _, @IsNormalProdLe.prodF _ E₁ E₂ _ _ a b ha hb ra rb =>
      ⟨(Z ⊗ E₁) ⊗ E₂, Term.assocL Z E₁ E₂, Term.prodF (Term.snd Z E₁ ⨟ a) b,
        IsLift.assocL _ _ _,
        .prodF (IsDrop.comp (IsDrop.snd _ _) ha) hb (by simp only [rank]; split_ifs <;> omega) (by omega),
        Term.snd_prodF_assocL a b⟩
  | _, _, _, _, @IsNormalProdLe.either _ E₁ E₂ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq
        (by
          calc (Term.snd Z (E₁ ⊕' E₂) ⨟ Term.either N₁ N₂)
              ≡ₜ ((Term.distR Z E₁ E₂ ⨟ Term.sumF (Term.snd Z E₁) (Term.snd Z E₂)) ⨟
                  Term.either N₁ N₂) := PEq.compL _ (PEq.symm (Term.distR_snd Z E₁ E₂))
            _ ≡ₜ (Term.distR Z E₁ E₂ ⨟ (Term.sumF (Term.snd Z E₁) (Term.snd Z E₂) ⨟
                  Term.either N₁ N₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distR Z E₁ E₂ ⨟
                  Term.either (Term.snd Z E₁ ⨟ N₁) (Term.snd Z E₂ ⨟ N₂)) :=
                PEq.compR _ (sumF_either _ _ _ _))
        (NormProd.lift_comp (IsLift.distR _ _ _)
          (NormProd.either (s₁.sndPre Z) (s₂.sndPre Z)))

/-- A product of a drop with a normal form, followed by the left associator. -/
theorem IsNormalProdLe.assocLLeaf {r : ℕ} {X B : Ty} {x : Term X B} (hx : IsDrop x)
    (hxr : rank x ≤ r) : {Y C D : Ty} → {M : Term Y (C ⊗ D)} → IsNormalProdLe r M →
    NormProd r (Term.prodF x M ⨟ Term.assocL B C D)
  | _, _, _, _, @IsNormalProdLe.prodF _ Y₁ Y₂ _ _ y z hy hz ry rz =>
      ⟨(X ⊗ Y₁) ⊗ Y₂, Term.assocL X Y₁ Y₂, Term.prodF (Term.prodF x y) z,
        IsLift.assocL _ _ _,
        .prodF (IsDrop.prodF hx hy) hz (by simp only [rank]; omega) rz,
        PEq.nat_assocL x y z⟩
  | _, _, _, _, @IsNormalProdLe.either _ Y₁ Y₂ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq
        (by
          calc (Term.prodF x (Term.either N₁ N₂) ⨟ Term.assocL B _ _)
              ≡ₜ ((Term.distR X Y₁ Y₂ ⨟
                    Term.either (Term.prodF x N₁) (Term.prodF x N₂)) ⨟ Term.assocL B _ _) :=
                PEq.compL _ (Term.prodF_either_distR N₁ N₂ x)
            _ ≡ₜ (Term.distR X Y₁ Y₂ ⨟
                  (Term.either (Term.prodF x N₁) (Term.prodF x N₂) ⨟ Term.assocL B _ _)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distR X Y₁ Y₂ ⨟
                  Term.either (Term.prodF x N₁ ⨟ Term.assocL B _ _)
                    (Term.prodF x N₂ ⨟ Term.assocL B _ _)) :=
                PEq.compR _ (either_comp _ _ _))
        (NormProd.lift_comp (IsLift.distR _ _ _)
          (NormProd.either (s₁.assocLLeaf hx hxr) (s₂.assocLLeaf hx hxr)))

/-- A product of a normal form with a drop, followed by the right associator. -/
theorem IsNormalProdLe.assocRLeaf {r : ℕ} {Y D : Ty} {y : Term Y D} (hy : IsDrop y)
    (hyr : rank y ≤ r) : {X B C : Ty} → {M : Term X (B ⊗ C)} → IsNormalProdLe r M →
    NormProd r (Term.prodF M y ⨟ Term.assocR B C D)
  | _, _, _, _, @IsNormalProdLe.prodF _ X₁ X₂ _ _ a b ha hb ra rb =>
      ⟨X₁ ⊗ (X₂ ⊗ Y), Term.assocR X₁ X₂ Y, Term.prodF a (Term.prodF b y),
        IsLift.assocR _ _ _,
        .prodF ha (IsDrop.prodF hb hy) ra (by simp only [rank]; omega),
        PEq.nat_assocR a b y⟩
  | _, _, _, _, @IsNormalProdLe.either _ X₁ X₂ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq
        (by
          calc (Term.prodF (Term.either N₁ N₂) y ⨟ Term.assocR _ _ D)
              ≡ₜ ((Term.distL X₁ X₂ Y ⨟
                    Term.either (Term.prodF N₁ y) (Term.prodF N₂ y)) ⨟ Term.assocR _ _ D) :=
                PEq.compL _ (Term.prodF_either_distL N₁ N₂ y)
            _ ≡ₜ (Term.distL X₁ X₂ Y ⨟
                  (Term.either (Term.prodF N₁ y) (Term.prodF N₂ y) ⨟ Term.assocR _ _ D)) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.distL X₁ X₂ Y ⨟
                  Term.either (Term.prodF N₁ y ⨟ Term.assocR _ _ D)
                    (Term.prodF N₂ y ⨟ Term.assocR _ _ D)) :=
                PEq.compR _ (either_comp _ _ _))
        (NormProd.lift_comp (IsLift.distL _ _ _)
          (NormProd.either (s₁.assocRLeaf hy hyr) (s₂.assocRLeaf hy hyr)))

/-! ### Pushing a projection or an associator through a normal form

These are the cases of the induction which appeal to the induction hypothesis: the leaves of
the normal form of `f₁` have to be normalised again before the last prime drop of `f` can be
pushed through them. -/

/-- A normal form with product codomain, followed by the first projection onto a
co-product. -/
theorem IsNormalProdLe.fstPostSum {r m : ℕ} (hS : SumNormalisable m) (hrm : r ≤ m) :
    {D B₁ B₂ Y : Ty} → {M : Term D ((B₁ ⊕' B₂) ⊗ Y)} → IsNormalProdLe r M →
    NormSum (r + 1) (M ⨟ Term.fst (B₁ ⊕' B₂) Y)
  | _, B₁, B₂, Y, _, @IsNormalProdLe.prodF _ X Y' _ _ x y hx hy rx ry => by
      obtain ⟨E, beta, T, hbeta, hT, hxe⟩ := hS x hx (rx.trans hrm)
      refine NormSum.of_eq ?_ (NormSum.lift_comp (IsLift.prodF hbeta (IsLift.id Y'))
        ((hT.mono rx).fstPre Y'))
      calc (Term.prodF x y ⨟ Term.fst (B₁ ⊕' B₂) Y)
          ≡ₜ (Term.fst X Y' ⨟ x) := PEq.nat_fst x y
        _ ≡ₜ (Term.fst X Y' ⨟ (beta ⨟ T)) := PEq.compR _ hxe
        _ ≡ₜ ((Term.fst X Y' ⨟ beta) ⨟ T) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((Term.prodF beta (Term.id Y') ⨟ Term.fst E Y') ⨟ T) :=
            PEq.compL _ (PEq.symm (PEq.nat_fst beta (Term.id Y')))
        _ ≡ₜ (Term.prodF beta (Term.id Y') ⨟ (Term.fst E Y' ⨟ T)) := PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormSum.of_eq (either_comp _ _ _)
        (NormSum.either (s₁.fstPostSum hS hrm) (s₂.fstPostSum hS hrm))

/-- A normal form with product codomain, followed by the second projection onto a
co-product. -/
theorem IsNormalProdLe.sndPostSum {r m : ℕ} (hS : SumNormalisable m) (hrm : r ≤ m) :
    {D B₁ B₂ Y : Ty} → {M : Term D (Y ⊗ (B₁ ⊕' B₂))} → IsNormalProdLe r M →
    NormSum (r + 1) (M ⨟ Term.snd Y (B₁ ⊕' B₂))
  | _, B₁, B₂, Y, _, @IsNormalProdLe.prodF _ X' X _ _ y x hy hx ry rx => by
      obtain ⟨E, beta, T, hbeta, hT, hxe⟩ := hS x hx (rx.trans hrm)
      refine NormSum.of_eq ?_ (NormSum.lift_comp (IsLift.prodF (IsLift.id X') hbeta)
        ((hT.mono rx).sndPre X'))
      calc (Term.prodF y x ⨟ Term.snd Y (B₁ ⊕' B₂))
          ≡ₜ (Term.snd X' X ⨟ x) := PEq.nat_snd y x
        _ ≡ₜ (Term.snd X' X ⨟ (beta ⨟ T)) := PEq.compR _ hxe
        _ ≡ₜ ((Term.snd X' X ⨟ beta) ⨟ T) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((Term.prodF (Term.id X') beta ⨟ Term.snd X' E) ⨟ T) :=
            PEq.compL _ (PEq.symm (PEq.nat_snd (Term.id X') beta))
        _ ≡ₜ (Term.prodF (Term.id X') beta ⨟ (Term.snd X' E ⨟ T)) := PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormSum.of_eq (either_comp _ _ _)
        (NormSum.either (s₁.sndPostSum hS hrm) (s₂.sndPostSum hS hrm))

/-- A normal form with product codomain, followed by the first projection onto a product. -/
theorem IsNormalProdLe.fstPostProd {r m : ℕ} (hP : ProdNormalisable m) (hrm : r ≤ m) :
    {D B₁ B₂ Z : Ty} → {M : Term D ((B₁ ⊗ B₂) ⊗ Z)} → IsNormalProdLe r M →
    NormProd (r + 1) (M ⨟ Term.fst (B₁ ⊗ B₂) Z)
  | _, B₁, B₂, Z, _, @IsNormalProdLe.prodF _ X Y _ _ x z hx hz rx rz => by
      obtain ⟨E, beta, M', hbeta, hM', hxe⟩ := hP x hx (rx.trans hrm)
      refine NormProd.of_eq ?_ (NormProd.lift_comp (IsLift.prodF hbeta (IsLift.id Y))
        ((hM'.mono rx).fstPre Y))
      calc (Term.prodF x z ⨟ Term.fst (B₁ ⊗ B₂) Z)
          ≡ₜ (Term.fst X Y ⨟ x) := PEq.nat_fst x z
        _ ≡ₜ (Term.fst X Y ⨟ (beta ⨟ M')) := PEq.compR _ hxe
        _ ≡ₜ ((Term.fst X Y ⨟ beta) ⨟ M') := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((Term.prodF beta (Term.id Y) ⨟ Term.fst E Y) ⨟ M') :=
            PEq.compL _ (PEq.symm (PEq.nat_fst beta (Term.id Y)))
        _ ≡ₜ (Term.prodF beta (Term.id Y) ⨟ (Term.fst E Y ⨟ M')) := PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq (either_comp _ _ _)
        (NormProd.either (s₁.fstPostProd hP hrm) (s₂.fstPostProd hP hrm))

/-- A normal form with product codomain, followed by the second projection onto a product. -/
theorem IsNormalProdLe.sndPostProd {r m : ℕ} (hP : ProdNormalisable m) (hrm : r ≤ m) :
    {D B₁ B₂ Z : Ty} → {M : Term D (Z ⊗ (B₁ ⊗ B₂))} → IsNormalProdLe r M →
    NormProd (r + 1) (M ⨟ Term.snd Z (B₁ ⊗ B₂))
  | _, B₁, B₂, Z, _, @IsNormalProdLe.prodF _ Y X _ _ z x hz hx rz rx => by
      obtain ⟨E, beta, M', hbeta, hM', hxe⟩ := hP x hx (rx.trans hrm)
      refine NormProd.of_eq ?_ (NormProd.lift_comp (IsLift.prodF (IsLift.id Y) hbeta)
        ((hM'.mono rx).sndPre Y))
      calc (Term.prodF z x ⨟ Term.snd Z (B₁ ⊗ B₂))
          ≡ₜ (Term.snd Y X ⨟ x) := PEq.nat_snd z x
        _ ≡ₜ (Term.snd Y X ⨟ (beta ⨟ M')) := PEq.compR _ hxe
        _ ≡ₜ ((Term.snd Y X ⨟ beta) ⨟ M') := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((Term.prodF (Term.id Y) beta ⨟ Term.snd Y E) ⨟ M') :=
            PEq.compL _ (PEq.symm (PEq.nat_snd (Term.id Y) beta))
        _ ≡ₜ (Term.prodF (Term.id Y) beta ⨟ (Term.snd Y E ⨟ M')) := PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq (either_comp _ _ _)
        (NormProd.either (s₁.sndPostProd hP hrm) (s₂.sndPostProd hP hrm))

/-- A normal form with product codomain, followed by the left associator. -/
theorem IsNormalProdLe.assocLPost {r m : ℕ} (hP : ProdNormalisable m) (hrm : r ≤ m) :
    {D B C E : Ty} → {M : Term D (B ⊗ (C ⊗ E))} → IsNormalProdLe r M →
    NormProd r (M ⨟ Term.assocL B C E)
  | _, B, C, E, _, @IsNormalProdLe.prodF _ X Y _ _ x w hx hw rx rw => by
      obtain ⟨F, beta, M', hbeta, hM', hwe⟩ := hP w hw (rw.trans hrm)
      refine NormProd.of_eq ?_ (NormProd.lift_comp (IsLift.prodF (IsLift.id X) hbeta)
        (IsNormalProdLe.assocLLeaf hx rx (hM'.mono rw)))
      calc (Term.prodF x w ⨟ Term.assocL B C E)
          ≡ₜ (Term.prodF (Term.id X ⨟ x) (beta ⨟ M') ⨟ Term.assocL B C E) :=
            PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) hwe)
        _ ≡ₜ ((Term.prodF (Term.id X) beta ⨟ Term.prodF x M') ⨟ Term.assocL B C E) :=
            PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
        _ ≡ₜ (Term.prodF (Term.id X) beta ⨟ (Term.prodF x M' ⨟ Term.assocL B C E)) :=
            PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq (either_comp _ _ _)
        (NormProd.either (s₁.assocLPost hP hrm) (s₂.assocLPost hP hrm))

/-- A normal form with product codomain, followed by the right associator. -/
theorem IsNormalProdLe.assocRPost {r m : ℕ} (hP : ProdNormalisable m) (hrm : r ≤ m) :
    {D B C E : Ty} → {M : Term D ((B ⊗ C) ⊗ E)} → IsNormalProdLe r M →
    NormProd r (M ⨟ Term.assocR B C E)
  | _, B, C, E, _, @IsNormalProdLe.prodF _ X Y _ _ w y hw hy rw ry => by
      obtain ⟨F, beta, M', hbeta, hM', hwe⟩ := hP w hw (rw.trans hrm)
      refine NormProd.of_eq ?_ (NormProd.lift_comp (IsLift.prodF hbeta (IsLift.id Y))
        (IsNormalProdLe.assocRLeaf hy ry (hM'.mono rw)))
      calc (Term.prodF w y ⨟ Term.assocR B C E)
          ≡ₜ (Term.prodF (beta ⨟ M') (Term.id Y ⨟ y) ⨟ Term.assocR B C E) :=
            PEq.compL _ (PEq.congr_prodF hwe (PEq.symm (PEq.id_comp _)))
        _ ≡ₜ ((Term.prodF beta (Term.id Y) ⨟ Term.prodF M' y) ⨟ Term.assocR B C E) :=
            PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
        _ ≡ₜ (Term.prodF beta (Term.id Y) ⨟ (Term.prodF M' y ⨟ Term.assocR B C E)) :=
            PEq.comp_assoc _ _ _
  | _, _, _, _, _, @IsNormalProdLe.either _ _ _ _ _ N₁ N₂ s₁ s₂ =>
      NormProd.of_eq (either_comp _ _ _)
        (NormProd.either (s₁.assocRPost hP hrm) (s₂.assocRPost hP hrm))

/-! ### The atoms -/

/-- A prime drop, or a functoriality combinator applied to drops, with co-product codomain is
already in normal form up to a lift. -/
theorem IsDropAtom.sumCases : {A B₁ B₂ : Ty} → {f : Term A (B₁ ⊕' B₂)} → IsDropAtom f →
    NormSum (rank f) f
  | _, _, _, _, .sumF hg₁ hg₂ =>
      NormSum.tree (.sumF hg₁ hg₂ (le_max_left _ _) (le_max_right _ _))
  | _, B₁, B₂, _, .id _ =>
      NormSum.of_eq (PEq.symm (PEq.sum_id B₁ B₂))
        (NormSum.tree (.sumF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _)))
  | _, B₁, B₂, _, .inl _ _ =>
      NormSum.of_eq (PEq.symm (PEq.id_comp _))
        (NormSum.tree (.inl (IsDrop.id B₁) (le_refl _)))
  | _, B₁, B₂, _, .inr _ _ =>
      NormSum.of_eq (PEq.symm (PEq.id_comp _))
        (NormSum.tree (.inr (IsDrop.id B₂) (le_refl _)))
  | _, B₁, B₂, _, .codiag _ =>
      NormSum.of_eq
        (PEq.symm
          (calc Term.either (Term.sumF (Term.id B₁) (Term.id B₂))
                  (Term.sumF (Term.id B₁) (Term.id B₂))
              ≡ₜ Term.either (Term.id (B₁ ⊕' B₂)) (Term.id (B₁ ⊕' B₂)) :=
                either_congr (PEq.sum_id _ _) (PEq.sum_id _ _)
            _ ≡ₜ (Term.id ((B₁ ⊕' B₂) ⊕' (B₁ ⊕' B₂)) ⨟ Term.codiag (B₁ ⊕' B₂)) :=
                PEq.compL _ (PEq.sum_id _ _)
            _ ≡ₜ Term.codiag (B₁ ⊕' B₂) := PEq.id_comp _))
        (NormSum.tree
          (.either (.sumF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _))
            (.sumF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _))))
  | _, B₁, B₂, _, .fst _ Y =>
      ⟨(B₁ ⊗ Y) ⊕' (B₂ ⊗ Y), Term.distL B₁ B₂ Y,
        Term.sumF (Term.fst B₁ Y) (Term.fst B₂ Y), IsLift.distL _ _ _,
        .sumF (IsDrop.fst _ _) (IsDrop.fst _ _) (le_refl _) (le_refl _),
        PEq.symm (Term.distL_fst B₁ B₂ Y)⟩
  | _, B₁, B₂, _, .snd Y _ =>
      ⟨(Y ⊗ B₁) ⊕' (Y ⊗ B₂), Term.distR Y B₁ B₂,
        Term.sumF (Term.snd Y B₁) (Term.snd Y B₂), IsLift.distR _ _ _,
        .sumF (IsDrop.snd _ _) (IsDrop.snd _ _) (le_refl _) (le_refl _),
        PEq.symm (Term.distR_snd Y B₁ B₂)⟩
  | A, _, _, _, .bangV _ v => by
      obtain ⟨u, hu, hvu⟩ := normalisation_of_values v
      cases hu with
      | @inl _ _ w _ =>
          exact NormSum.of_eq ((PEq.compR _ hvu).trans (PEq.symm (PEq.comp_assoc _ _ _)))
            (NormSum.tree (.inl (IsDrop.bangV A w) (by simp [rank_const])))
      | @inr _ _ w _ =>
          exact NormSum.of_eq ((PEq.compR _ hvu).trans (PEq.symm (PEq.comp_assoc _ _ _)))
            (NormSum.tree (.inr (IsDrop.bangV A w) (by simp [rank_const])))

/-- A prime drop, or a functoriality combinator applied to drops, with product codomain is
already in normal form up to a lift. -/
theorem IsDropAtom.prodCases : {A B₁ B₂ : Ty} → {f : Term A (B₁ ⊗ B₂)} → IsDropAtom f →
    NormProd (rank f) f
  | _, _, _, _, .prodF hx hy =>
      NormProd.tree (.prodF hx hy (le_max_left _ _) (le_max_right _ _))
  | _, B₁, B₂, _, .id _ =>
      NormProd.of_eq (PEq.symm (PEq.prod_id B₁ B₂))
        (NormProd.tree (.prodF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _)))
  | _, _, _, _, .assocL P Q R =>
      ⟨(P ⊗ Q) ⊗ R, Term.assocL P Q R, Term.prodF (Term.id (P ⊗ Q)) (Term.id R),
        IsLift.assocL _ _ _,
        .prodF (IsDrop.id _) (IsDrop.id _) (le_refl _) (le_refl _),
        PEq.symm ((PEq.compR _ (PEq.prod_id _ _)).trans (PEq.comp_id _))⟩
  | _, _, _, _, .assocR P Q R =>
      ⟨P ⊗ (Q ⊗ R), Term.assocR P Q R, Term.prodF (Term.id P) (Term.id (Q ⊗ R)),
        IsLift.assocR _ _ _,
        .prodF (IsDrop.id _) (IsDrop.id _) (le_refl _) (le_refl _),
        PEq.symm ((PEq.compR _ (PEq.prod_id _ _)).trans (PEq.comp_id _))⟩
  | _, B₁, B₂, _, .fst _ Z =>
      ⟨B₁ ⊗ (B₂ ⊗ Z), Term.assocR B₁ B₂ Z, Term.prodF (Term.id B₁) (Term.fst B₂ Z),
        IsLift.assocR _ _ _,
        .prodF (IsDrop.id _) (IsDrop.fst _ _) (le_refl _) (le_refl _),
        by
          calc Term.fst (B₁ ⊗ B₂) Z
              ≡ₜ (Term.fst (B₁ ⊗ B₂) Z ⨟ Term.id (B₁ ⊗ B₂)) := PEq.symm (PEq.comp_id _)
            _ ≡ₜ (Term.fst (B₁ ⊗ B₂) Z ⨟ Term.prodF (Term.id B₁) (Term.id B₂)) :=
                PEq.compR _ (PEq.symm (PEq.prod_id _ _))
            _ ≡ₜ (Term.assocR B₁ B₂ Z ⨟
                  Term.prodF (Term.id B₁) (Term.fst B₂ Z ⨟ Term.id B₂)) :=
                Term.fst_prodF_assocR _ _
            _ ≡ₜ (Term.assocR B₁ B₂ Z ⨟ Term.prodF (Term.id B₁) (Term.fst B₂ Z)) :=
                PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))⟩
  | _, B₁, B₂, _, .snd Z _ =>
      ⟨(Z ⊗ B₁) ⊗ B₂, Term.assocL Z B₁ B₂, Term.prodF (Term.snd Z B₁) (Term.id B₂),
        IsLift.assocL _ _ _,
        .prodF (IsDrop.snd _ _) (IsDrop.id _) (le_refl _) (le_refl _),
        by
          calc Term.snd Z (B₁ ⊗ B₂)
              ≡ₜ (Term.snd Z (B₁ ⊗ B₂) ⨟ Term.id (B₁ ⊗ B₂)) := PEq.symm (PEq.comp_id _)
            _ ≡ₜ (Term.snd Z (B₁ ⊗ B₂) ⨟ Term.prodF (Term.id B₁) (Term.id B₂)) :=
                PEq.compR _ (PEq.symm (PEq.prod_id _ _))
            _ ≡ₜ (Term.assocL Z B₁ B₂ ⨟
                  Term.prodF (Term.snd Z B₁ ⨟ Term.id B₁) (Term.id B₂)) :=
                Term.snd_prodF_assocL _ _
            _ ≡ₜ (Term.assocL Z B₁ B₂ ⨟ Term.prodF (Term.snd Z B₁) (Term.id B₂)) :=
                PEq.compR _ (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _))⟩
  | _, B₁, B₂, _, .codiag _ =>
      NormProd.of_eq
        (PEq.symm
          (calc Term.either (Term.prodF (Term.id B₁) (Term.id B₂))
                  (Term.prodF (Term.id B₁) (Term.id B₂))
              ≡ₜ Term.either (Term.id (B₁ ⊗ B₂)) (Term.id (B₁ ⊗ B₂)) :=
                either_congr (PEq.prod_id _ _) (PEq.prod_id _ _)
            _ ≡ₜ (Term.id ((B₁ ⊗ B₂) ⊕' (B₁ ⊗ B₂)) ⨟ Term.codiag (B₁ ⊗ B₂)) :=
                PEq.compL _ (PEq.sum_id _ _)
            _ ≡ₜ Term.codiag (B₁ ⊗ B₂) := PEq.id_comp _))
        (NormProd.tree
          (.either (.prodF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _))
            (.prodF (IsDrop.id B₁) (IsDrop.id B₂) (le_refl _) (le_refl _))))
  | A, _, _, _, .bangV _ v => by
      obtain ⟨u, hu, hvu⟩ := normalisation_of_values v
      cases hu with
      | @pair _ _ w₁ w₂ _ _ =>
          refine ⟨A ⊗ Ty.unit, Term.unitR A,
            Term.prodF (Term.toUnit A ⨟ w₁) (Term.toUnit Ty.unit ⨟ w₂), IsLift.unitR A,
            .prodF (IsDrop.bangV A w₁) (IsDrop.bangV Ty.unit w₂)
              (by simp [rank_const]) (by simp [rank_const]), ?_⟩
          calc (Term.toUnit A ⨟ v)
              ≡ₜ (Term.toUnit A ⨟ (Term.unitR Ty.unit ⨟ Term.prodF w₁ w₂)) :=
                PEq.compR _ hvu
            _ ≡ₜ ((Term.toUnit A ⨟ Term.unitR Ty.unit) ⨟ Term.prodF w₁ w₂) :=
                PEq.symm (PEq.comp_assoc _ _ _)
            _ ≡ₜ ((Term.unitR A ⨟ Term.prodF (Term.toUnit A) (Term.id Ty.unit)) ⨟
                  Term.prodF w₁ w₂) := PEq.compL _ (PEq.nat_unitR _)
            _ ≡ₜ (Term.unitR A ⨟ (Term.prodF (Term.toUnit A) (Term.id Ty.unit) ⨟
                  Term.prodF w₁ w₂)) := PEq.comp_assoc _ _ _
            _ ≡ₜ (Term.unitR A ⨟
                  Term.prodF (Term.toUnit A ⨟ w₁) (Term.id Ty.unit ⨟ w₂)) :=
                PEq.compR _ (PEq.prod_comp _ _ _ _)
            _ ≡ₜ (Term.unitR A ⨟
                  Term.prodF (Term.toUnit A ⨟ w₁) (Term.toUnit Ty.unit ⨟ w₂)) :=
                PEq.compR _ (PEq.congr_prodF (PEq.refl _)
                  (PEq.compL _ (PEq.unit_unique _ _)))

/-! ### The induction step -/

/-- The induction step of the sum normalisation lemma: a drop followed by an atom with
co-product codomain. -/
theorem IsDropAtom.sumStep {n : ℕ} (hS : SumNormalisable n) (hP : ProdNormalisable n)
    {A : Ty} : {C B₁ B₂ : Ty} → {f₂ : Term C (B₁ ⊕' B₂)} → IsDropAtom f₂ →
    ∀ f₁ : Term A C, IsDrop f₁ → rank f₁ ≤ n →
      NormSum (rank f₁ + rank f₂ + 1) (f₁ ⨟ f₂)
  | _, _, _, _, @IsDropAtom.sumF _ _ _ _ h₁ h₂ hh₁ hh₂, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, N, halpha, hN, he⟩ := hS f₁ hf₁ hr₁
      obtain ⟨N', hN', he'⟩ :=
        IsNormalSumTree.sumFPost hh₁ hh₂ (le_max_left _ _) (le_max_right _ _) hN
      exact ⟨D, alpha, N', halpha, hN',
        (PEq.compL _ he).trans ((PEq.comp_assoc _ _ _).trans (PEq.compR _ he'))⟩
  | _, _, _, _, .id _, f₁, hf₁, hr₁ =>
      NormSum.of_eq (PEq.comp_id _) ((hS f₁ hf₁ hr₁).mono (by omega))
  | _, _, _, _, .inl _ _, f₁, hf₁, hr₁ =>
      NormSum.tree (.inl hf₁ (by omega))
  | _, _, _, _, .inr _ _, f₁, hf₁, hr₁ =>
      NormSum.tree (.inr hf₁ (by omega))
  | _, B₁, B₂, _, .codiag .(B₁ ⊕' B₂), f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, N, halpha, hN, he⟩ := hS f₁ hf₁ hr₁
      refine NormSum.mono (by omega) (NormSum.of_eq ?_
        (NormSum.lift_comp halpha (CopairTree.normSum hS hr₁ hN.codiagPost)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .fst _ Y, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormSum.mono (by omega) (NormSum.of_eq ?_
        (NormSum.lift_comp halpha (hM.fstPostSum hS hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .snd Y _, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormSum.mono (by omega) (NormSum.of_eq ?_
        (NormSum.lift_comp halpha (hM.sndPostSum hS hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .bangV C v, f₁, hf₁, hr₁ => by
      refine NormSum.of_eq ?_
        (((IsDropAtom.bangV A v).sumCases).mono (by simp [rank_const]))
      exact (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- The induction step of the product normalisation lemma: a drop followed by an atom with
product codomain. -/
theorem IsDropAtom.prodStep {n : ℕ} (hS : SumNormalisable n) (hP : ProdNormalisable n)
    {A : Ty} : {C B₁ B₂ : Ty} → {f₂ : Term C (B₁ ⊗ B₂)} → IsDropAtom f₂ →
    ∀ f₁ : Term A C, IsDrop f₁ → rank f₁ ≤ n →
      NormProd (rank f₁ + rank f₂ + 1) (f₁ ⨟ f₂)
  | _, _, _, _, @IsDropAtom.prodF _ _ _ _ h₁ h₂ hh₁ hh₂, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      obtain ⟨M', hM', he'⟩ :=
        IsNormalProdLe.prodFPost hh₁ hh₂ (le_max_left _ _) (le_max_right _ _) hM
      exact ⟨D, alpha, M', halpha, hM',
        (PEq.compL _ he).trans ((PEq.comp_assoc _ _ _).trans (PEq.compR _ he'))⟩
  | _, _, _, _, .id _, f₁, hf₁, hr₁ =>
      NormProd.of_eq (PEq.comp_id _) ((hP f₁ hf₁ hr₁).mono (by omega))
  | _, _, _, _, .assocL P Q R, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormProd.mono (by omega) (NormProd.of_eq ?_
        (NormProd.lift_comp halpha (hM.assocLPost hP hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .assocR P Q R, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormProd.mono (by omega) (NormProd.of_eq ?_
        (NormProd.lift_comp halpha (hM.assocRPost hP hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .fst _ Z, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormProd.mono (by omega) (NormProd.of_eq ?_
        (NormProd.lift_comp halpha (hM.fstPostProd hP hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .snd Z _, f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, M, halpha, hM, he⟩ := hP f₁ hf₁ hr₁
      refine NormProd.mono (by omega) (NormProd.of_eq ?_
        (NormProd.lift_comp halpha (hM.sndPostProd hP hr₁)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, B₁, B₂, _, .codiag .(B₁ ⊗ B₂), f₁, hf₁, hr₁ => by
      obtain ⟨D, alpha, N, halpha, hN, he⟩ := hS f₁ hf₁ hr₁
      refine NormProd.mono (by omega) (NormProd.of_eq ?_
        (NormProd.lift_comp halpha (CopairTree.normProd hP hr₁ hN.codiagPost)))
      exact (PEq.compL _ he).trans (PEq.comp_assoc _ _ _)
  | _, _, _, _, .bangV C v, f₁, hf₁, hr₁ => by
      refine NormProd.of_eq ?_
        (((IsDropAtom.bangV A v).prodCases).mono (by simp [rank_const]))
      exact (PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ (PEq.unit_unique _ _))

/-- **The two normalisation lemmas**, by mutual induction on the rank. -/
theorem sumProd_normalisable (n : ℕ) : SumNormalisable n ∧ ProdNormalisable n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    constructor
    · intro A B₁ B₂ f hf hfn
      rcases hf.spine with ⟨f', hatom, hle, heq⟩ | ⟨C, f₁, f₂, hf₁, hatom₂, hrk, heq⟩
      · exact NormSum.of_eq heq (hatom.sumCases.mono hle)
      · have hlt : rank f - 1 < n := by omega
        exact NormSum.of_eq heq
          (NormSum.mono hrk
            (IsDropAtom.sumStep (IH _ hlt).1 (IH _ hlt).2 hatom₂ f₁ hf₁ (by omega)))
    · intro A B₁ B₂ f hf hfn
      rcases hf.spine with ⟨f', hatom, hle, heq⟩ | ⟨C, f₁, f₂, hf₁, hatom₂, hrk, heq⟩
      · exact NormProd.of_eq heq (hatom.prodCases.mono hle)
      · have hlt : rank f - 1 < n := by omega
        exact NormProd.of_eq heq
          (NormProd.mono hrk
            (IsDropAtom.prodStep (IH _ hlt).1 (IH _ hlt).2 hatom₂ f₁ hf₁ (by omega)))

/-! ### The two normalisation lemmas -/

/-- **Lemma (Sum normalisation), tree version** (appendix, corrected).  Every drop with a
co-product codomain is provably equal to a lift followed by an `n`-ary co-pairing of drops in
normal form, all of whose components have at most the rank of the original drop.

This is the form in which the induction of the appendix produces the normal form; it is
turned into the right-associated co-pairing of the paper by
`Lax149335Proofs.IsNormalSumTree.toVec`, which gives `Lax149335Proofs.drops_with_sum_codomain`. -/
theorem drops_with_sum_codomain_tree {A B₁ B₂ : Ty} (f : Term A (B₁ ⊕' B₂)) (hf : IsDrop f) :
    ∃ (D : Ty) (alpha : Term A D) (g : Term D (B₁ ⊕' B₂)),
      IsLift alpha ∧ IsDrop g ∧ IsNormalSumTree (rank f) g ∧ f ≡ₜ (alpha ⨟ g) := by
  obtain ⟨D, alpha, g, halpha, hg, he⟩ := (sumProd_normalisable (rank f)).1 f hf le_rfl
  exact ⟨D, alpha, g, halpha, hg.isDrop, hg, he⟩

/-- **Lemma (Product normalisation)** (appendix).  Every drop with a product codomain is
provably equal to a lift followed by an `n`-ary co-pairing of products of drops, all of whose
components have at most the rank of the original drop.

(Restated, with the same proof, as `Lax149335Proofs.drops_with_prod_codomain` in
`Lax149335Proofs.Appendix.Drops.DropNormalisation`.) -/
theorem drops_with_prod_codomain_of_rank {A B₁ B₂ : Ty} (f : Term A (B₁ ⊗ B₂))
    (hf : IsDrop f) :
    ∃ (D : Ty) (alpha : Term A D) (g : Term D (B₁ ⊗ B₂)),
      IsLift alpha ∧ IsDrop g ∧ IsNormalProdLe (rank f) g ∧ f ≡ₜ (alpha ⨟ g) := by
  obtain ⟨D, alpha, g, halpha, hg, he⟩ := (sumProd_normalisable (rank f)).2 f hf le_rfl
  exact ⟨D, alpha, g, halpha, hg.isDrop, hg, he⟩

/-! ### From case trees to the normal form of the paper

The induction produces the normal form with sum codomain as a case tree, i.e. an arbitrarily
nested co-pairing whose leaves are of the three shapes `g ; Left`, `g ; Right` and
`g₁ + g₂`.  The normal form of the paper is a co-pairing of an arbitrary number of components
`gᵢ ; ρ`, with `ρ` a co-projection, associated to the right.  The two are related by a lift:
a leaf `g₁ + g₂` is the two-component co-pairing `⟨g₁ ; Left, g₂ ; Right⟩`, and a co-pairing
is re-associated to the right by the prime lift `sumAssocR`. -/

namespace Term

/-- A co-product of two terms is the co-pairing of its two components followed by the
co-projections. -/
theorem sumF_as_either {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) :
    sumF f g ≡ₜ either (f ⨟ inl B₁ B₂) (g ⨟ inr B₁ B₂) := by
  refine either_ext _ _ ?_ ?_
  · exact (PEq.nat_inl f g).trans (PEq.symm (inl_either _ _))
  · exact (PEq.nat_inr f g).trans (PEq.symm (inr_either _ _))

/-- The left component of `sumAssocR`. -/
theorem inl_sumAssocR (A B C : Ty) :
    (inl (A ⊕' B) C ⨟ sumAssocR A B C) ≡ₜ
      either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) :=
  inl_either _ _

/-- The right component of `sumAssocR`. -/
theorem inr_sumAssocR (A B C : Ty) :
    (inr (A ⊕' B) C ⨟ sumAssocR A B C) ≡ₜ (inr B C ⨟ inr A (B ⊕' C)) :=
  inr_either _ _

/-- Re-associating a co-pairing to the right. -/
theorem either_assocR {A B C Z : Ty} (f : Term A Z) (g : Term B Z) (h : Term C Z) :
    either (either f g) h ≡ₜ (sumAssocR A B C ⨟ either f (either g h)) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl (A ⊕' B) C ⨟ either (either f g) h) ≡ₜ either f g := inl_either _ _
      _ ≡ₜ either (inl A (B ⊕' C) ⨟ either f (either g h))
            ((inl B C ⨟ inr A (B ⊕' C)) ⨟ either f (either g h)) :=
          either_congr (PEq.symm (inl_either _ _))
            (((PEq.comp_assoc _ _ _).trans
              (PEq.compR _ (inr_either _ _))).trans (inl_either _ _)).symm
      _ ≡ₜ (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) ⨟
            either f (either g h)) := PEq.symm (either_comp _ _ _)
      _ ≡ₜ ((inl (A ⊕' B) C ⨟ sumAssocR A B C) ⨟ either f (either g h)) :=
          PEq.compL _ (PEq.symm (inl_sumAssocR A B C))
      _ ≡ₜ (inl (A ⊕' B) C ⨟ (sumAssocR A B C ⨟ either f (either g h))) :=
          PEq.comp_assoc _ _ _
  · calc (inr (A ⊕' B) C ⨟ either (either f g) h) ≡ₜ h := inr_either _ _
      _ ≡ₜ (inr B C ⨟ either g h) := PEq.symm (inr_either _ _)
      _ ≡ₜ (inr B C ⨟ (inr A (B ⊕' C) ⨟ either f (either g h))) :=
          PEq.compR _ (PEq.symm (inr_either _ _))
      _ ≡ₜ ((inr B C ⨟ inr A (B ⊕' C)) ⨟ either f (either g h)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inr (A ⊕' B) C ⨟ sumAssocR A B C) ⨟ either f (either g h)) :=
          PEq.compL _ (PEq.symm (inr_sumAssocR A B C))
      _ ≡ₜ (inr (A ⊕' B) C ⨟ (sumAssocR A B C ⨟ either f (either g h))) :=
          PEq.comp_assoc _ _ _

/-- Re-associating a co-pairing to the left. -/
theorem either_assocL {A B C Z : Ty} (f : Term A Z) (g : Term B Z) (h : Term C Z) :
    either f (either g h) ≡ₜ (sumAssocL A B C ⨟ either (either f g) h) := by
  calc either f (either g h)
      ≡ₜ (Term.id (A ⊕' (B ⊕' C)) ⨟ either f (either g h)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((sumAssocL A B C ⨟ sumAssocR A B C) ⨟ either f (either g h)) :=
        PEq.compL _ (PEq.symm (sumAssocL_sumAssocR A B C))
    _ ≡ₜ (sumAssocL A B C ⨟ (sumAssocR A B C ⨟ either f (either g h))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (sumAssocL A B C ⨟ either (either f g) h) :=
        PEq.compR _ (PEq.symm (either_assocR f g h))

/-- Pulling a term out of the right component of a co-pairing. -/
theorem either_pushR {D₁ D₂ D₂' Z : Ty} (u : Term D₁ Z) (c : Term D₂ D₂') (v : Term D₂' Z) :
    either u (c ⨟ v) ≡ₜ (sumF (Term.id D₁) c ⨟ either u v) :=
  PEq.symm ((sumF_either (Term.id D₁) c u v).trans
    (either_congr (PEq.id_comp u) (PEq.refl _)))

end Term

/-- **Concatenating two normal forms.**  The co-pairing of two normal forms is, up to a lift,
again a normal form: the components of the second one are appended to those of the first. -/
theorem IsNormalSumVec.append {r : ℕ} {B₁ B₂ : Ty} :
    {A₁ : Ty} → {N₁ : Term A₁ (B₁ ⊕' B₂)} → IsNormalSumVec r N₁ →
    {A₂ : Ty} → {N₂ : Term A₂ (B₁ ⊕' B₂)} → IsNormalSumVec r N₂ →
    ∃ (D : Ty) (beta : Term (A₁ ⊕' A₂) D) (N : Term D (B₁ ⊕' B₂)),
      IsLift beta ∧ IsNormalSumVec r N ∧ Term.either N₁ N₂ ≡ₜ (beta ⨟ N)
  | _, _, .single hl, _, N₂, h₂ =>
      ⟨_, Term.id _, Term.either _ N₂, IsLift.id _, .cons hl h₂, PEq.symm (PEq.id_comp _)⟩
  | _, _, @IsNormalSumVec.cons _ A' A'' _ _ l M hl hM, A₂, N₂, h₂ => by
      obtain ⟨D, beta, N, hb, hN, he⟩ := hM.append h₂
      refine ⟨A' ⊕' D, Term.sumAssocR A' A'' A₂ ⨟ Term.sumF (Term.id A') beta,
        Term.either l N, IsLift.comp (IsLift.sumAssocR _ _ _)
          (IsLift.sumF (IsLift.id _) hb), .cons hl hN, ?_⟩
      calc Term.either (Term.either l M) N₂
          ≡ₜ (Term.sumAssocR A' A'' A₂ ⨟ Term.either l (Term.either M N₂)) :=
            Term.either_assocR _ _ _
        _ ≡ₜ (Term.sumAssocR A' A'' A₂ ⨟ Term.either l (beta ⨟ N)) :=
            PEq.compR _ (either_congr (PEq.refl _) he)
        _ ≡ₜ (Term.sumAssocR A' A'' A₂ ⨟ (Term.sumF (Term.id A') beta ⨟ Term.either l N)) :=
            PEq.compR _ (Term.either_pushR _ _ _)
        _ ≡ₜ ((Term.sumAssocR A' A'' A₂ ⨟ Term.sumF (Term.id A') beta) ⨟ Term.either l N) :=
            PEq.symm (PEq.comp_assoc _ _ _)

/-- **Flattening a case tree.**  A case tree in normal form is, up to a lift, a normal form
in the sense of the paper: a right-associated co-pairing of components `gᵢ ; ρ`. -/
theorem IsNormalSumTree.toVec {r : ℕ} : {A B₁ B₂ : Ty} → {N : Term A (B₁ ⊕' B₂)} →
    IsNormalSumTree r N →
    ∃ (D : Ty) (beta : Term A D) (N' : Term D (B₁ ⊕' B₂)),
      IsLift beta ∧ IsNormalSumVec r N' ∧ N ≡ₜ (beta ⨟ N')
  | _, _, _, _, .inl hg hr =>
      ⟨_, Term.id _, _, IsLift.id _, .single (.inl hg hr), PEq.symm (PEq.id_comp _)⟩
  | _, _, _, _, .inr hg hr =>
      ⟨_, Term.id _, _, IsLift.id _, .single (.inr hg hr), PEq.symm (PEq.id_comp _)⟩
  | _, _, _, _, @IsNormalSumTree.sumF _ _ _ _ _ g₁ g₂ hg₁ hg₂ hr₁ hr₂ =>
      ⟨_, Term.id _, Term.either (g₁ ⨟ Term.inl _ _) (g₂ ⨟ Term.inr _ _), IsLift.id _,
        .cons (.inl hg₁ hr₁) (.single (.inr hg₂ hr₂)),
        (Term.sumF_as_either g₁ g₂).trans (PEq.symm (PEq.id_comp _))⟩
  | _, _, _, _, @IsNormalSumTree.either _ _ _ _ _ f₁ f₂ t₁ t₂ => by
      obtain ⟨D₁, b₁, N₁, hb₁, hN₁, he₁⟩ := t₁.toVec
      obtain ⟨D₂, b₂, N₂, hb₂, hN₂, he₂⟩ := t₂.toVec
      obtain ⟨D, c, N, hc, hN, he⟩ := hN₁.append hN₂
      refine ⟨D, Term.sumF b₁ b₂ ⨟ c, N, IsLift.comp (IsLift.sumF hb₁ hb₂) hc, hN, ?_⟩
      calc Term.either f₁ f₂ ≡ₜ Term.either (b₁ ⨟ N₁) (b₂ ⨟ N₂) := either_congr he₁ he₂
        _ ≡ₜ (Term.sumF b₁ b₂ ⨟ Term.either N₁ N₂) := PEq.symm (sumF_either _ _ _ _)
        _ ≡ₜ (Term.sumF b₁ b₂ ⨟ (c ⨟ N)) := PEq.compR _ he
        _ ≡ₜ ((Term.sumF b₁ b₂ ⨟ c) ⨟ N) := PEq.symm (PEq.comp_assoc _ _ _)

/-- **Lemma (Sum normalisation)** (appendix).  Every drop `f` with a co-product codomain is
provably equal to a lift followed by a co-pairing `⟨f₁, …, fₙ⟩`, of arbitrary arity and
associated to the right, in which every component `fᵢ` is of the form `gᵢ ; Left` or
`gᵢ ; Right` for a drop `gᵢ` of rank at most the rank of `f`. -/
theorem drops_with_sum_codomain {A B₁ B₂ : Ty} (f : Term A (B₁ ⊕' B₂)) (hf : IsDrop f) :
    ∃ (D : Ty) (alpha : Term A D) (N : Term D (B₁ ⊕' B₂)),
      IsLift alpha ∧ IsDrop N ∧ IsNormalSumVec (rank f) N ∧ f ≡ₜ (alpha ⨟ N) := by
  obtain ⟨D, alpha, T, halpha, hT, he⟩ := (sumProd_normalisable (rank f)).1 f hf le_rfl
  obtain ⟨D', beta, N, hbeta, hN, he'⟩ := hT.toVec
  exact ⟨D', alpha ⨟ beta, N, IsLift.comp halpha hbeta, hN.isDrop, hN,
    (he.trans (PEq.compR _ he')).trans (PEq.symm (PEq.comp_assoc _ _ _))⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
