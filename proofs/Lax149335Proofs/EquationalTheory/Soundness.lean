import Lax149335Proofs.Terms.Semantics
import Lax149335Proofs.EquationalTheory.Axioms
import Lax149335Proofs.SimpleCompleteness.BundleDecomposition
import Lax149335Proofs.EquationalTheory.WindowSemantics

/-!
# Soundness of the equational theory

Every axiom of Section 4 is valid for the denotational semantics, and the rules of
equational reasoning preserve validity; hence provable equality implies denotational
equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- The semantic content of Axiom 15: `shiftR` does not change the content of the list. -/
theorem shiftR_content_den {α β : Type} (l : List (α × β)) (a : α) :
    Sum.inl (shiftRDen l a).1 ::
        ((shiftRDen l a).2.map (fun p : β × α => [Sum.inr p.1, Sum.inl p.2])).flatten =
      (l.map (fun p : α × β => [Sum.inl p.1, Sum.inr p.2])).flatten ++ [Sum.inl a] := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a₁, b₁⟩ := p
    simp only [shiftRDen_cons, List.map_cons, List.flatten_cons, List.cons_append,
      List.nil_append]
    exact congrArg _ (congrArg _ ih)

/-- **Soundness.**  If `f ≡ g` is provable from Axioms 1-16, then `f` and `g` have the same
denotation. -/
theorem PEq.sound {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) : f.den = g.den := by
  induction h with
  | refl f => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr_comp _ _ ih₁ ih₂ => funext x; simp [ih₁, ih₂]
  | congr_prodF _ _ ih₁ ih₂ => funext x; simp [ih₁, ih₂]
  | congr_sumF _ _ ih₁ ih₂ => funext x; cases x <;> simp [ih₁, ih₂]
  | congr_listF _ ih => funext x; simp [ih]
  | list_comp f g => funext x; simp [List.map_map, Function.comp_def]
  | sum_comp f₁ f₂ g₁ g₂ => funext x; cases x <;> simp
  | nat_codiag f => funext x; cases x <;> simp
  | nat_cons f => funext x; rcases x with ⟨⟩ | ⟨a, l⟩ <;> simp
  | nat_uncons f => funext x; cases x <;> simp
  | nat_snoc f => funext x; rcases x with ⟨⟩ | ⟨l, a⟩ <;> simp [snocDen]
  | nat_unsnoc f => funext x; have hX := unsnocDen_map f.den x; simp at hX ⊢; exact hX
  | nat_distL f g h => funext x; rcases x with ⟨a | b, c⟩ <;> simp
  | nat_distR f g h => funext x; rcases x with ⟨a, b | c⟩ <;> simp
  | nat_block f g =>
    funext x
    have hX := blockDen_map f.den g.den x; simp [Sum.map] at hX ⊢; exact hX
  | nat_shiftR f g =>
    funext x
    obtain ⟨l, a⟩ := x
    have hX := shiftRDen_map f.den g.den l a; simp at hX ⊢; exact hX
  | nat_shiftL f g =>
    funext x
    obtain ⟨a, l⟩ := x
    have hX := shiftLDen_map f.den g.den a l; simp at hX ⊢; exact hX
  | distL_undistL A B C => funext x; rcases x with ⟨a | b, c⟩ <;> rfl
  | undistL_distL A B C => funext x; rcases x with ⟨a, c⟩ | ⟨b, c⟩ <;> rfl
  | distR_undistR A B C => funext x; rcases x with ⟨a, b | c⟩ <;> rfl
  | undistR_distR A B C => funext x; rcases x with ⟨a, b⟩ | ⟨a, c⟩ <;> rfl
  | cons_uncons A => funext x; rcases x with ⟨⟩ | ⟨a, l⟩ <;> rfl
  | uncons_cons A => funext x; cases x <;> rfl
  | block_unblock A B =>
    funext x; rw [den_comp, den_block, den_unblock, unblockDen_blockDen, den_id]
  | unblock_block A B =>
    funext x; rw [den_comp, den_unblock, den_block, blockDen_unblockDen, den_id]
  | shiftL_shiftR A B =>
    funext x
    obtain ⟨a, l⟩ := x
    have hX := shiftRDen_shiftLDen a l; simp at hX ⊢; exact hX
  | shiftR_shiftL A B =>
    funext x
    obtain ⟨l, a⟩ := x
    have hX := shiftLDen_shiftRDen l a; simp at hX ⊢; exact hX
  | pref_unpref A G =>
    funext x
    letI := G
    rw [den_comp, den_pref, den_unpref]
    exact unprefDen_prefixMul 1 x
  | unpref_pref A G =>
    funext x
    letI := G
    rw [den_comp, den_unpref, den_pref]
    exact prefixMul_unprefDen 1 x
  | sum_inl_inr_codiag A B => funext x; cases x <;> simp
  | binconcat_assoc A =>
    funext x
    obtain ⟨⟨l₁, l₂⟩, l₃⟩ := x
    simp [List.append_assoc]
  | binconcat_concat A =>
    funext x
    obtain ⟨l₁, l₂⟩ := x
    simp only [den_comp, den_binconcat, den_prodF, den_concat]
    exact List.flatten_append
  | concat_concat A =>
    funext x
    show ((x.map List.flatten).flatten : List ⟦A⟧) = x.flatten.flatten
    exact (List.flatten_flatten).symm
  | pure_concat A => funext x; exact List.append_nil x
  | listF_pure_concat A => funext x; exact flatten_map_pure x
  | prepend_def A =>
    funext x
    obtain ⟨a, l⟩ := x
    simp only [den_comp, den_prodF, den_pureT, den_id, den_binconcat, den_prepend]
    rfl
  | nil_map_concat A =>
    funext x
    show ((x.map (fun _ => ([] : List ⟦A⟧))).flatten) = []
    exact flatten_map_nil x
  | shiftR_content A B =>
    funext x
    obtain ⟨l, a⟩ := x
    simp only [TyF2.concatMap, den_comp, den_shiftR, den_fdot, den_homT, den_pureT,
      List.append_eq]
    have e1 : ⟦(inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))⟧ₜ
        = fun q : ⟦B⟧ × ⟦A⟧ => [Sum.inl q.2].cons (Sum.inr q.1) := rfl
    have e2 : ⟦(inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))⟧ₜ
        = fun p : ⟦A⟧ × ⟦B⟧ => [Sum.inr p.2].cons (Sum.inl p.1) := rfl
    rw [e1, e2]
    exact shiftR_content_den l a
  | window =>
    -- Axiom 16: the bundle term of Definition H.5 splits a list into bundles of two
    -- consecutive entries, and concatenating the bundles gives the list back
    exact Term.bundle_concatMap_den ((Ty.finAlph 1)⋆) (nilT (Ty.finAlph 1))
  | _ =>
    funext x
    first
      | rfl
      | simp

end Lax149335Proofs

bridge_export Lax149335Proofs
