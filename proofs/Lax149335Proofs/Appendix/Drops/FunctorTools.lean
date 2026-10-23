import Lax149335Proofs.Appendix.Drops.DropRank

/-!
# Functorial tools for multivariate list-polynomial functors

The equational facts about the functorial action `TyFn.mapN` of a multivariate
list-polynomial functor and about its concatenation combinator `TyFn.listConcatMap` that the
proofs of the exchange lemmas (Lemma 7.5 and the group exchange lemma) need:

* functoriality of `TyFn.mapN`, and its compatibility with lifts and drops;
* the concatenation combinator `genconc` is provably equal to a drop, and is natural.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Functoriality of the multivariate functorial action -/

/-- The functorial action of a multivariate functor preserves composition. -/
theorem TyFn.mapN_comp : (F : TyFn) → {As Bs Cs : ℕ → Ty} →
    (f : (i : ℕ) → Term (As i) (Bs i)) → (g : (i : ℕ) → Term (Bs i) (Cs i)) →
    (F.mapN f ⨟ F.mapN g) ≡ₜ F.mapN (fun i => f i ⨟ g i)
  | .param _, _, _, _, _, _ => PEq.refl _
  | .unit, _, _, _, _, _ => PEq.id_comp _
  | .prod F G, _, _, _, f, g =>
      (PEq.prod_comp _ _ _ _).trans
        (PEq.congr_prodF (F.mapN_comp f g) (G.mapN_comp f g))
  | .sum F G, _, _, _, f, g =>
      (PEq.sum_comp _ _ _ _).trans
        (PEq.congr_sumF (F.mapN_comp f g) (G.mapN_comp f g))
  | .list F, _, _, _, f, g =>
      (PEq.list_comp _ _).trans (PEq.congr_listF (F.mapN_comp f g))

/-- The functorial action of a multivariate functor on a family of drops is a drop. -/
theorem TyFn.isDrop_mapN : (F : TyFn) → {As Bs : ℕ → Ty} →
    {f : (i : ℕ) → Term (As i) (Bs i)} → (∀ i, IsDrop (f i)) → IsDrop (F.mapN f)
  | .param i, _, _, _, h => h i
  | .unit, _, _, _, _ => IsDrop.id _
  | .prod F G, _, _, _, h => IsDrop.prodF (F.isDrop_mapN h) (G.isDrop_mapN h)
  | .sum F G, _, _, _, h => IsDrop.sumF (F.isDrop_mapN h) (G.isDrop_mapN h)
  | .list F, _, _, _, h => IsDrop.listF (F.isDrop_mapN h)

/-- The functorial action of a multivariate functor on a family of lifts is a lift. -/
theorem TyFn.isLift_mapN : (F : TyFn) → {As Bs : ℕ → Ty} →
    {f : (i : ℕ) → Term (As i) (Bs i)} → (∀ i, IsLift (f i)) → IsLift (F.mapN f)
  | .param i, _, _, _, h => h i
  | .unit, _, _, _, _ => IsLift.id _
  | .prod F G, _, _, _, h => IsLift.prodF (F.isLift_mapN h) (G.isLift_mapN h)
  | .sum F G, _, _, _, h => IsLift.sumF (F.isLift_mapN h) (G.isLift_mapN h)
  | .list F, _, _, _, h => IsLift.listF (F.isLift_mapN h)

/-- Two families of terms that agree on the parameters that a multivariate functor uses have
the same functorial action. -/
theorem TyFn.mapN_congr : (F : TyFn) → {As Bs : ℕ → Ty} →
    {f g : (i : ℕ) → Term (As i) (Bs i)} → (∀ i, F.usesParam i → f i ≡ₜ g i) →
    F.mapN f ≡ₜ F.mapN g
  | .param i, _, _, _, _, h => h i rfl
  | .unit, _, _, _, _, _ => PEq.refl _
  | .prod F G, _, _, _, _, h =>
      PEq.congr_prodF (F.mapN_congr fun i hi => h i (Or.inl hi))
        (G.mapN_congr fun i hi => h i (Or.inr hi))
  | .sum F G, _, _, _, _, h =>
      PEq.congr_sumF (F.mapN_congr fun i hi => h i (Or.inl hi))
        (G.mapN_congr fun i hi => h i (Or.inr hi))
  | .list F, _, _, _, _, h => PEq.congr_listF (F.mapN_congr h)

/-! ### The concatenation combinator of a multivariate functor -/

/-- The concatenation combinator `genconc` is provably equal to a drop. -/
theorem TyFn.isEqDrop_listConcatMap : (F : TyFn) → (B : Ty) →
    IsEqDrop (F.listConcatMap B)
  | .param _, B => IsEqDrop.of_isDrop (IsDrop.id B⋆)
  | .unit, B => isEqDrop_nilT B
  | .prod F G, B =>
      IsEqDrop.comp (IsEqDrop.prodF (F.isEqDrop_listConcatMap B) (G.isEqDrop_listConcatMap B))
        (IsEqDrop.of_isDrop (IsDrop.binconcat B))
  | .sum F G, B =>
      IsEqDrop.either (F.isEqDrop_listConcatMap B) (G.isEqDrop_listConcatMap B)
  | .list F, B =>
      IsEqDrop.comp (IsEqDrop.listF (F.isEqDrop_listConcatMap B))
        (IsEqDrop.of_isDrop (IsDrop.concat B))

/-- The concatenation combinator `genconc` is natural: mapping a term over the resulting
list is the same as mapping it over each of the lists that are concatenated. -/
theorem TyFn.listConcatMap_natural : (F : TyFn) → {B B' : Ty} → (g : Term B B') →
    (F.listConcatMap B ⨟ listF g) ≡ₜ
      (F.mapN (fun _ => listF g) ⨟ F.listConcatMap B')
  | .param _, _, _, g => (PEq.id_comp _).trans (PEq.symm (PEq.comp_id _))
  | .unit, B, B', g => (nilT_natural g).trans (PEq.symm (PEq.id_comp _))
  | .prod F G, B, B', g => by
      calc ((prodF (F.listConcatMap B) (G.listConcatMap B) ⨟ binconcat B) ⨟ listF g)
          ≡ₜ (prodF (F.listConcatMap B ⨟ listF g) (G.listConcatMap B ⨟ listF g) ⨟
              binconcat B') := fdot_natural _ _ g
        _ ≡ₜ (prodF (F.mapN (fun _ => listF g) ⨟ F.listConcatMap B')
              (G.mapN (fun _ => listF g) ⨟ G.listConcatMap B') ⨟ binconcat B') :=
            PEq.compL _ (PEq.congr_prodF (F.listConcatMap_natural g)
              (G.listConcatMap_natural g))
        _ ≡ₜ ((prodF (F.mapN (fun _ => listF g)) (G.mapN (fun _ => listF g)) ⨟
              prodF (F.listConcatMap B') (G.listConcatMap B')) ⨟ binconcat B') :=
            PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
        _ ≡ₜ (prodF (F.mapN (fun _ => listF g)) (G.mapN (fun _ => listF g)) ⨟
              (prodF (F.listConcatMap B') (G.listConcatMap B') ⨟ binconcat B')) :=
            PEq.comp_assoc _ _ _
  | .sum F G, B, B', g => by
      calc (either (F.listConcatMap B) (G.listConcatMap B) ⨟ listF g)
          ≡ₜ either (F.listConcatMap B ⨟ listF g) (G.listConcatMap B ⨟ listF g) :=
            either_comp _ _ _
        _ ≡ₜ either (F.mapN (fun _ => listF g) ⨟ F.listConcatMap B')
              (G.mapN (fun _ => listF g) ⨟ G.listConcatMap B') :=
            either_congr (F.listConcatMap_natural g) (G.listConcatMap_natural g)
        _ ≡ₜ (sumF (F.mapN (fun _ => listF g)) (G.mapN (fun _ => listF g)) ⨟
              either (F.listConcatMap B') (G.listConcatMap B')) :=
            PEq.symm (sumF_either _ _ _ _)
  | .list F, B, B', g => by
      calc ((listF (F.listConcatMap B) ⨟ concat B) ⨟ listF g)
          ≡ₜ (listF (F.listConcatMap B) ⨟ (concat B ⨟ listF g)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (listF (F.listConcatMap B) ⨟ (listF (listF g) ⨟ concat B')) :=
            PEq.compR _ (PEq.symm (PEq.nat_concat g))
        _ ≡ₜ ((listF (F.listConcatMap B) ⨟ listF (listF g)) ⨟ concat B') :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (listF (F.listConcatMap B ⨟ listF g) ⨟ concat B') :=
            PEq.compL _ (PEq.list_comp _ _)
        _ ≡ₜ (listF (F.mapN (fun _ => listF g) ⨟ F.listConcatMap B') ⨟ concat B') :=
            PEq.compL _ (PEq.congr_listF (F.listConcatMap_natural g))
        _ ≡ₜ ((listF (F.mapN (fun _ => listF g)) ⨟ listF (F.listConcatMap B')) ⨟ concat B') :=
            PEq.compL _ (PEq.symm (PEq.list_comp _ _))
        _ ≡ₜ (listF (F.mapN (fun _ => listF g)) ⨟ (listF (F.listConcatMap B') ⨟ concat B')) :=
            PEq.comp_assoc _ _ _

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
