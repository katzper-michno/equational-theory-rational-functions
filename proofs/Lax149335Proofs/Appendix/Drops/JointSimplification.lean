import Lax149335Proofs.Appendix.Drops.DropSimplification
import Mathlib.Tactic.Set

/-!
# Joint simplification of two drops (appendix, *Proof of joint simplification*)

This file proves the appendix lemma behind Lemma 7.3: given two drops `f, g : A ⇒ B*` into
lists over a finite alphabet, there is a *single* lift after which both are simple.

The drop simplification lemma (`Lax149335Proofs.drop_simplification`) already gives, for one drop, a
lift `δ : A ⊸ C` after which the drop becomes a shape with values in the leaves.  The
difficulty of the joint statement is that simplifying the second drop introduces a further
lift `δ₂ : C ⊸ D`, and one has to know that the first drop stays simple on `D`.  This is the
content of `Lax149335Proofs.shape_transport_of_lift` below: a shape with values in the leaves can be
pushed along any lift.  The reason is that such a shape is a concatenation map with the
letters read through a fixed alphabet map, and every lift commutes with concatenation maps.

To keep the bookkeeping structural, the shapes are described by *leaf assignments*: for a
type `X` built from `1` with products, co-products and lists, a `Lax149335Proofs.LeafVal B X` picks
a value of type `B*` for every leaf of `X`, and `Lax149335Proofs.shapeOf` turns such an assignment
into the term `X ⇒ B*` that concatenates the chosen values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Shapes with values in the leaves, described by leaf assignments -/

/-- An assignment of a value of type `B*` to every leaf of the type `X`. -/
def LeafVal (B : Ty) : Ty → Type
  | .unit => Value B⋆
  | .prod X Y => LeafVal B X × LeafVal B Y
  | .sum X Y => LeafVal B X × LeafVal B Y
  | .list X => LeafVal B X

/-- The term `X ⇒ B*` determined by an assignment of values to the leaves of `X`: the values
of all the leaves reachable in the input are concatenated, from left to right. -/
def shapeOf (B : Ty) : (X : Ty) → LeafVal B X → Term X B⋆
  | .unit, v => v
  | .prod X Y, lv => shapeOf B X lv.1 ⊙ shapeOf B Y lv.2
  | .sum X Y, lv => Term.either (shapeOf B X lv.1) (shapeOf B Y lv.2)
  | .list X, lv => Term.homT (shapeOf B X lv)

@[simp] theorem shapeOf_unit (B : Ty) (v : Value B⋆) : shapeOf B .unit v = v := rfl

@[simp] theorem shapeOf_prod (B X Y : Ty) (lv : LeafVal B (X ⊗ Y)) :
    shapeOf B (X ⊗ Y) lv = (shapeOf B X lv.1 ⊙ shapeOf B Y lv.2) := rfl

@[simp] theorem shapeOf_sum (B X Y : Ty) (lv : LeafVal B (X ⊕' Y)) :
    shapeOf B (X ⊕' Y) lv = Term.either (shapeOf B X lv.1) (shapeOf B Y lv.2) := rfl

@[simp] theorem shapeOf_list (B X : Ty) (lv : LeafVal B X⋆) :
    shapeOf B X⋆ lv = Term.homT (shapeOf B X lv) := rfl

/-- Every shape with values in the leaves is a simple rational term. -/
theorem shapeOf_isSimple (B : Ty) : (X : Ty) → (lv : LeafVal B X) →
    ∃ s : Term X B⋆, IsSimple B s ∧ shapeOf B X lv ≡ₜ s
  | .unit, v => ⟨Term.dotL v (nilT B), IsSimple.dotL v IsSimple.nil, by
      -- `v ≡ v · []`
      have h : Term.dotL v (nilT B) ≡ₜ (Term.unitL Ty.unit ⨟ (v ⊙ nilT B)) :=
        PEq.comp_assoc _ _ _
      refine PEq.symm (h.trans ?_)
      calc (Term.unitL Ty.unit ⨟ (v ⊙ nilT B))
          ≡ₜ (Term.unitL Ty.unit ⨟ (Term.fst Ty.unit Ty.unit ⨟ v)) :=
            PEq.compR _ (Term.fdot_nil_right v)
        _ ≡ₜ ((Term.unitL Ty.unit ⨟ Term.fst Ty.unit Ty.unit) ⨟ v) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id Ty.unit ⨟ v) :=
            PEq.compL _ (PEq.unit_unique _ (Term.id Ty.unit))
        _ ≡ₜ v := PEq.id_comp _⟩
  | .prod X Y, lv => by
      obtain ⟨s₁, hs₁, he₁⟩ := shapeOf_isSimple B X lv.1
      obtain ⟨s₂, hs₂, he₂⟩ := shapeOf_isSimple B Y lv.2
      exact ⟨s₁ ⊙ s₂, IsSimple.fdot hs₁ hs₂, Term.fdot_congr he₁ he₂⟩
  | .sum X Y, lv => by
      obtain ⟨s₁, hs₁, he₁⟩ := shapeOf_isSimple B X lv.1
      obtain ⟨s₂, hs₂, he₂⟩ := shapeOf_isSimple B Y lv.2
      exact ⟨Term.either s₁ s₂, IsSimple.either hs₁ hs₂, Term.either_congr he₁ he₂⟩
  | .list X, lv => by
      obtain ⟨s, hs, he⟩ := shapeOf_isSimple B X lv
      exact ⟨Term.homT s, IsSimple.hom hs, Term.homT_congr he⟩

/-- The normal shapes produced by the drop simplification lemma are shapes with values in the
leaves. -/
theorem exists_leafVal_normalListShape (B : Ty) : (F : TyFn) → (vs : (i : ℕ) → Value B⋆) →
    ∃ lv : LeafVal B (F.app (fun _ => Ty.unit)),
      normalListShape B F (fun _ => Ty.unit) vs ≡ₜ shapeOf B (F.app (fun _ => Ty.unit)) lv
  | .param i, vs => ⟨vs i, Term.normalListShape_param _ _ _ _⟩
  | .unit, _ => ⟨nilT B, Term.normalListShape_unit _ _ _⟩
  | .prod F G, vs => by
      obtain ⟨lv₁, h₁⟩ := exists_leafVal_normalListShape B F vs
      obtain ⟨lv₂, h₂⟩ := exists_leafVal_normalListShape B G vs
      exact ⟨(lv₁, lv₂), (Term.normalListShape_prod _ _ _ _ _).trans (Term.fdot_congr h₁ h₂)⟩
  | .sum F G, vs => by
      obtain ⟨lv₁, h₁⟩ := exists_leafVal_normalListShape B F vs
      obtain ⟨lv₂, h₂⟩ := exists_leafVal_normalListShape B G vs
      exact ⟨(lv₁, lv₂),
        (Term.normalListShape_sum _ _ _ _ _).trans (Term.either_congr h₁ h₂)⟩
  | .list F, vs => by
      obtain ⟨lv, h⟩ := exists_leafVal_normalListShape B F vs
      exact ⟨lv, (Term.normalListShape_list _ _ _ _).trans (Term.homT_congr h)⟩

/-! ### Plugging two terms into the leaves of a two-parameter functor -/

namespace Term

/-- Plugging two terms with list outputs into the two parameters of a two-parameter
list-polynomial functor, and concatenating the results. -/
def TyF2.plug {B : Ty} : (F : TyF2) → {S T : Ty} → Term S B⋆ → Term T B⋆ →
    Term (F.app S T) B⋆
  | .p1, _, _, sa, _ => sa
  | .p2, _, _, _, sb => sb
  | .unit, _, _, _, _ => nilT B
  | .prod F G, _, _, sa, sb => (TyF2.plug F sa sb) ⊙ (TyF2.plug G sa sb)
  | .sum F G, _, _, sa, sb => Term.either (TyF2.plug F sa sb) (TyF2.plug G sa sb)
  | .list F, _, _, sa, sb => Term.homT (TyF2.plug F sa sb)

bridge_export Lax149335Proofs

/-- Plugging respects provable equality. -/
theorem TyF2.plug_congr {B : Ty} : (F : TyF2) → {S T : Ty} → {sa sa' : Term S B⋆} →
    {sb sb' : Term T B⋆} → sa ≡ₜ sa' → sb ≡ₜ sb' → F.plug sa sb ≡ₜ F.plug sa' sb'
  | .p1, _, _, _, _, _, _, ha, _ => ha
  | .p2, _, _, _, _, _, _, _, hb => hb
  | .unit, _, _, _, _, _, _, _, _ => PEq.refl _
  | .prod F G, _, _, _, _, _, _, ha, hb =>
      Term.fdot_congr (TyF2.plug_congr F ha hb) (TyF2.plug_congr G ha hb)
  | .sum F G, _, _, _, _, _, _, ha, hb =>
      Term.either_congr (TyF2.plug_congr F ha hb) (TyF2.plug_congr G ha hb)
  | .list F, _, _, _, _, _, _, ha, hb => Term.homT_congr (TyF2.plug_congr F ha hb)

/-- The concatenation map of a two-parameter functor, followed by a homomorphism out of the
co-product of the two parameters, is the same as plugging the two components of the
homomorphism into the parameters. -/
theorem TyF2.concatMap_comp_homT {B : Ty} : (F : TyF2) → {S T : Ty} → (m : Term (S ⊕' T) B⋆) →
    (TyF2.concatMap F S T ⨟ Term.homT m) ≡ₜ
      F.plug (Term.inl S T ⨟ m) (Term.inr S T ⨟ m)
  | .p1, _, _, m =>
      (PEq.comp_assoc _ _ _).trans (PEq.compR _ (Term.homT_pure m))
  | .p2, _, _, m =>
      (PEq.comp_assoc _ _ _).trans (PEq.compR _ (Term.homT_pure m))
  | .unit, _, _, m => Term.homT_nil m
  | .prod F G, _, _, m =>
      (Term.fdot_comp_homT _ _ m).trans
        (Term.fdot_congr (TyF2.concatMap_comp_homT F m) (TyF2.concatMap_comp_homT G m))
  | .sum F G, _, _, m =>
      (Term.either_comp _ _ _).trans
        (Term.either_congr (TyF2.concatMap_comp_homT F m) (TyF2.concatMap_comp_homT G m))
  | .list F, _, _, m =>
      (Term.homT_comp _ _).trans (Term.homT_congr (TyF2.concatMap_comp_homT F m))

end Term

/-! ### Pushing a shape along a lift

The key step of the joint simplification: a shape with values in the leaves can be pushed
along a lift.  Every lift commutes with the concatenation maps, and a shape is a
concatenation map read through a fixed assignment of values to the letters. -/

/-- **Transport of a value shape along a lift.**  If `α : X ⊸ Y` is a lift, then every shape
with values in the leaves of `X` is provably equal to `α` followed by a shape with values in
the leaves of `Y`. -/
theorem shape_transport_of_lift (B : Ty) {X Y : Ty} {alpha : Term X Y} (ha : IsLift alpha) :
    ∀ lv : LeafVal B X, ∃ lv' : LeafVal B Y,
      shapeOf B X lv ≡ₜ (alpha ⨟ shapeOf B Y lv') := by
  induction ha with
  | @comp X Z Y f g _ _ ihf ihg =>
      intro lv
      obtain ⟨lv₁, h₁⟩ := ihf lv
      obtain ⟨lv₂, h₂⟩ := ihg lv₁
      exact ⟨lv₂, h₁.trans ((PEq.compR _ h₂).trans (PEq.symm (PEq.comp_assoc _ _ _)))⟩
  | @prodF X₁ X₂ Y₁ Y₂ f g _ _ ihf ihg =>
      intro lv
      obtain ⟨lv₁, h₁⟩ := ihf lv.1
      obtain ⟨lv₂, h₂⟩ := ihg lv.2
      refine ⟨(lv₁, lv₂), ?_⟩
      calc (shapeOf B X₁ lv.1 ⊙ shapeOf B X₂ lv.2)
          ≡ₜ ((f ⨟ shapeOf B Y₁ lv₁) ⊙ (g ⨟ shapeOf B Y₂ lv₂)) := Term.fdot_congr h₁ h₂
        _ ≡ₜ (Term.prodF f g ⨟ (shapeOf B Y₁ lv₁ ⊙ shapeOf B Y₂ lv₂)) := by
            calc ((Term.prodF (f ⨟ shapeOf B Y₁ lv₁) (g ⨟ shapeOf B Y₂ lv₂)) ⨟
                  Term.binconcat B)
                ≡ₜ ((Term.prodF f g ⨟
                      Term.prodF (shapeOf B Y₁ lv₁) (shapeOf B Y₂ lv₂)) ⨟ Term.binconcat B) :=
                  PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
              _ ≡ₜ (Term.prodF f g ⨟ (Term.prodF (shapeOf B Y₁ lv₁) (shapeOf B Y₂ lv₂) ⨟
                      Term.binconcat B)) := PEq.comp_assoc _ _ _
  | @sumF X₁ X₂ Y₁ Y₂ f g _ _ ihf ihg =>
      intro lv
      obtain ⟨lv₁, h₁⟩ := ihf lv.1
      obtain ⟨lv₂, h₂⟩ := ihg lv.2
      exact ⟨(lv₁, lv₂),
        (Term.either_congr h₁ h₂).trans (PEq.symm (Term.sumF_either _ _ _ _))⟩
  | @listF X Y f _ ih =>
      intro lv
      obtain ⟨lv', h⟩ := ih lv
      exact ⟨lv', (Term.homT_congr h).trans (Term.homT_precomp _ _)⟩
  | id X => exact fun lv => ⟨lv, PEq.symm (PEq.id_comp _)⟩
  | unitR X =>
      intro lv
      refine ⟨(lv, nilT B), ?_⟩
      calc shapeOf B X lv
          ≡ₜ (Term.id X ⨟ shapeOf B X lv) := PEq.symm (PEq.id_comp _)
        _ ≡ₜ ((Term.unitR X ⨟ Term.fst X Ty.unit) ⨟ shapeOf B X lv) :=
            PEq.compL _ (PEq.symm (PEq.unitR_fst X))
        _ ≡ₜ (Term.unitR X ⨟ (Term.fst X Ty.unit ⨟ shapeOf B X lv)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.unitR X ⨟ (shapeOf B X lv ⊙ nilT B)) :=
            PEq.compR _ (PEq.symm (Term.fdot_nil_right _))
  | unitL X =>
      intro lv
      refine ⟨(nilT B, lv), ?_⟩
      calc shapeOf B X lv
          ≡ₜ (Term.id X ⨟ shapeOf B X lv) := PEq.symm (PEq.id_comp _)
        _ ≡ₜ ((Term.unitL X ⨟ Term.snd Ty.unit X) ⨟ shapeOf B X lv) :=
            PEq.compL _ (PEq.symm (PEq.unitL_snd X))
        _ ≡ₜ (Term.unitL X ⨟ (Term.snd Ty.unit X ⨟ shapeOf B X lv)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.unitL X ⨟ (nilT B ⊙ shapeOf B X lv)) :=
            PEq.compR _ (PEq.symm (Term.fdot_nil_left _))
  | assocL X Y Z =>
      intro lv
      obtain ⟨a, b, c⟩ : LeafVal B X × LeafVal B Y × LeafVal B Z := lv
      refine ⟨((a, b), c), ?_⟩
      calc (shapeOf B X a ⊙ (shapeOf B Y b ⊙ shapeOf B Z c))
          ≡ₜ (Term.id (X ⊗ (Y ⊗ Z)) ⨟ (shapeOf B X a ⊙ (shapeOf B Y b ⊙ shapeOf B Z c))) :=
            PEq.symm (PEq.id_comp _)
        _ ≡ₜ ((Term.assocL X Y Z ⨟ Term.assocR X Y Z) ⨟
              (shapeOf B X a ⊙ (shapeOf B Y b ⊙ shapeOf B Z c))) :=
            PEq.compL _ (PEq.symm (PEq.assocL_assocR X Y Z))
        _ ≡ₜ (Term.assocL X Y Z ⨟ (Term.assocR X Y Z ⨟
              (shapeOf B X a ⊙ (shapeOf B Y b ⊙ shapeOf B Z c)))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.assocL X Y Z ⨟ ((shapeOf B X a ⊙ shapeOf B Y b) ⊙ shapeOf B Z c)) :=
            PEq.compR _ (PEq.symm (Term.fdot_assoc _ _ _))
  | assocR X Y Z =>
      intro lv
      obtain ⟨⟨a, b⟩, c⟩ : (LeafVal B X × LeafVal B Y) × LeafVal B Z := lv
      exact ⟨(a, (b, c)), Term.fdot_assoc _ _ _⟩
  | sumAssocL X Y Z =>
      intro lv
      obtain ⟨a, b, c⟩ : LeafVal B X × LeafVal B Y × LeafVal B Z := lv
      exact ⟨((a, b), c), Term.either_assocL _ _ _⟩
  | sumAssocR X Y Z =>
      intro lv
      obtain ⟨⟨a, b⟩, c⟩ : (LeafVal B X × LeafVal B Y) × LeafVal B Z := lv
      exact ⟨(a, (b, c)), Term.either_assocR _ _ _⟩
  | comm X Y =>
      intro lv
      refine ⟨(lv.2, lv.1), ?_⟩
      refine PEq.symm ((Term.either_comp _ _ _).trans (Term.either_congr ?_ ?_))
      · exact Term.inr_either _ _
      · exact Term.inl_either _ _
  | distL X Y Z =>
      intro lv
      obtain ⟨⟨a, b⟩, c⟩ : (LeafVal B X × LeafVal B Y) × LeafVal B Z := lv
      exact ⟨((a, c), (b, c)), Term.fdot_either_distL _ _ _⟩
  | distR X Y Z =>
      intro lv
      obtain ⟨a, b, c⟩ : LeafVal B X × LeafVal B Y × LeafVal B Z := lv
      exact ⟨((a, b), (a, c)), Term.fdot_either_distR _ _ _⟩
  | split X Y =>
      intro lv
      obtain ⟨a, b⟩ : LeafVal B X × LeafVal B Y := lv
      refine ⟨(a, (b, a)), ?_⟩
      set sa := shapeOf B X a with hsa
      set sb := shapeOf B Y b with hsb
      set m := Term.either sa sb with hm
      have hl : (Term.inl X Y ⨟ m) ≡ₜ sa := Term.inl_either _ _
      have hr : (Term.inr X Y ⨟ m) ≡ₜ sb := Term.inr_either _ _
      have hplug : (Term.unsplit X Y ⨟ Term.homT m) ≡ₜ
          (Term.homT sa ⊙ Term.homT (sb ⊙ Term.homT sa)) := by
        have h := (Term.TyF2.concatMap_comp_homT
            (.prod (.list .p1) (.list (.prod .p2 (.list .p1)))) m).trans
          (Term.TyF2.plug_congr (.prod (.list .p1) (.list (.prod .p2 (.list .p1)))) hl hr)
        simp [Term.TyF2.plug] at h
        exact h
      calc Term.homT m
          ≡ₜ (Term.id ((X ⊕' Y)⋆) ⨟ Term.homT m) := PEq.symm (PEq.id_comp _)
        _ ≡ₜ ((Term.split X Y ⨟ Term.unsplit X Y) ⨟ Term.homT m) :=
            PEq.compL _ (PEq.symm (PEq.split_unsplit X Y))
        _ ≡ₜ (Term.split X Y ⨟ (Term.unsplit X Y ⨟ Term.homT m)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.split X Y ⨟ (Term.homT sa ⊙ Term.homT (sb ⊙ Term.homT sa))) :=
            PEq.compR _ hplug
  | shift X Y =>
      intro lv
      obtain ⟨a, b⟩ : LeafVal B X × LeafVal B Y := lv
      refine ⟨(nilT B, (a, ((b, a), b))), ?_⟩
      set sa := shapeOf B X a with hsa
      set sb := shapeOf B Y b with hsb
      set m := Term.either sa sb with hm
      have hl : (Term.inl X Y ⨟ m) ≡ₜ sa := Term.inl_either _ _
      have hr : (Term.inr X Y ⨟ m) ≡ₜ sb := Term.inr_either _ _
      have hsrc : (TyF2.concatMap (.list (.prod .p1 .p2)) X Y ⨟ Term.homT m) ≡ₜ
          Term.homT (sa ⊙ sb) := by
        have h := (Term.TyF2.concatMap_comp_homT (.list (.prod .p1 .p2)) m).trans
          (Term.TyF2.plug_congr (.list (.prod .p1 .p2)) hl hr)
        simpa [Term.TyF2.plug] using h
      have htgt : (TyF2.concatMap
            (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) X Y ⨟
            Term.homT m) ≡ₜ
          Term.either (nilT B) (sa ⊙ (Term.homT (sb ⊙ sa) ⊙ sb)) := by
        have h := (Term.TyF2.concatMap_comp_homT
            (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) m).trans
          (Term.TyF2.plug_congr
            (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) hl hr)
        simpa [Term.TyF2.plug] using h
      calc Term.homT (sa ⊙ sb)
          ≡ₜ (TyF2.concatMap (.list (.prod .p1 .p2)) X Y ⨟ Term.homT m) := PEq.symm hsrc
        _ ≡ₜ ((Term.shift X Y ⨟ TyF2.concatMap
                (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) X Y) ⨟
              Term.homT m) :=
            PEq.compL _ (PEq.symm (Term.shift_rebracketing X Y))
        _ ≡ₜ (Term.shift X Y ⨟ (TyF2.concatMap
                (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) X Y ⨟
              Term.homT m)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.shift X Y ⨟
              Term.either (nilT B) (sa ⊙ (Term.homT (sb ⊙ sa) ⊙ sb))) := PEq.compR _ htgt

/-! ### Joint simplification -/

/-- **Lemma (joint simplification of two drops)** (appendix).  If `B` is a finite alphabet
and `f, g : A ⇒ B*` are drops, then there is a lift `A ⊸ D` whose drop inverse `π` is such
that both `π; f` and `π; g` are provably equal to shapes with values in the leaves. -/
theorem drops_to_common_shape {A B : Ty} (hB : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsDrop f) (hg : IsDrop g) :
    ∃ (D : Ty) (l : Term A D) (pi : Term D A) (lvf lvg : LeafVal B D),
      IsLift l ∧ IsDrop pi ∧ (l ⨟ pi) ≡ₜ Term.id A ∧ (pi ⨟ l) ≡ₜ Term.id D ∧
        (pi ⨟ f) ≡ₜ shapeOf B D lvf ∧ (pi ⨟ g) ≡ₜ shapeOf B D lvg := by
  -- simplify `f`
  obtain ⟨F, dlt1, vs, hdlt1, hfe⟩ := drop_simplification hB f hf
  obtain ⟨lv, hlv⟩ := exists_leafVal_normalListShape B F vs
  obtain ⟨pi₁, hpi₁, hdp₁, hpd₁⟩ := lift_iso dlt1 hdlt1
  have hf' : (pi₁ ⨟ f) ≡ₜ shapeOf B (F.app (fun _ => Ty.unit)) lv := by
    calc (pi₁ ⨟ f) ≡ₜ (pi₁ ⨟ (dlt1 ⨟ normalListShape B F (fun _ => Ty.unit) vs)) :=
          PEq.compR _ hfe
      _ ≡ₜ ((pi₁ ⨟ dlt1) ⨟ normalListShape B F (fun _ => Ty.unit) vs) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (F.app (fun _ => Ty.unit)) ⨟
            normalListShape B F (fun _ => Ty.unit) vs) := PEq.compL _ hpd₁
      _ ≡ₜ normalListShape B F (fun _ => Ty.unit) vs := PEq.id_comp _
      _ ≡ₜ shapeOf B (F.app (fun _ => Ty.unit)) lv := hlv
  -- simplify `π₁; g`
  obtain ⟨G, dlt2, ws, hdlt2, hge⟩ :=
    drop_simplification hB (pi₁ ⨟ g) (IsDrop.comp hpi₁ hg)
  obtain ⟨lw, hlw⟩ := exists_leafVal_normalListShape B G ws
  obtain ⟨pi₂, hpi₂, hdp₂, hpd₂⟩ := lift_iso dlt2 hdlt2
  have hg' : (pi₂ ⨟ (pi₁ ⨟ g)) ≡ₜ shapeOf B (G.app (fun _ => Ty.unit)) lw := by
    calc (pi₂ ⨟ (pi₁ ⨟ g))
        ≡ₜ (pi₂ ⨟ (dlt2 ⨟ normalListShape B G (fun _ => Ty.unit) ws)) := PEq.compR _ hge
      _ ≡ₜ ((pi₂ ⨟ dlt2) ⨟ normalListShape B G (fun _ => Ty.unit) ws) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (G.app (fun _ => Ty.unit)) ⨟
            normalListShape B G (fun _ => Ty.unit) ws) := PEq.compL _ hpd₂
      _ ≡ₜ normalListShape B G (fun _ => Ty.unit) ws := PEq.id_comp _
      _ ≡ₜ shapeOf B (G.app (fun _ => Ty.unit)) lw := hlw
  -- push the shape of `f` along the second lift
  obtain ⟨lv', hlv'⟩ := shape_transport_of_lift B hdlt2 lv
  refine ⟨G.app (fun _ => Ty.unit), dlt1 ⨟ dlt2, pi₂ ⨟ pi₁, lv', lw,
    IsLift.comp hdlt1 hdlt2, IsDrop.comp hpi₂ hpi₁, ?_, ?_, ?_, ?_⟩
  · calc ((dlt1 ⨟ dlt2) ⨟ (pi₂ ⨟ pi₁))
        ≡ₜ (dlt1 ⨟ (dlt2 ⨟ (pi₂ ⨟ pi₁))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (dlt1 ⨟ ((dlt2 ⨟ pi₂) ⨟ pi₁)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (dlt1 ⨟ (Term.id (F.app (fun _ => Ty.unit)) ⨟ pi₁)) :=
          PEq.compR _ (PEq.compL _ hdp₂)
      _ ≡ₜ (dlt1 ⨟ pi₁) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := hdp₁
  · calc ((pi₂ ⨟ pi₁) ⨟ (dlt1 ⨟ dlt2))
        ≡ₜ (pi₂ ⨟ (pi₁ ⨟ (dlt1 ⨟ dlt2))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pi₂ ⨟ ((pi₁ ⨟ dlt1) ⨟ dlt2)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (pi₂ ⨟ (Term.id (F.app (fun _ => Ty.unit)) ⨟ dlt2)) :=
          PEq.compR _ (PEq.compL _ hpd₁)
      _ ≡ₜ (pi₂ ⨟ dlt2) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id (G.app (fun _ => Ty.unit)) := hpd₂
  · calc ((pi₂ ⨟ pi₁) ⨟ f) ≡ₜ (pi₂ ⨟ (pi₁ ⨟ f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pi₂ ⨟ shapeOf B (F.app (fun _ => Ty.unit)) lv) := PEq.compR _ hf'
      _ ≡ₜ (pi₂ ⨟ (dlt2 ⨟ shapeOf B (G.app (fun _ => Ty.unit)) lv')) := PEq.compR _ hlv'
      _ ≡ₜ ((pi₂ ⨟ dlt2) ⨟ shapeOf B (G.app (fun _ => Ty.unit)) lv') :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (G.app (fun _ => Ty.unit)) ⨟
            shapeOf B (G.app (fun _ => Ty.unit)) lv') := PEq.compL _ hpd₂
      _ ≡ₜ shapeOf B (G.app (fun _ => Ty.unit)) lv' := PEq.id_comp _
  · exact (PEq.comp_assoc _ _ _).trans hg'

end Lax149335Proofs

bridge_export Lax149335Proofs
