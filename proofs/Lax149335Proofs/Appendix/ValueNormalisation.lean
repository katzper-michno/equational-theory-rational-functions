import Lax149335Proofs.Appendix.ShiftOnes
import Lax149335Proofs.EquationalTheory.Soundness
import Mathlib.Tactic.Set

/-!
# Computing with values (the proof of Lemma 5.3)

Lemma 5.3 of the paper says that every value `1 → A` is provably equivalent to a value in
normal form.  The proof in the appendix proceeds by induction on the structure of a term `f`,
showing that the composition `v; f` of a value `v` in normal form with `f` is again provably
equivalent to a value in normal form.

Here this is organised slightly differently.  For every element `x` of a type `A` we define a
value `encV A x : 1 → A` in normal form, and we prove the statement

  `Computes f`:  for every element `x` of the input type, `encV x ; f ≡ encV (⟦f⟧ x)`,

for every rational term `f`.  Lemma 5.3 is the special case where `f` is the value itself and
`x` is the unique element of the unit type.

The predicate `Computes` is closed under the four combinators, and the atomic functions are
treated one at a time.  Five atomic functions are treated by the *isomorphism trick* of the
paper: `uncons`, `unsnoc`, `shiftL`, `split` and the group prefix multiplication `pref` are
handled through their inverses `cons`, `snoc`, `shiftR`, `unsplit` and `unpref`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- The value representing an element of a type: the unique element of the unit type is
represented by the identity, an element of a product by a pair of values, an element of a
co-product by a value composed with a co-projection, and a list by the concatenation of the
singleton values of its entries. -/
def encV : (A : Ty) → ⟦A⟧ → Value A
  | .unit => fun _ => Term.id Ty.unit
  | .prod A B => fun x => Term.pairR (encV A x.1) (encV B x.2)
  | .sum A B => fun x =>
      match x with
      | .inl a => encV A a ⨟ Term.inl A B
      | .inr b => encV B b ⨟ Term.inr A B
  | .list A => fun l => l.foldr (fun a v => Term.dotL (Term.sing (encV A a)) v) (Term.nilT A)

@[simp] theorem encV_unit (x : ⟦Ty.unit⟧) : encV Ty.unit x = Term.id Ty.unit := rfl

@[simp] theorem encV_prod (A B : Ty) (x : ⟦A ⊗ B⟧) :
    encV (A ⊗ B) x = Term.pairR (encV A x.1) (encV B x.2) := rfl

@[simp] theorem encV_inl (A B : Ty) (a : ⟦A⟧) :
    encV (A ⊕' B) (Sum.inl a) = (encV A a ⨟ Term.inl A B) := rfl

@[simp] theorem encV_inr (A B : Ty) (b : ⟦B⟧) :
    encV (A ⊕' B) (Sum.inr b) = (encV B b ⨟ Term.inr A B) := rfl

@[simp] theorem encV_nil (A : Ty) : encV A⋆ [] = Term.nilT A := rfl

@[simp] theorem encV_cons (A : Ty) (a : ⟦A⟧) (l : ⟦A⋆⟧) :
    encV A⋆ (a :: l) = Term.dotL (Term.sing (encV A a)) (encV A⋆ l) := rfl

namespace Term

/-! ### A few auxiliary derived rules -/

/-- Inserting the unit type on the left or on the right of the unit type agree. -/
theorem unitL_unit : unitL Ty.unit ≡ₜ unitR Ty.unit := by
  calc unitL Ty.unit ≡ₜ (unitL Ty.unit ⨟ Term.id (Ty.unit ⊗ Ty.unit)) :=
        PEq.symm (PEq.comp_id _)
    _ ≡ₜ (unitL Ty.unit ⨟ (fst Ty.unit Ty.unit ⨟ unitR Ty.unit)) :=
        PEq.compR _ (PEq.symm (PEq.fst_unitR Ty.unit))
    _ ≡ₜ ((unitL Ty.unit ⨟ fst Ty.unit Ty.unit) ⨟ unitR Ty.unit) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id Ty.unit ⨟ unitR Ty.unit) :=
        PEq.compL _ (PEq.unit_unique _ _)
    _ ≡ₜ unitR Ty.unit := PEq.id_comp _

/-- For two values, pairing on the left and on the right agree. -/
theorem pairL_eq_pairR {B C : Ty} (v : Value C) (w : Value B) :
    pairL v w ≡ₜ pairR v w :=
  PEq.compL _ unitL_unit

/-- For two list values, concatenating on the left and on the right agree. -/
theorem dotL_eq_dotR {B : Ty} (v w : Value B⋆) : dotL v w ≡ₜ dotR v w :=
  PEq.compL _ (pairL_eq_pairR v w)

/-- Congruence for concatenation on the left. -/
theorem dotL_congr {X B : Ty} {w w' : Value B⋆} {f f' : Term X B⋆} (hw : w ≡ₜ w')
    (hf : f ≡ₜ f') : dotL w f ≡ₜ dotL w' f' :=
  PEq.compL _ (PEq.compR _ (PEq.congr_prodF hw hf))

/-- Congruence for concatenation on the right. -/
theorem dotR_congr {X B : Ty} {f f' : Term X B⋆} {w w' : Value B⋆} (hf : f ≡ₜ f')
    (hw : w ≡ₜ w') : dotR f w ≡ₜ dotR f' w' :=
  PEq.compL _ (PEq.compR _ (PEq.congr_prodF hf hw))

/-- The second projection recovers the second component of a right pairing with a value. -/
theorem pairR_snd {B C : Ty} (v : Value B) (w : Value C) :
    (pairR v w ⨟ snd B C) ≡ₜ w := by
  calc ((unitR Ty.unit ⨟ prodF v w) ⨟ snd B C)
      ≡ₜ (unitR Ty.unit ⨟ (prodF v w ⨟ snd B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR Ty.unit ⨟ (snd Ty.unit Ty.unit ⨟ w)) := PEq.compR _ (PEq.nat_snd v w)
    _ ≡ₜ ((unitR Ty.unit ⨟ snd Ty.unit Ty.unit) ⨟ w) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id Ty.unit ⨟ w) := PEq.compL _ (PEq.unit_unique _ _)
    _ ≡ₜ w := PEq.id_comp _

/-- Concatenation on the left is natural. -/
theorem dotL_natural {X A B : Ty} (w : Value A⋆) (g : Term X A⋆) (f : Term A B) :
    (dotL w g ⨟ listF f) ≡ₜ dotL (w ⨟ listF f) (g ⨟ listF f) := by
  calc (((unitL X ⨟ prodF w g) ⨟ binconcat A) ⨟ listF f)
      ≡ₜ ((unitL X ⨟ (prodF w g ⨟ binconcat A)) ⨟ listF f) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (unitL X ⨟ ((prodF w g ⨟ binconcat A) ⨟ listF f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL X ⨟ (prodF (w ⨟ listF f) (g ⨟ listF f) ⨟ binconcat B)) :=
        PEq.compR _ (fdot_natural w g f)
    _ ≡ₜ ((unitL X ⨟ prodF (w ⨟ listF f) (g ⨟ listF f)) ⨟ binconcat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- Distributivity on the left undoes the left co-projection. -/
theorem prodF_inl_distL (A B C : Ty) :
    (prodF (inl A B) (Term.id C) ⨟ distL A B C) ≡ₜ inl (A ⊗ C) (B ⊗ C) := by
  calc (prodF (inl A B) (Term.id C) ⨟ distL A B C)
      ≡ₜ ((inl (A ⊗ C) (B ⊗ C) ⨟ undistL A B C) ⨟ distL A B C) :=
        PEq.compL _ (PEq.symm (inl_either _ _))
    _ ≡ₜ (inl (A ⊗ C) (B ⊗ C) ⨟ (undistL A B C ⨟ distL A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl (A ⊗ C) (B ⊗ C) ⨟ Term.id ((A ⊗ C) ⊕' (B ⊗ C))) :=
        PEq.compR _ (PEq.undistL_distL A B C)
    _ ≡ₜ inl (A ⊗ C) (B ⊗ C) := PEq.comp_id _

/-- Distributivity on the left undoes the right co-projection. -/
theorem prodF_inr_distL (A B C : Ty) :
    (prodF (inr A B) (Term.id C) ⨟ distL A B C) ≡ₜ inr (A ⊗ C) (B ⊗ C) := by
  calc (prodF (inr A B) (Term.id C) ⨟ distL A B C)
      ≡ₜ ((inr (A ⊗ C) (B ⊗ C) ⨟ undistL A B C) ⨟ distL A B C) :=
        PEq.compL _ (PEq.symm (inr_either _ _))
    _ ≡ₜ (inr (A ⊗ C) (B ⊗ C) ⨟ (undistL A B C ⨟ distL A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inr (A ⊗ C) (B ⊗ C) ⨟ Term.id ((A ⊗ C) ⊕' (B ⊗ C))) :=
        PEq.compR _ (PEq.undistL_distL A B C)
    _ ≡ₜ inr (A ⊗ C) (B ⊗ C) := PEq.comp_id _

/-- The singleton list is natural. -/
theorem sing_natural {A B : Ty} (v : Value A) (f : Term A B) :
    (sing v ⨟ listF f) ≡ₜ sing (v ⨟ f) := by
  calc ((v ⨟ pureT A) ⨟ listF f) ≡ₜ (v ⨟ (pureT A ⨟ listF f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (v ⨟ (f ⨟ pureT B)) := PEq.compR _ (PEq.symm (pureT_natural f))
    _ ≡ₜ ((v ⨟ f) ⨟ pureT B) := PEq.symm (PEq.comp_assoc _ _ _)

end Term

/-- A term *computes on values* if composing it with the value representing an element `x`
gives the value representing the image of `x`. -/
def Computes {A B : Ty} (f : Term A B) : Prop :=
  ∀ x : ⟦A⟧, (encV A x ⨟ f) ≡ₜ encV B (f.den x)

namespace Computes

theorem comp {A B C : Ty} {f : Term A B} {g : Term B C} (hf : Computes f)
    (hg : Computes g) : Computes (f ⨟ g) := by
  intro x
  show (encV A x ⨟ (f ⨟ g)) ≡ₜ encV C (g.den (f.den x))
  calc (encV A x ⨟ (f ⨟ g)) ≡ₜ ((encV A x ⨟ f) ⨟ g) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (encV B (f.den x) ⨟ g) := PEq.compL _ (hf x)
    _ ≡ₜ encV C (g.den (f.den x)) := hg _

theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} (hf : Computes f)
    (hg : Computes g) : Computes (Term.prodF f g) := by
  intro x
  show (Term.pairR (encV A₁ x.1) (encV A₂ x.2) ⨟ Term.prodF f g) ≡ₜ
    Term.pairR (encV B₁ (f.den x.1)) (encV B₂ (g.den x.2))
  exact (Term.pairR_prodF _ _ _ _).trans (Term.pairR_congr (hf x.1) (hg x.2))

theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} (hf : Computes f)
    (hg : Computes g) : Computes (Term.sumF f g) := by
  intro x
  match x with
  | .inl a =>
      show ((encV A₁ a ⨟ Term.inl A₁ A₂) ⨟ Term.sumF f g) ≡ₜ
        (encV B₁ (f.den a) ⨟ Term.inl B₁ B₂)
      calc ((encV A₁ a ⨟ Term.inl A₁ A₂) ⨟ Term.sumF f g)
          ≡ₜ (encV A₁ a ⨟ (Term.inl A₁ A₂ ⨟ Term.sumF f g)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (encV A₁ a ⨟ (f ⨟ Term.inl B₁ B₂)) := PEq.compR _ (PEq.nat_inl f g)
        _ ≡ₜ ((encV A₁ a ⨟ f) ⨟ Term.inl B₁ B₂) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (encV B₁ (f.den a) ⨟ Term.inl B₁ B₂) := PEq.compL _ (hf a)
  | .inr b =>
      show ((encV A₂ b ⨟ Term.inr A₁ A₂) ⨟ Term.sumF f g) ≡ₜ
        (encV B₂ (g.den b) ⨟ Term.inr B₁ B₂)
      calc ((encV A₂ b ⨟ Term.inr A₁ A₂) ⨟ Term.sumF f g)
          ≡ₜ (encV A₂ b ⨟ (Term.inr A₁ A₂ ⨟ Term.sumF f g)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (encV A₂ b ⨟ (g ⨟ Term.inr B₁ B₂)) := PEq.compR _ (PEq.nat_inr f g)
        _ ≡ₜ ((encV A₂ b ⨟ g) ⨟ Term.inr B₁ B₂) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (encV B₂ (g.den b) ⨟ Term.inr B₁ B₂) := PEq.compL _ (hg b)

theorem listF {A B : Ty} {f : Term A B} (hf : Computes f) : Computes (Term.listF f) := by
  intro l
  show (encV A⋆ l ⨟ Term.listF f) ≡ₜ encV B⋆ (l.map f.den)
  induction l with
  | nil => exact Term.nilT_natural f
  | cons a t ih =>
      calc (Term.dotL (Term.sing (encV A a)) (encV A⋆ t) ⨟ Term.listF f)
          ≡ₜ Term.dotL (Term.sing (encV A a) ⨟ Term.listF f) (encV A⋆ t ⨟ Term.listF f) :=
            Term.dotL_natural _ _ _
        _ ≡ₜ Term.dotL (Term.sing (encV B (f.den a))) (encV B⋆ (t.map f.den)) :=
            Term.dotL_congr ((Term.sing_natural _ f).trans
              (PEq.congr_comp (hf a) (PEq.refl _))) ih

/-- The isomorphism trick: if `g` is a two-sided inverse of `f` that computes on values, then
so does `f`. -/
theorem of_inverse {A B : Ty} {f : Term A B} {g : Term B A} (hg : Computes g)
    (h₁ : (f ⨟ g) ≡ₜ Term.id A) (h₂ : (g ⨟ f) ≡ₜ Term.id B) : Computes f := by
  intro x
  have hden : g.den (f.den x) = x := congrFun (PEq.sound h₁) x
  have h3 : (encV B (f.den x) ⨟ g) ≡ₜ encV A x := by
    have h4 := hg (f.den x)
    rwa [hden] at h4
  calc (encV A x ⨟ f) ≡ₜ ((encV B (f.den x) ⨟ g) ⨟ f) := PEq.compL _ (PEq.symm h3)
    _ ≡ₜ (encV B (f.den x) ⨟ (g ⨟ f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (encV B (f.den x) ⨟ Term.id B) := PEq.compR _ h₂
    _ ≡ₜ encV B (f.den x) := PEq.comp_id _

end Computes

/-! ### The atomic functions -/

theorem computes_id (A : Ty) : Computes (Term.id A) := fun x => PEq.comp_id (encV A x)

theorem computes_inl (A B : Ty) : Computes (Term.inl A B) := fun _ => PEq.refl _

theorem computes_inr (A B : Ty) : Computes (Term.inr A B) := fun _ => PEq.refl _

theorem computes_codiag (A : Ty) : Computes (Term.codiag A) := by
  intro x
  match x with
  | .inl a =>
      show ((encV A a ⨟ Term.inl A A) ⨟ Term.codiag A) ≡ₜ encV A a
      calc ((encV A a ⨟ Term.inl A A) ⨟ Term.codiag A)
          ≡ₜ (encV A a ⨟ (Term.inl A A ⨟ Term.codiag A)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (encV A a ⨟ Term.id A) := PEq.compR _ (PEq.inl_codiag A)
        _ ≡ₜ encV A a := PEq.comp_id _
  | .inr a =>
      show ((encV A a ⨟ Term.inr A A) ⨟ Term.codiag A) ≡ₜ encV A a
      calc ((encV A a ⨟ Term.inr A A) ⨟ Term.codiag A)
          ≡ₜ (encV A a ⨟ (Term.inr A A ⨟ Term.codiag A)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (encV A a ⨟ Term.id A) := PEq.compR _ (PEq.inr_codiag A)
        _ ≡ₜ encV A a := PEq.comp_id _

theorem computes_fst (A B : Ty) : Computes (Term.fst A B) := fun x =>
  Term.pairR_fst (encV A x.1) (encV B x.2)

theorem computes_snd (A B : Ty) : Computes (Term.snd A B) := fun x =>
  Term.pairR_snd (encV A x.1) (encV B x.2)

theorem computes_unitR (A : Ty) : Computes (Term.unitR A) := fun x =>
  PEq.nat_unitR (encV A x)

theorem computes_unitL (A : Ty) : Computes (Term.unitL A) := by
  intro x
  show (encV A x ⨟ Term.unitL A) ≡ₜ Term.pairR (Term.id Ty.unit) (encV A x)
  calc (encV A x ⨟ Term.unitL A)
      ≡ₜ (Term.unitL Ty.unit ⨟ Term.prodF (Term.id Ty.unit) (encV A x)) :=
        PEq.nat_unitL (encV A x)
    _ ≡ₜ (Term.unitR Ty.unit ⨟ Term.prodF (Term.id Ty.unit) (encV A x)) :=
        PEq.compL _ Term.unitL_unit

theorem computes_assocR (A B C : Ty) : Computes (Term.assocR A B C) := by
  intro x
  set u : Value A := encV A x.1.1 with hu
  set v : Value B := encV B x.1.2 with hv
  set w : Value C := encV C x.2 with hw
  show (Term.pairR (Term.pairR u v) w ⨟ Term.assocR A B C) ≡ₜ Term.pairR u (Term.pairR v w)
  calc ((Term.unitR Ty.unit ⨟ Term.prodF (Term.pairR u v) w) ⨟ Term.assocR A B C)
      ≡ₜ ((Term.unitR Ty.unit ⨟
            Term.prodF (Term.unitR Ty.unit ⨟ Term.prodF u v)
              (Term.id Ty.unit ⨟ w)) ⨟ Term.assocR A B C) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.id_comp _))))
    _ ≡ₜ ((Term.unitR Ty.unit ⨟
            (Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit) ⨟
              Term.prodF (Term.prodF u v) w)) ⨟ Term.assocR A B C) :=
        PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((Term.unitR Ty.unit ⨟ Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit)) ⨟
            Term.prodF (Term.prodF u v) w) ⨟ Term.assocR A B C) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((Term.unitR Ty.unit ⨟ Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit)) ⨟
          (Term.prodF (Term.prodF u v) w ⨟ Term.assocR A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((Term.unitR Ty.unit ⨟ Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit)) ⨟
          (Term.assocR Ty.unit Ty.unit Ty.unit ⨟ Term.prodF u (Term.prodF v w))) :=
        PEq.compR _ (PEq.nat_assocR u v w)
    _ ≡ₜ (((Term.unitR Ty.unit ⨟ Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit)) ⨟
          Term.assocR Ty.unit Ty.unit Ty.unit) ⨟ Term.prodF u (Term.prodF v w)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.unitR Ty.unit ⨟ (Term.prodF (Term.unitR Ty.unit) (Term.id Ty.unit) ⨟
          Term.assocR Ty.unit Ty.unit Ty.unit)) ⨟ Term.prodF u (Term.prodF v w)) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.unitR Ty.unit ⨟ Term.prodF (Term.id Ty.unit) (Term.unitL Ty.unit)) ⨟
          Term.prodF u (Term.prodF v w)) :=
        PEq.compL _ (Term.unitR_unitR_assocR Ty.unit)
    _ ≡ₜ ((Term.unitR Ty.unit ⨟ Term.prodF (Term.id Ty.unit) (Term.unitR Ty.unit)) ⨟
          Term.prodF u (Term.prodF v w)) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _) Term.unitL_unit))
    _ ≡ₜ (Term.unitR Ty.unit ⨟ (Term.prodF (Term.id Ty.unit) (Term.unitR Ty.unit) ⨟
          Term.prodF u (Term.prodF v w))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.unitR Ty.unit ⨟ Term.prodF (Term.id Ty.unit ⨟ u)
          (Term.unitR Ty.unit ⨟ Term.prodF v w)) := PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (Term.unitR Ty.unit ⨟ Term.prodF u (Term.unitR Ty.unit ⨟ Term.prodF v w)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))

theorem computes_assocL (A B C : Ty) : Computes (Term.assocL A B C) :=
  Computes.of_inverse (computes_assocR A B C) (PEq.assocL_assocR A B C)
    (PEq.assocR_assocL A B C)

theorem computes_distR (A B C : Ty) : Computes (Term.distR A B C) := by
  intro x
  obtain ⟨a, s⟩ := x
  match s with
  | .inl b =>
      show (Term.pairR (encV A a) (encV B b ⨟ Term.inl B C) ⨟ Term.distR A B C) ≡ₜ
        (Term.pairR (encV A a) (encV B b) ⨟ Term.inl (A ⊗ B) (A ⊗ C))
      calc (Term.pairR (encV A a) (encV B b ⨟ Term.inl B C) ⨟ Term.distR A B C)
          ≡ₜ ((Term.pairR (encV A a) (encV B b) ⨟
              Term.prodF (Term.id A) (Term.inl B C)) ⨟ Term.distR A B C) :=
            PEq.compL _ (PEq.symm ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.comp_id _) (PEq.refl _))))
        _ ≡ₜ (Term.pairR (encV A a) (encV B b) ⨟
              (Term.prodF (Term.id A) (Term.inl B C) ⨟ Term.distR A B C)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV A a) (encV B b) ⨟ Term.inl (A ⊗ B) (A ⊗ C)) :=
            PEq.compR _ (Term.prodF_inl_distR A B C)
  | .inr c =>
      show (Term.pairR (encV A a) (encV C c ⨟ Term.inr B C) ⨟ Term.distR A B C) ≡ₜ
        (Term.pairR (encV A a) (encV C c) ⨟ Term.inr (A ⊗ B) (A ⊗ C))
      calc (Term.pairR (encV A a) (encV C c ⨟ Term.inr B C) ⨟ Term.distR A B C)
          ≡ₜ ((Term.pairR (encV A a) (encV C c) ⨟
              Term.prodF (Term.id A) (Term.inr B C)) ⨟ Term.distR A B C) :=
            PEq.compL _ (PEq.symm ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.comp_id _) (PEq.refl _))))
        _ ≡ₜ (Term.pairR (encV A a) (encV C c) ⨟
              (Term.prodF (Term.id A) (Term.inr B C) ⨟ Term.distR A B C)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV A a) (encV C c) ⨟ Term.inr (A ⊗ B) (A ⊗ C)) :=
            PEq.compR _ (Term.prodF_inr_distR A B C)

theorem computes_distL (A B C : Ty) : Computes (Term.distL A B C) := by
  intro x
  obtain ⟨s, c⟩ := x
  match s with
  | .inl a =>
      show (Term.pairR (encV A a ⨟ Term.inl A B) (encV C c) ⨟ Term.distL A B C) ≡ₜ
        (Term.pairR (encV A a) (encV C c) ⨟ Term.inl (A ⊗ C) (B ⊗ C))
      calc (Term.pairR (encV A a ⨟ Term.inl A B) (encV C c) ⨟ Term.distL A B C)
          ≡ₜ ((Term.pairR (encV A a) (encV C c) ⨟
              Term.prodF (Term.inl A B) (Term.id C)) ⨟ Term.distL A B C) :=
            PEq.compL _ (PEq.symm ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.refl _) (PEq.comp_id _))))
        _ ≡ₜ (Term.pairR (encV A a) (encV C c) ⨟
              (Term.prodF (Term.inl A B) (Term.id C) ⨟ Term.distL A B C)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV A a) (encV C c) ⨟ Term.inl (A ⊗ C) (B ⊗ C)) :=
            PEq.compR _ (Term.prodF_inl_distL A B C)
  | .inr b =>
      show (Term.pairR (encV B b ⨟ Term.inr A B) (encV C c) ⨟ Term.distL A B C) ≡ₜ
        (Term.pairR (encV B b) (encV C c) ⨟ Term.inr (A ⊗ C) (B ⊗ C))
      calc (Term.pairR (encV B b ⨟ Term.inr A B) (encV C c) ⨟ Term.distL A B C)
          ≡ₜ ((Term.pairR (encV B b) (encV C c) ⨟
              Term.prodF (Term.inr A B) (Term.id C)) ⨟ Term.distL A B C) :=
            PEq.compL _ (PEq.symm ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.refl _) (PEq.comp_id _))))
        _ ≡ₜ (Term.pairR (encV B b) (encV C c) ⨟
              (Term.prodF (Term.inr A B) (Term.id C) ⨟ Term.distL A B C)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV B b) (encV C c) ⨟ Term.inr (A ⊗ C) (B ⊗ C)) :=
            PEq.compR _ (Term.prodF_inr_distL A B C)

/-! ### Lists -/

/-- The value representing a singleton list is the singleton of the value. -/
theorem encV_singleton (A : Ty) (a : ⟦A⟧) : encV A⋆ [a] ≡ₜ Term.sing (encV A a) :=
  (Term.dotL_eq_dotR _ _).trans (Term.dotR_nil _)

/-- The value representing a concatenation of two lists is the concatenation of the two
values. -/
theorem encV_append (A : Ty) (l₁ l₂ : List ⟦A⟧) :
    encV A⋆ (l₁ ++ l₂) ≡ₜ Term.dotR (encV A⋆ l₁) (encV A⋆ l₂) := by
  induction l₁ with
  | nil =>
      exact PEq.symm ((PEq.symm (Term.dotL_eq_dotR _ _)).trans (Term.dotL_nil _))
  | cons a t ih =>
      show encV A⋆ (a :: (t ++ l₂)) ≡ₜ
        Term.dotR (Term.dotL (Term.sing (encV A a)) (encV A⋆ t)) (encV A⋆ l₂)
      exact (Term.dotL_congr (PEq.refl _) ih).trans (PEq.symm (Term.dotR_dotL _ _ _))

theorem computes_cons (A : Ty) : Computes (Term.cons A) := by
  intro x
  match x with
  | .inl _ =>
      show ((Term.id Ty.unit ⨟ Term.inl Ty.unit (A ⊗ A⋆)) ⨟ Term.cons A) ≡ₜ Term.nilT A
      exact PEq.compL _ (PEq.id_comp _)
  | .inr y =>
      show ((Term.pairR (encV A y.1) (encV A⋆ y.2) ⨟ Term.inr Ty.unit (A ⊗ A⋆)) ⨟
        Term.cons A) ≡ₜ Term.dotL (Term.sing (encV A y.1)) (encV A⋆ y.2)
      calc ((Term.pairR (encV A y.1) (encV A⋆ y.2) ⨟ Term.inr Ty.unit (A ⊗ A⋆)) ⨟
            Term.cons A)
          ≡ₜ (Term.pairR (encV A y.1) (encV A⋆ y.2) ⨟ Term.prepend A) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV A y.1) (encV A⋆ y.2) ⨟
              (Term.prodF (Term.pureT A) (Term.id A⋆) ⨟ Term.binconcat A)) :=
            PEq.compR _ (PEq.prepend_def A)
        _ ≡ₜ ((Term.pairR (encV A y.1) (encV A⋆ y.2) ⨟
              Term.prodF (Term.pureT A) (Term.id A⋆)) ⨟ Term.binconcat A) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.pairR (Term.sing (encV A y.1)) (encV A⋆ y.2) ⨟ Term.binconcat A) :=
            PEq.compL _ ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.refl _) (PEq.comp_id _)))
        _ ≡ₜ Term.dotL (Term.sing (encV A y.1)) (encV A⋆ y.2) :=
            PEq.symm (Term.dotL_eq_dotR _ _)

theorem computes_snoc (A : Ty) : Computes (Term.snoc A) := by
  intro x
  match x with
  | .inl _ =>
      show ((Term.id Ty.unit ⨟ Term.inl Ty.unit (A⋆ ⊗ A)) ⨟ Term.snoc A) ≡ₜ Term.nilT A
      exact (PEq.compL _ (PEq.id_comp _)).trans (PEq.inl_snoc_cons A)
  | .inr y =>
      refine PEq.trans ?_ (PEq.symm (encV_append A y.1 [y.2]))
      show ((Term.pairR (encV A⋆ y.1) (encV A y.2) ⨟ Term.inr Ty.unit (A⋆ ⊗ A)) ⨟
        Term.snoc A) ≡ₜ Term.dotR (encV A⋆ y.1) (encV A⋆ [y.2])
      calc ((Term.pairR (encV A⋆ y.1) (encV A y.2) ⨟ Term.inr Ty.unit (A⋆ ⊗ A)) ⨟
            Term.snoc A)
          ≡ₜ (Term.pairR (encV A⋆ y.1) (encV A y.2) ⨟ Term.append A) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (Term.pairR (encV A⋆ y.1) (encV A y.2) ⨟
              (Term.prodF (Term.id A⋆) (Term.pureT A) ⨟ Term.binconcat A)) :=
            PEq.compR _ (PEq.append_def A)
        _ ≡ₜ ((Term.pairR (encV A⋆ y.1) (encV A y.2) ⨟
              Term.prodF (Term.id A⋆) (Term.pureT A)) ⨟ Term.binconcat A) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ Term.dotR (encV A⋆ y.1) (Term.sing (encV A y.2)) :=
            PEq.compL _ ((Term.pairR_prodF _ _ _ _).trans
              (Term.pairR_congr (PEq.comp_id _) (PEq.refl _)))
        _ ≡ₜ Term.dotR (encV A⋆ y.1) (encV A⋆ [y.2]) :=
            Term.dotR_congr (PEq.refl _) (PEq.symm (encV_singleton A y.2))

/-- Concatenating a list of lists distributes over concatenation on the left. -/
theorem dotL_concat {X A : Ty} (w : Value A⋆⋆) (g : Term X A⋆⋆) :
    (Term.dotL w g ⨟ Term.concat A) ≡ₜ
      Term.dotL (w ⨟ Term.concat A) (g ⨟ Term.concat A) := by
  calc (((Term.unitL X ⨟ Term.prodF w g) ⨟ Term.binconcat A⋆) ⨟ Term.concat A)
      ≡ₜ ((Term.unitL X ⨟ Term.prodF w g) ⨟ (Term.binconcat A⋆ ⨟ Term.concat A)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((Term.unitL X ⨟ Term.prodF w g) ⨟
          (Term.prodF (Term.concat A) (Term.concat A) ⨟ Term.binconcat A)) :=
        PEq.compR _ (PEq.binconcat_concat A)
    _ ≡ₜ (((Term.unitL X ⨟ Term.prodF w g) ⨟
          Term.prodF (Term.concat A) (Term.concat A)) ⨟ Term.binconcat A) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.unitL X ⨟ (Term.prodF w g ⨟
          Term.prodF (Term.concat A) (Term.concat A))) ⨟ Term.binconcat A) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.unitL X ⨟ Term.prodF (w ⨟ Term.concat A) (g ⨟ Term.concat A)) ⨟
          Term.binconcat A) := PEq.compL _ (PEq.compR _ (PEq.prod_comp _ _ _ _))

theorem computes_concat (A : Ty) : Computes (Term.concat A) := by
  intro l
  show (encV A⋆⋆ l ⨟ Term.concat A) ≡ₜ encV A⋆ l.flatten
  induction l with
  | nil => exact PEq.nil_concat A
  | cons t rest ih =>
      refine PEq.trans ?_ (PEq.symm (encV_append A t rest.flatten))
      have hsing : (Term.sing (encV A⋆ t) ⨟ Term.concat A) ≡ₜ encV A⋆ t := by
        calc ((encV A⋆ t ⨟ Term.pureT A⋆) ⨟ Term.concat A)
            ≡ₜ (encV A⋆ t ⨟ (Term.pureT A⋆ ⨟ Term.concat A)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (encV A⋆ t ⨟ Term.id A⋆) := PEq.compR _ (PEq.pure_concat A)
          _ ≡ₜ encV A⋆ t := PEq.comp_id _
      calc (Term.dotL (Term.sing (encV A⋆ t)) (encV A⋆⋆ rest) ⨟ Term.concat A)
          ≡ₜ Term.dotL (Term.sing (encV A⋆ t) ⨟ Term.concat A)
              (encV A⋆⋆ rest ⨟ Term.concat A) := dotL_concat _ _
        _ ≡ₜ Term.dotL (encV A⋆ t) (encV A⋆ rest.flatten) := Term.dotL_congr hsing ih
        _ ≡ₜ Term.dotR (encV A⋆ t) (encV A⋆ rest.flatten) := Term.dotL_eq_dotR _ _

theorem computes_uncons (A : Ty) : Computes (Term.uncons A) :=
  Computes.of_inverse (computes_cons A) (PEq.uncons_cons A) (PEq.cons_uncons A)

theorem computes_unsnoc (A : Ty) : Computes (Term.unsnoc A) :=
  Computes.of_inverse (computes_snoc A) (PEq.unsnoc_snoc A) (PEq.snoc_unsnoc A)

/-! ### Terms that do not use the six atomic functions treated separately -/

/-- Whether a term uses one of the atomic functions `uncons`, `unsnoc`, `shiftL`, `shiftR`,
`split` and `pref`, which are treated separately. -/
def usesHard : {A B : Ty} → Term A B → Bool
  | _, _, .comp f g => usesHard f || usesHard g
  | _, _, .prodF f g => usesHard f || usesHard g
  | _, _, .sumF f g => usesHard f || usesHard g
  | _, _, .listF f => usesHard f
  | _, _, .uncons _ => true
  | _, _, .unsnoc _ => true
  | _, _, .shiftL _ _ => true
  | _, _, .shiftR _ _ => true
  | _, _, .split _ _ => true
  | _, _, .pref _ _ => true
  | _, _, _ => false

/-- Every term that does not use one of the six atomic functions treated separately computes
on values. -/
theorem computes_of_not_usesHard : {A B : Ty} → (f : Term A B) → usesHard f = false →
    Computes f := by
  intro A B f
  induction f with
  | comp f g ihf ihg =>
      intro h
      have h' : (usesHard f || usesHard g) = false := h
      rw [Bool.or_eq_false_iff] at h'
      exact Computes.comp (ihf h'.1) (ihg h'.2)
  | prodF f g ihf ihg =>
      intro h
      have h' : (usesHard f || usesHard g) = false := h
      rw [Bool.or_eq_false_iff] at h'
      exact Computes.prodF (ihf h'.1) (ihg h'.2)
  | sumF f g ihf ihg =>
      intro h
      have h' : (usesHard f || usesHard g) = false := h
      rw [Bool.or_eq_false_iff] at h'
      exact Computes.sumF (ihf h'.1) (ihg h'.2)
  | listF f ih =>
      intro h
      exact Computes.listF (ih h)
  | id A => intro _; exact computes_id A
  | inl A B => intro _; exact computes_inl A B
  | inr A B => intro _; exact computes_inr A B
  | codiag A => intro _; exact computes_codiag A
  | fst A B => intro _; exact computes_fst A B
  | snd A B => intro _; exact computes_snd A B
  | unitR A => intro _; exact computes_unitR A
  | unitL A => intro _; exact computes_unitL A
  | assocL A B C => intro _; exact computes_assocL A B C
  | assocR A B C => intro _; exact computes_assocR A B C
  | distR A B C => intro _; exact computes_distR A B C
  | distL A B C => intro _; exact computes_distL A B C
  | cons A => intro _; exact computes_cons A
  | snoc A => intro _; exact computes_snoc A
  | concat A => intro _; exact computes_concat A
  | uncons A => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)
  | unsnoc A => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)
  | shiftL A B => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)
  | shiftR A B => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)
  | split A B => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)
  | pref A G => intro h; exact Bool.noConfusion (show (true : Bool) = false from h)

/-! ### The atomic functions `shiftR` and `shiftL`

These are treated by cancelling the concatenation map `A ⊗ (B ⊗ A)* ↣ (A+B)*` of Axiom 15,
which is provably injective: its left inverse is obtained from the symmetric variant of
splitting, whose inverse is the concatenation map of `(A* ⊗ B)* ⊗ A*`. -/

namespace Term

/-- The first element of a list, or a default value if the list is empty. -/
def headOr (A : Ty) : Term A⋆ A :=
  uncons A ⨟ either (defaultValue A) (fst A A⋆)

/-- Taking the head of a one element list gives the element back. -/
theorem pureT_headOr (A : Ty) : (pureT A ⨟ headOr A) ≡ₜ Term.id A := by
  have hpu : (prepend A ⨟ uncons A) ≡ₜ inr Ty.unit (A ⊗ A⋆) := by
    calc ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ uncons A)
        ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ uncons A)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ Term.id (Ty.unit ⊕' (A ⊗ A⋆))) :=
          PEq.compR _ (PEq.cons_uncons A)
      _ ≡ₜ inr Ty.unit (A ⊗ A⋆) := PEq.comp_id _
  calc ((pairR (Term.id A) (nilT A) ⨟ prepend A) ⨟ headOr A)
      ≡ₜ (pairR (Term.id A) (nilT A) ⨟ (prepend A ⨟ headOr A)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (pairR (Term.id A) (nilT A) ⨟
          ((prepend A ⨟ uncons A) ⨟ either (defaultValue A) (fst A A⋆))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (pairR (Term.id A) (nilT A) ⨟
          (inr Ty.unit (A ⊗ A⋆) ⨟ either (defaultValue A) (fst A A⋆))) :=
        PEq.compR _ (PEq.compL _ hpu)
    _ ≡ₜ (pairR (Term.id A) (nilT A) ⨟ fst A A⋆) := PEq.compR _ (inr_either _ _)
    _ ≡ₜ Term.id A := pairR_fst _ _

/-- Composing a product of two terms with a concatenation of two terms. -/
theorem fdot_precomp {X Y X' Y' D : Ty} (f : Term X X') (g : Term Y Y') (x : Term X' D⋆)
    (y : Term Y' D⋆) : (prodF f g ⨟ (x ⊙ y)) ≡ₜ ((f ⨟ x) ⊙ (g ⨟ y)) := by
  calc (prodF f g ⨟ (prodF x y ⨟ binconcat D))
      ≡ₜ ((prodF f g ⨟ prodF x y) ⨟ binconcat D) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (f ⨟ x) (g ⨟ y) ⨟ binconcat D) := PEq.compL _ (PEq.prod_comp _ _ _ _)

/-- The concatenation map of `(A × B)* × A` factors through the concatenation map of the
symmetric variant of splitting. -/
theorem cmL_factor (A B : Ty) :
    cmL A B ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟ cmSplitL A B) := by
  have h2 : (pureT A ⨟ homT (inl A B ⨟ pureT (A ⊕' B))) ≡ₜ
      (inl A B ⨟ pureT (A ⊕' B)) := homT_pure _
  have h1 : (listF (prodF (pureT A) (Term.id B)) ⨟
      homT (homT (inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B)))) ≡ₜ
      homT ((inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) := by
    refine (PEq.symm (homT_precomp _ _)).trans (homT_congr ?_)
    calc (prodF (pureT A) (Term.id B) ⨟
          (homT (inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))))
        ≡ₜ ((pureT A ⨟ homT (inl A B ⨟ pureT (A ⊕' B))) ⊙
            (Term.id B ⨟ (inr A B ⨟ pureT (A ⊕' B)))) := fdot_precomp _ _ _ _
      _ ≡ₜ ((inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) :=
          fdot_congr h2 (PEq.id_comp _)
  exact PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr h1 h2))

/-- The left inverse of the concatenation map of `(A × B)* × A`. -/
def uncmL (A B : Ty) : Term ((A ⊕' B)⋆) ((A ⊗ B)⋆ ⊗ A) :=
  splitLT A B ⨟ prodF (listF (prodF (headOr A) (Term.id B))) (headOr A)

theorem cmL_uncmL (A B : Ty) : (cmL A B ⨟ uncmL A B) ≡ₜ Term.id ((A ⊗ B)⋆ ⊗ A) := by
  have hhead : (listF (prodF (pureT A) (Term.id B)) ⨟
      listF (prodF (headOr A) (Term.id B))) ≡ₜ Term.id ((A ⊗ B)⋆) := by
    calc (listF (prodF (pureT A) (Term.id B)) ⨟ listF (prodF (headOr A) (Term.id B)))
        ≡ₜ listF (prodF (pureT A) (Term.id B) ⨟ prodF (headOr A) (Term.id B)) :=
          PEq.list_comp _ _
      _ ≡ₜ listF (prodF (pureT A ⨟ headOr A) (Term.id B ⨟ Term.id B)) :=
          PEq.congr_listF (PEq.prod_comp _ _ _ _)
      _ ≡ₜ listF (prodF (Term.id A) (Term.id B)) :=
          PEq.congr_listF (PEq.congr_prodF (pureT_headOr A) (PEq.id_comp _))
      _ ≡ₜ listF (Term.id (A ⊗ B)) := PEq.congr_listF (PEq.prod_id A B)
      _ ≡ₜ Term.id ((A ⊗ B)⋆) := PEq.list_id (A ⊗ B)
  calc (cmL A B ⨟ uncmL A B)
      ≡ₜ ((prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟ cmSplitL A B) ⨟
          (splitLT A B ⨟ prodF (listF (prodF (headOr A) (Term.id B))) (headOr A))) :=
        PEq.compL _ (cmL_factor A B)
    _ ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟ (cmSplitL A B ⨟
          (splitLT A B ⨟ prodF (listF (prodF (headOr A) (Term.id B))) (headOr A)))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟ ((cmSplitL A B ⨟
          splitLT A B) ⨟ prodF (listF (prodF (headOr A) (Term.id B))) (headOr A))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟
          (Term.id ((A⋆ ⊗ B)⋆ ⊗ A⋆) ⨟
            prodF (listF (prodF (headOr A) (Term.id B))) (headOr A))) :=
        PEq.compR _ (PEq.compL _ (splitLT_iso A B).2)
    _ ≡ₜ (prodF (listF (prodF (pureT A) (Term.id B))) (pureT A) ⨟
          prodF (listF (prodF (headOr A) (Term.id B))) (headOr A)) :=
        PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ prodF (listF (prodF (pureT A) (Term.id B)) ⨟ listF (prodF (headOr A) (Term.id B)))
          (pureT A ⨟ headOr A) := PEq.prod_comp _ _ _ _
    _ ≡ₜ prodF (Term.id ((A ⊗ B)⋆)) (Term.id A) := PEq.congr_prodF hhead (pureT_headOr A)
    _ ≡ₜ Term.id ((A ⊗ B)⋆ ⊗ A) := PEq.prod_id _ _

/-- The concatenation map of `(A × B)* × A` is provably injective. -/
theorem cmL_injective (A B : Ty) : ProvablyInjective (cmL A B) := ⟨uncmL A B, cmL_uncmL A B⟩

/-- The concatenation map of `A × (B × A)*` is provably injective. -/
theorem cmR_injective (A B : Ty) : ProvablyInjective (cmR A B) := by
  refine ⟨uncmL A B ⨟ shiftR A B, ?_⟩
  calc (cmR A B ⨟ (uncmL A B ⨟ shiftR A B))
      ≡ₜ ((shiftL A B ⨟ cmL A B) ⨟ (uncmL A B ⨟ shiftR A B)) :=
        PEq.compL _ (PEq.symm (shiftL_cm A B))
    _ ≡ₜ (shiftL A B ⨟ (cmL A B ⨟ (uncmL A B ⨟ shiftR A B))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (shiftL A B ⨟ ((cmL A B ⨟ uncmL A B) ⨟ shiftR A B)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (shiftL A B ⨟ (Term.id ((A ⊗ B)⋆ ⊗ A) ⨟ shiftR A B)) :=
        PEq.compR _ (PEq.compL _ (cmL_uncmL A B))
    _ ≡ₜ (shiftL A B ⨟ shiftR A B) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id (A ⊗ (B ⊗ A)⋆) := PEq.shiftL_shiftR A B

end Term

theorem computes_shiftR (A B : Ty) : Computes (Term.shiftR A B) := by
  intro x
  have hcmL : Computes (Term.cmL A B) := computes_of_not_usesHard (Term.cmL A B) rfl
  have hcmR : Computes (Term.cmR A B) := computes_of_not_usesHard (Term.cmR A B) rfl
  have hden : (Term.cmL A B).den x = (Term.cmR A B).den ((Term.shiftR A B).den x) :=
    (congrFun (PEq.sound (PEq.shiftR_content A B)) x).symm
  refine ((cancel _ _).1 _ (Term.cmR A B) (Term.cmR_injective A B)).2 ?_
  calc ((encV ((A ⊗ B)⋆ ⊗ A) x ⨟ Term.shiftR A B) ⨟ Term.cmR A B)
      ≡ₜ (encV ((A ⊗ B)⋆ ⊗ A) x ⨟ (Term.shiftR A B ⨟ Term.cmR A B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (encV ((A ⊗ B)⋆ ⊗ A) x ⨟ Term.cmL A B) :=
        PEq.compR _ (PEq.shiftR_content A B)
    _ ≡ₜ encV ((A ⊕' B)⋆) ((Term.cmL A B).den x) := hcmL x
    _ ≡ₜ encV ((A ⊕' B)⋆) ((Term.cmR A B).den ((Term.shiftR A B).den x)) := by
        rw [hden]
        exact PEq.refl _
    _ ≡ₜ (encV (A ⊗ (B ⊗ A)⋆) ((Term.shiftR A B).den x) ⨟ Term.cmR A B) :=
        PEq.symm (hcmR _)

theorem computes_shiftL (A B : Ty) : Computes (Term.shiftL A B) :=
  Computes.of_inverse (computes_shiftR A B) (PEq.shiftL_shiftR A B) (PEq.shiftR_shiftL A B)

/-! ### The four remaining atomic functions -/

theorem computes_unsplit (A B : Ty) : Computes (Term.unsplit A B) :=
  computes_of_not_usesHard (Term.unsplit A B) rfl

theorem computes_split (A B : Ty) : Computes (Term.split A B) :=
  Computes.of_inverse (computes_unsplit A B) (PEq.split_unsplit A B) (PEq.unsplit_split A B)

/-! The term `unpref`, the inverse of the group prefix multiplication, is built from `shiftL`
and from terms that use none of the atomic functions treated separately. -/

theorem usesHard_constFin : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) →
    usesHard (Term.constFin g) = false
  | 0, _ => rfl
  | (_ + 1), .inl _ => rfl
  | (_ + 1), .inr g => by
      have h : usesHard (Term.constFin g) = false := usesHard_constFin g
      show (usesHard (Term.constFin g) || false) = false
      rw [h]
      rfl

theorem usesHard_caseR : {n : ℕ} → {A B : Ty} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (∀ g, usesHard (t g) = false) → usesHard (Term.caseR t) = false
  | 0, _, _, t, h => by
      show (false || usesHard (t ())) = false
      rw [h ()]
      rfl
  | (n + 1), A, B, t, h => by
      have h1 : usesHard (t (.inl ())) = false := h _
      have h2 : usesHard (Term.caseR (fun g => t (.inr g))) = false :=
        usesHard_caseR _ (fun g => h _)
      show (false || (((false || usesHard (t (.inl ()))) ||
        usesHard (Term.caseR (fun g => t (.inr g)))) || false)) = false
      rw [h1, h2]
      rfl

theorem usesHard_caseL : {n : ℕ} → {A B : Ty} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (∀ g, usesHard (t g) = false) → usesHard (Term.caseL t) = false
  | 0, _, _, t, h => by
      show (false || usesHard (t ())) = false
      rw [h ()]
      rfl
  | (n + 1), A, B, t, h => by
      have h1 : usesHard (t (.inl ())) = false := h _
      have h2 : usesHard (Term.caseL (fun g => t (.inr g))) = false :=
        usesHard_caseL _ (fun g => h _)
      show (false || (((false || usesHard (t (.inl ()))) ||
        usesHard (Term.caseL (fun g => t (.inr g)))) || false)) = false
      rw [h1, h2]
      rfl

theorem usesHard_grepeat (A : Ty) (n : ℕ) : usesHard (Term.grepeat A n) = false := by
  refine usesHard_caseR _ (fun g => ?_)
  show (false || (usesHard (Term.constFin g) ||
    (false || (false || usesHard (Term.constFin g))))) = false
  rw [usesHard_constFin g]
  rfl

theorem usesHard_gdiv (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesHard (Term.gdiv A G) = false := by
  refine usesHard_caseL _ (fun h => ?_)
  refine usesHard_caseL _ (fun g => ?_)
  show (false || (false || usesHard (Term.constFin (letI := G; h⁻¹ * g)))) = false
  rw [usesHard_constFin]
  rfl

theorem computes_unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Computes (Term.unpref A G) := by
  have h1 : Computes (Term.listF (Term.grepeat A n)) :=
    Computes.listF (computes_of_not_usesHard _ (usesHard_grepeat A n))
  have h2 : Computes (Term.listF (Term.assocL (Ty.finAlph n) A (Ty.finAlph n))) :=
    Computes.listF (computes_assocL _ _ _)
  have h3 : Computes (Term.pairL (Term.constFin (letI := G; (1 : ⟦Ty.finAlph n⟧)))
      (Term.id ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n)⋆)) := by
    refine computes_of_not_usesHard _ ?_
    show (false || (usesHard (Term.constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) || false)) =
      false
    rw [usesHard_constFin]
    rfl
  have h4 : Computes (Term.listF (Term.gdiv A G)) :=
    Computes.listF (computes_of_not_usesHard _ (usesHard_gdiv A G))
  exact Computes.comp
    (Computes.comp
      (Computes.comp
        (Computes.comp (Computes.comp h1 h2) h3)
        (computes_shiftL (Ty.finAlph n) (Ty.finAlph n ⊗ A)))
      (computes_fst _ _))
    h4

theorem computes_pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Computes (Term.pref A G) :=
  Computes.of_inverse (computes_unpref A G) (PEq.pref_unpref A G) (PEq.unpref_pref A G)

/-! ### Every term computes on values -/

/-- Every rational term computes on values: composing it with the value representing an
element gives the value representing the image of that element. -/
theorem computes {A B : Ty} (f : Term A B) : Computes f := by
  induction f with
  | comp f g ihf ihg => exact Computes.comp ihf ihg
  | prodF f g ihf ihg => exact Computes.prodF ihf ihg
  | sumF f g ihf ihg => exact Computes.sumF ihf ihg
  | listF f ih => exact Computes.listF ih
  | id A => exact computes_id A
  | inl A B => exact computes_inl A B
  | inr A B => exact computes_inr A B
  | codiag A => exact computes_codiag A
  | fst A B => exact computes_fst A B
  | snd A B => exact computes_snd A B
  | unitR A => exact computes_unitR A
  | unitL A => exact computes_unitL A
  | assocL A B C => exact computes_assocL A B C
  | assocR A B C => exact computes_assocR A B C
  | distR A B C => exact computes_distR A B C
  | distL A B C => exact computes_distL A B C
  | cons A => exact computes_cons A
  | snoc A => exact computes_snoc A
  | concat A => exact computes_concat A
  | uncons A => exact computes_uncons A
  | unsnoc A => exact computes_unsnoc A
  | shiftL A B => exact computes_shiftL A B
  | shiftR A B => exact computes_shiftR A B
  | split A B => exact computes_split A B
  | pref A G => exact computes_pref A G

end Lax149335Proofs

bridge_export Lax149335Proofs
