import Lax149335Proofs.Appendix.ValueAlgebra

/-!
# The homomorphism combinator

The combinator `hom f = f*; concat` sends a term `A → B*` to the unique monoid homomorphism
`A* → B*` that extends it.  This file collects the corresponding provable equalities, which
are used throughout the appendix: `hom f` maps the empty list to the empty list, commutes
with concatenation, extends `f` along `pure`, and composes with another homomorphism as
expected.  As a consequence, the inverse of `split` composed with a homomorphism is computed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

variable {A B : Ty}

/-- Congruence for the concatenation combinator. -/
theorem fdot_congr {X Y : Ty} {x x' : Term X A⋆} {y y' : Term Y A⋆}
    (hx : x ≡ₜ x') (hy : y ≡ₜ y') : (x ⊙ y) ≡ₜ (x' ⊙ y') :=
  PEq.compL _ (PEq.congr_prodF hx hy)

/-- Congruence for the homomorphism combinator. -/
theorem homT_congr {f f' : Term A B⋆} (h : f ≡ₜ f') : homT f ≡ₜ homT f' :=
  PEq.compL _ (PEq.congr_listF h)

/-- A homomorphism maps the empty list to the empty list. -/
theorem homT_nil (f : Term A B⋆) : (nilT A ⨟ homT f) ≡ₜ nilT B := by
  calc (nilT A ⨟ (listF f ⨟ concat B))
      ≡ₜ ((nilT A ⨟ listF f) ⨟ concat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (nilT B⋆ ⨟ concat B) := PEq.compL _ (nilT_natural f)
    _ ≡ₜ nilT B := PEq.nil_concat B

/-- A homomorphism extends the term it is built from. -/
theorem homT_pure (f : Term A B⋆) : (pureT A ⨟ homT f) ≡ₜ f := by
  calc (pureT A ⨟ (listF f ⨟ concat B))
      ≡ₜ ((pureT A ⨟ listF f) ⨟ concat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((f ⨟ pureT B⋆) ⨟ concat B) := PEq.compL _ (PEq.symm (pureT_natural f))
    _ ≡ₜ (f ⨟ (pureT B⋆ ⨟ concat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ Term.id B⋆) := PEq.compR _ (PEq.pure_concat B)
    _ ≡ₜ f := PEq.comp_id f

/-- A homomorphism commutes with binary concatenation. -/
theorem homT_binconcat (f : Term A B⋆) :
    (binconcat A ⨟ homT f) ≡ₜ (prodF (homT f) (homT f) ⨟ binconcat B) := by
  calc (binconcat A ⨟ (listF f ⨟ concat B))
      ≡ₜ ((binconcat A ⨟ listF f) ⨟ concat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (listF f) (listF f) ⨟ binconcat B⋆) ⨟ concat B) :=
        PEq.compL _ (PEq.symm (binconcat_natural f))
    _ ≡ₜ (prodF (listF f) (listF f) ⨟ (binconcat B⋆ ⨟ concat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (listF f) (listF f) ⨟ (prodF (concat B) (concat B) ⨟ binconcat B)) :=
        PEq.compR _ (PEq.binconcat_concat B)
    _ ≡ₜ ((prodF (listF f) (listF f) ⨟ prodF (concat B) (concat B)) ⨟ binconcat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (listF f ⨟ concat B) (listF f ⨟ concat B) ⨟ binconcat B) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)

/-- Composing two homomorphisms. -/
theorem homT_comp {C : Ty} (g : Term A C⋆) (f : Term C B⋆) :
    (homT g ⨟ homT f) ≡ₜ homT (g ⨟ homT f) := by
  calc ((listF g ⨟ concat C) ⨟ (listF f ⨟ concat B))
      ≡ₜ (listF g ⨟ (concat C ⨟ (listF f ⨟ concat B))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF g ⨟ ((concat C ⨟ listF f) ⨟ concat B)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (listF g ⨟ ((listF (listF f) ⨟ concat B⋆) ⨟ concat B)) :=
        PEq.compR _ (PEq.compL _ (PEq.symm (PEq.nat_concat f)))
    _ ≡ₜ (listF g ⨟ ((listF (listF f) ⨟ (listF (concat B) ⨟ concat B)))) := by
        refine PEq.compR _ ?_
        calc ((listF (listF f) ⨟ concat B⋆) ⨟ concat B)
            ≡ₜ (listF (listF f) ⨟ (concat B⋆ ⨟ concat B)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (listF (listF f) ⨟ (listF (concat B) ⨟ concat B)) :=
              PEq.compR _ (PEq.symm (PEq.concat_concat B))
    _ ≡ₜ (listF g ⨟ ((listF (listF f) ⨟ listF (concat B)) ⨟ concat B)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (listF g ⨟ (listF (listF f ⨟ concat B) ⨟ concat B)) :=
        PEq.compR _ (PEq.compL _ (PEq.list_comp _ _))
    _ ≡ₜ ((listF g ⨟ listF (listF f ⨟ concat B)) ⨟ concat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (listF (g ⨟ (listF f ⨟ concat B)) ⨟ concat B) := PEq.compL _ (PEq.list_comp _ _)

/-- Pre-composing inside a homomorphism. -/
theorem homT_precomp {X Y : Ty} (g : Term X Y) (f : Term Y B⋆) :
    homT (g ⨟ f) ≡ₜ (listF g ⨟ homT f) := by
  calc (listF (g ⨟ f) ⨟ concat B)
      ≡ₜ ((listF g ⨟ listF f) ⨟ concat B) := PEq.compL _ (PEq.symm (PEq.list_comp _ _))
    _ ≡ₜ (listF g ⨟ (listF f ⨟ concat B)) := PEq.comp_assoc _ _ _

/-- A homomorphism distributes over the concatenation combinator. -/
theorem fdot_comp_homT {X Y : Ty} (x : Term X A⋆) (y : Term Y A⋆) (f : Term A B⋆) :
    ((x ⊙ y) ⨟ homT f) ≡ₜ ((x ⨟ homT f) ⊙ (y ⨟ homT f)) := by
  calc ((prodF x y ⨟ binconcat A) ⨟ homT f)
      ≡ₜ (prodF x y ⨟ (binconcat A ⨟ homT f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF x y ⨟ (prodF (homT f) (homT f) ⨟ binconcat B)) :=
        PEq.compR _ (homT_binconcat f)
    _ ≡ₜ ((prodF x y ⨟ prodF (homT f) (homT f)) ⨟ binconcat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (x ⨟ homT f) (y ⨟ homT f) ⨟ binconcat B) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)

/-- Concatenating with a constantly empty first component is the second projection. -/
theorem prodF_nilconst_binconcat_left {X Y : Ty} (f : Term X A⋆) :
    (prodF (toUnit Y ⨟ nilT A) f ⨟ binconcat A) ≡ₜ (snd Y X ⨟ f) := by
  calc (prodF (toUnit Y ⨟ nilT A) f ⨟ binconcat A)
      ≡ₜ ((prodF (toUnit Y) f ⨟ prodF (nilT A) (Term.id A⋆)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))))
    _ ≡ₜ (prodF (toUnit Y) f ⨟ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (toUnit Y) f ⨟ snd Ty.unit A⋆) := PEq.compR _ (binconcat_nil_snd A)
    _ ≡ₜ (snd Y X ⨟ f) := PEq.nat_snd _ _

/-- The homomorphism extending a constantly empty term is constantly empty. -/
theorem homT_nilconst (E : Ty) (B : Ty) :
    homT (toUnit E ⨟ nilT B) ≡ₜ (toUnit E⋆ ⨟ nilT B) := by
  calc (listF (toUnit E ⨟ nilT B) ⨟ concat B)
      ≡ₜ ((listF (toUnit E) ⨟ listF (nilT B)) ⨟ concat B) :=
        PEq.compL _ (PEq.symm (PEq.list_comp _ _))
    _ ≡ₜ (listF (toUnit E) ⨟ (listF (nilT B) ⨟ concat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF (toUnit E) ⨟ (toUnit Ty.unit⋆ ⨟ nilT B)) :=
        PEq.compR _ (PEq.nil_map_concat B)
    _ ≡ₜ ((listF (toUnit E) ⨟ toUnit Ty.unit⋆) ⨟ nilT B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (toUnit E⋆ ⨟ nilT B) :=
        PEq.compL _ (PEq.unit_unique (listF (toUnit E) ⨟ toUnit Ty.unit⋆) (toUnit E⋆))

/-- Composing the inverse of `split` with a homomorphism. -/
theorem unsplit_comp_homT {E N : Ty} (f : Term (E ⊕' N) B⋆) :
    (unsplit E N ⨟ homT f) ≡ₜ
      (homT (inl E N ⨟ f) ⊙ homT ((inr E N ⨟ f) ⊙ homT (inl E N ⨟ f))) := by
  have hm1 : ((inl E N ⨟ pureT (E ⊕' N)) ⨟ homT f) ≡ₜ (inl E N ⨟ f) := by
    calc ((inl E N ⨟ pureT (E ⊕' N)) ⨟ homT f)
        ≡ₜ (inl E N ⨟ (pureT (E ⊕' N) ⨟ homT f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inl E N ⨟ f) := PEq.compR _ (homT_pure f)
  have hm2 : ((inr E N ⨟ pureT (E ⊕' N)) ⨟ homT f) ≡ₜ (inr E N ⨟ f) := by
    calc ((inr E N ⨟ pureT (E ⊕' N)) ⨟ homT f)
        ≡ₜ (inr E N ⨟ (pureT (E ⊕' N) ⨟ homT f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr E N ⨟ f) := PEq.compR _ (homT_pure f)
  calc ((homT (inl E N ⨟ pureT (E ⊕' N)) ⊙
          homT ((inr E N ⨟ pureT (E ⊕' N)) ⊙ homT (inl E N ⨟ pureT (E ⊕' N)))) ⨟ homT f)
      ≡ₜ ((homT (inl E N ⨟ pureT (E ⊕' N)) ⨟ homT f) ⊙
          (homT ((inr E N ⨟ pureT (E ⊕' N)) ⊙ homT (inl E N ⨟ pureT (E ⊕' N))) ⨟ homT f)) :=
        fdot_comp_homT _ _ f
    _ ≡ₜ (homT ((inl E N ⨟ pureT (E ⊕' N)) ⨟ homT f) ⊙
          homT (((inr E N ⨟ pureT (E ⊕' N)) ⊙ homT (inl E N ⨟ pureT (E ⊕' N))) ⨟ homT f)) :=
        fdot_congr (homT_comp _ _) (homT_comp _ _)
    _ ≡ₜ (homT (inl E N ⨟ f) ⊙
          homT (((inr E N ⨟ pureT (E ⊕' N)) ⨟ homT f) ⊙
            (homT (inl E N ⨟ pureT (E ⊕' N)) ⨟ homT f))) :=
        fdot_congr (homT_congr hm1) (homT_congr (fdot_comp_homT _ _ f))
    _ ≡ₜ (homT (inl E N ⨟ f) ⊙ homT ((inr E N ⨟ f) ⊙ homT (inl E N ⨟ f))) :=
        fdot_congr (PEq.refl _)
          (homT_congr (fdot_congr hm2 ((homT_comp _ _).trans (homT_congr hm1))))

/-- Post-composing a concatenation of two terms with the functorial action on lists. -/
theorem fdot_comp_listF {X Y D E : Ty} (x : Term X D⋆) (y : Term Y D⋆) (h : Term D E) :
    ((x ⊙ y) ⨟ listF h) ≡ₜ ((x ⨟ listF h) ⊙ (y ⨟ listF h)) := by
  calc ((prodF x y ⨟ binconcat D) ⨟ listF h)
      ≡ₜ (prodF x y ⨟ (binconcat D ⨟ listF h)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF x y ⨟ (prodF (listF h) (listF h) ⨟ binconcat E)) :=
        PEq.compR _ (PEq.symm (binconcat_natural h))
    _ ≡ₜ ((prodF x y ⨟ prodF (listF h) (listF h)) ⨟ binconcat E) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (x ⨟ listF h) (y ⨟ listF h) ⨟ binconcat E) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)

/-- Post-composing a homomorphism with the functorial action on lists. -/
theorem homT_comp_listF {A D E : Ty} (c : Term A D⋆) (h : Term D E) :
    (homT c ⨟ listF h) ≡ₜ homT (c ⨟ listF h) := by
  calc ((listF c ⨟ concat D) ⨟ listF h)
      ≡ₜ (listF c ⨟ (concat D ⨟ listF h)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF c ⨟ (listF (listF h) ⨟ concat E)) := PEq.compR _ (PEq.symm (PEq.nat_concat h))
    _ ≡ₜ ((listF c ⨟ listF (listF h)) ⨟ concat E) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (listF (c ⨟ listF h) ⨟ concat E) := PEq.compL _ (PEq.list_comp _ _)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
