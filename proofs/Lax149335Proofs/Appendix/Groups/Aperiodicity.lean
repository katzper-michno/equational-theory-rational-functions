import Lax149335Proofs.Appendix.Groups.ConstFin
import Lax149335Proofs.Appendix.ValueNormalisation

/-!
# Denotations and aperiodicity of the derived terms

Two toolkits that the group section of the appendix uses throughout:

* the denotation of the value `encV A x` that represents an element `x` of a type
  (`Lax149335Proofs.Term.den_encV`), together with the denotations of `shiftL` and `append` in the
  point-free form in which the `simp` set wants them;
* aperiodicity of the derived terms, i.e. the statement that they do not use the group prefix
  multiplication (`Lax149335Proofs.Term.usesPref`).  This is what lets the equational proofs of the
  section appeal to completeness in the aperiodic case (Corollary 7.6).  The two case
  combinators over a finite alphabet, `caseL` and `caseR`, are covered as well, and with them
  the unprefixing operation `unpref`, which is built from them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Values: denotation and aperiodicity -/

@[simp] theorem den_encV : (A : Ty) → (x : ⟦A⟧) → (encV A x).den () = x
  | .unit, x => by cases x; rfl
  | .prod A B, x => by
      show ((encV A x.1).den (), (encV B x.2).den ()) = x
      rw [den_encV A x.1, den_encV B x.2]
      rfl
  | .sum A B, .inl a => by
      show Sum.inl ((encV A a).den ()) = Sum.inl a
      rw [den_encV A a]
  | .sum A B, .inr b => by
      show Sum.inr ((encV B b).den ()) = Sum.inr b
      rw [den_encV B b]
  | .list A, l => by
      induction l with
      | nil => rfl
      | cons a t ih =>
          rw [encV_cons]
          simp only [den_dotL, den_sing, ih, den_encV A a]
          rfl

/-! ### Aperiodicity of the derived terms -/

@[simp] theorem usesPref_toUnit (A : Ty) : usesPref (toUnit A) = false := rfl

@[simp] theorem usesPref_nilT (A : Ty) : usesPref (nilT A) = false := rfl

@[simp] theorem usesPref_prepend (A : Ty) : usesPref (prepend A) = false := rfl

@[simp] theorem usesPref_append (A : Ty) : usesPref (append A) = false := rfl

@[simp] theorem usesPref_pureT (A : Ty) : usesPref (pureT A) = false := rfl

@[simp] theorem usesPref_binconcat (A : Ty) : usesPref (binconcat A) = false := rfl

@[simp] theorem usesPref_either {A₁ A₂ B : Ty} (f : Term A₁ B) (g : Term A₂ B) :
    usesPref (either f g) = (usesPref f || usesPref g) := by
  simp [either, usesPref]

@[simp] theorem usesPref_pairL {A B C : Ty} (v : Value C) (f : Term A B) :
    usesPref (pairL v f) = (usesPref v || usesPref f) := by
  simp [pairL, usesPref]

@[simp] theorem usesPref_pairR {A B C : Ty} (f : Term A B) (v : Value C) :
    usesPref (pairR f v) = (usesPref f || usesPref v) := by
  simp [pairR, usesPref]

/-! ### Terms out of a finite alphabet: denotation and aperiodicity -/

theorem usesPref_caseL {A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (∀ g, usesPref (t g) = false) → usesPref (caseL t) = false
  | 0, t, h => by simp [caseL, usesPref, h ()]
  | (n + 1), t, h => by
      simp [caseL, either, usesPref, h (.inl ()),
        usesPref_caseL (fun g => t (.inr g)) (fun g => h (.inr g))]

/-! ### Splitting the decorated list into blocks -/

@[simp] theorem den_shiftL_fun (A B : Ty) :
    (shiftL A B).den = fun x => shiftLDen x.1 x.2 := rfl

@[simp] theorem den_append_fun (A : Ty) :
    (append A).den = fun x => x.1 ++ [x.2] := rfl

/-! ### Aperiodicity of the unprefixing operation -/

theorem usesPref_caseR {A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (∀ g, usesPref (t g) = false) → usesPref (caseR t) = false
  | 0, t, h => by simp [caseR, usesPref, h ()]
  | (_ + 1), t, h => by
      simp [caseR, usesPref, h (.inl ()),
        usesPref_caseR (fun g => t (.inr g)) (fun g => h (.inr g))]

@[simp] theorem usesPref_grepeat (A : Ty) (n : ℕ) : usesPref (grepeat A n) = false := by
  refine usesPref_caseR _ (fun g => ?_)
  simp [usesPref, usesPref_constFin]

@[simp] theorem usesPref_gdiv (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (gdiv A G) = false := by
  refine usesPref_caseL _ (fun h => usesPref_caseL _ (fun g => ?_))
  simp [usesPref, usesPref_constFin]

@[simp] theorem usesPref_unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (unpref A G) = false := by
  simp [unpref, usesPref, usesPref_constFin]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
