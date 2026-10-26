import Lax149335Proofs.Appendix.Drops.InjectiveTypes

/-!
# Letters, contents, and the rebracketing properties of `block` and `shift`

Auxiliary terms and equations about the *content* of a type, i.e. the list of the letters it
carries, read in `(S + T)*`.  They are used by the appendix section on `block`
(`Lax149335Proofs.Appendix.Drops.BlockCollect` and the files that follow it).

* `Lax149335Proofs.sLetter` and `Lax149335Proofs.tLetter` are the one-letter words of `(S + T)*`;
* `Lax149335Proofs.pairContent` and `Lax149335Proofs.shiftContent` are the concatenation maps of the types
  `(S × T)*` and `1 + S × (T × S)* × T` into `(S + T)*`;
* `Lax149335Proofs.block_content` and `Lax149335Proofs.shift_content` say that the prime lifts `block` and
  `shift` do not change the content, in the form in which the appendix uses it: the content
  of a letter may be an arbitrary word.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

/-! ### Letters and contents -/

/-- The one-letter word consisting of a letter of `S`, seen in `(S + T)*`. -/
def sLetter (S T : Ty) : Term S ((S ⊕' T)⋆) := inl S T ⨟ pureT (S ⊕' T)

/-- The one-letter word consisting of a letter of `T`, seen in `(S + T)*`. -/
def tLetter (S T : Ty) : Term T ((S ⊕' T)⋆) := inr S T ⨟ pureT (S ⊕' T)

/-- The concatenation map `(S × T)* ↣ (S + T)*`. -/
def pairContent (S T : Ty) : Term ((S ⊗ T)⋆) ((S ⊕' T)⋆) :=
  TyF2.concatMap (.list (.prod .p1 .p2)) S T

/-- The concatenation map of the codomain of `shift` into `(S + T)*`. -/
def shiftContent (S T : Ty) : Term (Ty.unit ⊕' (S ⊗ ((T ⊗ S)⋆ ⊗ T))) ((S ⊕' T)⋆) :=
  TyF2.concatMap (.sum .unit (.prod .p1 (.prod (.list (.prod .p2 .p1)) .p2))) S T

/-! ### Re-associating a concatenation -/

/-- Re-associating a concatenation, from right to left. -/
theorem fdot_assoc' {X Y Z D : Ty} (c₁ : Term X D⋆) (c₂ : Term Y D⋆) (c₃ : Term Z D⋆) :
    (c₁ ⊙ (c₂ ⊙ c₃)) ≡ₜ (assocL X Y Z ⨟ ((c₁ ⊙ c₂) ⊙ c₃)) := by
  calc (c₁ ⊙ (c₂ ⊙ c₃))
      ≡ₜ (Term.id (X ⊗ (Y ⊗ Z)) ⨟ (c₁ ⊙ (c₂ ⊙ c₃))) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocL X Y Z ⨟ assocR X Y Z) ⨟ (c₁ ⊙ (c₂ ⊙ c₃))) :=
        PEq.compL _ (PEq.symm (PEq.assocL_assocR X Y Z))
    _ ≡ₜ (assocL X Y Z ⨟ (assocR X Y Z ⨟ (c₁ ⊙ (c₂ ⊙ c₃)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL X Y Z ⨟ ((c₁ ⊙ c₂) ⊙ c₃)) := PEq.compR _ (PEq.symm (fdot_assoc _ _ _))

/-! ### The content of `block` and of `shift`

The two prime lifts that the argument uses are rebracketings, and they stay rebracketings
when the letters are replaced by arbitrary contents: this is obtained from the rebracketing
properties for the letters of `A + B`, by post-composing with the homomorphism that maps a
letter to its content. -/

/-- **`block` does not change the content.** -/
theorem block_content {A B D : Ty} (u : Term A D⋆) (v : Term B D⋆) :
    (Term.block A B ⨟ (Term.homT u ⊙ Term.homT (v ⊙ Term.homT u))) ≡ₜ
      Term.homT (Term.either u v) := by
  set h : Term (A ⊕' B) D⋆ := Term.either u v with hh
  set iL : Term A ((A ⊕' B)⋆) := inl A B ⨟ pureT (A ⊕' B) with hiL
  set iR : Term B ((A ⊕' B)⋆) := inr A B ⨟ pureT (A ⊕' B) with hiR
  have hu : (iL ⨟ Term.homT h) ≡ₜ u :=
    (PEq.comp_assoc _ _ _).trans ((PEq.compR _ (homT_pure h)).trans (inl_either u v))
  have hv : (iR ⨟ Term.homT h) ≡ₜ v :=
    (PEq.comp_assoc _ _ _).trans ((PEq.compR _ (homT_pure h)).trans (inr_either u v))
  have hunblock : (Term.unblock A B ⨟ Term.homT h) ≡ₜ
      (Term.homT u ⊙ Term.homT (v ⊙ Term.homT u)) := by
    calc ((Term.homT iL ⊙ Term.homT (iR ⊙ Term.homT iL)) ⨟ Term.homT h)
        ≡ₜ ((Term.homT iL ⨟ Term.homT h) ⊙ (Term.homT (iR ⊙ Term.homT iL) ⨟ Term.homT h)) :=
          fdot_comp_homT _ _ _
      _ ≡ₜ (Term.homT (iL ⨟ Term.homT h) ⊙ Term.homT ((iR ⊙ Term.homT iL) ⨟ Term.homT h)) :=
          fdot_congr (homT_comp _ _) (homT_comp _ _)
      _ ≡ₜ (Term.homT u ⊙ Term.homT ((iR ⨟ Term.homT h) ⊙ (Term.homT iL ⨟ Term.homT h))) :=
          fdot_congr (homT_congr hu) (homT_congr (fdot_comp_homT _ _ _))
      _ ≡ₜ (Term.homT u ⊙ Term.homT (v ⊙ Term.homT (iL ⨟ Term.homT h))) :=
          fdot_congr (PEq.refl _) (homT_congr (fdot_congr hv (homT_comp _ _)))
      _ ≡ₜ (Term.homT u ⊙ Term.homT (v ⊙ Term.homT u)) :=
          fdot_congr (PEq.refl _) (homT_congr (fdot_congr (PEq.refl _) (homT_congr hu)))
  calc (Term.block A B ⨟ (Term.homT u ⊙ Term.homT (v ⊙ Term.homT u)))
      ≡ₜ (Term.block A B ⨟ (Term.unblock A B ⨟ Term.homT h)) :=
        PEq.compR _ (PEq.symm hunblock)
    _ ≡ₜ ((Term.block A B ⨟ Term.unblock A B) ⨟ Term.homT h) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((A ⊕' B)⋆) ⨟ Term.homT h) := PEq.compL _ (PEq.block_unblock A B)
    _ ≡ₜ Term.homT h := PEq.id_comp _

/-- **`shift` does not change the content.** -/
theorem shift_content {X K D : Ty} (u : Term X D⋆) (v : Term K D⋆) :
    (Term.shift X K ⨟
        Term.either (nilT D) (u ⊙ (Term.homT (v ⊙ u) ⊙ v))) ≡ₜ Term.homT (u ⊙ v) := by
  set h : Term (X ⊕' K) D⋆ := Term.either u v with hh
  set iL : Term X ((X ⊕' K)⋆) := inl X K ⨟ pureT (X ⊕' K) with hiL
  set iR : Term K ((X ⊕' K)⋆) := inr X K ⨟ pureT (X ⊕' K) with hiR
  have hu : (iL ⨟ Term.homT h) ≡ₜ u :=
    (PEq.comp_assoc _ _ _).trans ((PEq.compR _ (homT_pure h)).trans (inl_either u v))
  have hv : (iR ⨟ Term.homT h) ≡ₜ v :=
    (PEq.comp_assoc _ _ _).trans ((PEq.compR _ (homT_pure h)).trans (inr_either u v))
  have hunshift : (Term.unshift X K ⨟ Term.homT (u ⊙ v)) ≡ₜ
      Term.either (nilT D) (u ⊙ (Term.homT (v ⊙ u) ⊙ v)) := by
    have hsrc : (Term.homT (iL ⊙ iR) ⨟ Term.homT h) ≡ₜ Term.homT (u ⊙ v) :=
      (homT_comp _ _).trans (homT_congr ((fdot_comp_homT _ _ _).trans (fdot_congr hu hv)))
    calc (Term.unshift X K ⨟ Term.homT (u ⊙ v))
        ≡ₜ (Term.unshift X K ⨟ (Term.homT (iL ⊙ iR) ⨟ Term.homT h)) :=
          PEq.compR _ (PEq.symm hsrc)
      _ ≡ₜ ((Term.unshift X K ⨟ Term.homT (iL ⊙ iR)) ⨟ Term.homT h) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.either (nilT (X ⊕' K)) (iL ⊙ (Term.homT (iR ⊙ iL) ⊙ iR)) ⨟ Term.homT h) :=
          PEq.compL _ (Term.unshift_rebracketing X K)
      _ ≡ₜ Term.either (nilT (X ⊕' K) ⨟ Term.homT h)
            ((iL ⊙ (Term.homT (iR ⊙ iL) ⊙ iR)) ⨟ Term.homT h) := either_comp _ _ _
      _ ≡ₜ Term.either (nilT D)
            ((iL ⨟ Term.homT h) ⊙ ((Term.homT (iR ⊙ iL) ⊙ iR) ⨟ Term.homT h)) :=
          either_congr (homT_nil h) (fdot_comp_homT _ _ _)
      _ ≡ₜ Term.either (nilT D)
            (u ⊙ ((Term.homT (iR ⊙ iL) ⨟ Term.homT h) ⊙ (iR ⨟ Term.homT h))) :=
          either_congr (PEq.refl _) (fdot_congr hu (fdot_comp_homT _ _ _))
      _ ≡ₜ Term.either (nilT D) (u ⊙ (Term.homT ((iR ⊙ iL) ⨟ Term.homT h) ⊙ v)) :=
          either_congr (PEq.refl _) (fdot_congr (PEq.refl _) (fdot_congr (homT_comp _ _) hv))
      _ ≡ₜ Term.either (nilT D) (u ⊙ (Term.homT (v ⊙ u) ⊙ v)) :=
          either_congr (PEq.refl _) (fdot_congr (PEq.refl _)
            (fdot_congr (homT_congr ((fdot_comp_homT _ _ _).trans (fdot_congr hv hu)))
              (PEq.refl _)))
  calc (Term.shift X K ⨟ Term.either (nilT D) (u ⊙ (Term.homT (v ⊙ u) ⊙ v)))
      ≡ₜ (Term.shift X K ⨟ (Term.unshift X K ⨟ Term.homT (u ⊙ v))) :=
        PEq.compR _ (PEq.symm hunshift)
    _ ≡ₜ ((Term.shift X K ⨟ Term.unshift X K) ⨟ Term.homT (u ⊙ v)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((X ⊗ K)⋆) ⨟ Term.homT (u ⊙ v)) := PEq.compL _ (Term.shift_unshift X K)
    _ ≡ₜ Term.homT (u ⊙ v) := PEq.id_comp _

/-! ### `unshift` does not change the content -/

/-- `unshift` does not change the content. -/
theorem Term.unshift_pairContent (S T : Ty) :
    (Term.unshift S T ⨟ pairContent S T) ≡ₜ shiftContent S T := by
  calc (Term.unshift S T ⨟ pairContent S T)
      ≡ₜ (Term.unshift S T ⨟ (Term.shift S T ⨟ shiftContent S T)) :=
        PEq.compR _ (PEq.symm (Term.shift_rebracketing S T))
    _ ≡ₜ ((Term.unshift S T ⨟ Term.shift S T) ⨟ shiftContent S T) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (Ty.unit ⊕' (S ⊗ ((T ⊗ S)⋆ ⊗ T))) ⨟ shiftContent S T) :=
        PEq.compL _ (Term.unshift_shift S T)
    _ ≡ₜ shiftContent S T := PEq.id_comp _

end Lax149335Proofs

bridge_export Lax149335Proofs
