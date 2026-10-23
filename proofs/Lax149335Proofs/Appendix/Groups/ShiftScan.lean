import Lax149335Proofs.SimpleCompleteness.Statements
import Lax149335Proofs.Appendix.Groups.FiniteAlphabet

/-!
# Running `shiftL` over a concatenation (appendix, *Unprefixing*)

The group prefix multiplication is inverted by the term `unpref`, which is defined using
`shiftL`: reading `shiftL X Y : X ⊗ (Y ⊗ X)* → (X ⊗ Y)* ⊗ X` as a *scan*, its input is a
carry `X` together with a list of pairs, and its output is the list of pairs, each shifted by
one position, together with the final carry.

This file develops the two facts about such scans that the appendix uses when it distributes
unprefixing over concatenation:

* `Lax149335Proofs.Term.scanL_fdot` — running a scan over the concatenation of two lists is the same
  as running it over the first list and then, with the resulting carry, over the second one;
* `Lax149335Proofs.Term.scanL_homT` — the same for the concatenation of a list of lists.

Both are stated in the situation that occurs in the appendix, in which the carry produced by
each of the parts is a *value*; that is what makes the composition expressible, since the
system has no diagonal and therefore no way to duplicate a carry.  The proofs cancel the
provably injective concatenation map `cmL` of Axiom 15, so that everything is reduced to an
identity between contents of lists; for the second lemma, that identity is exactly the
conjugacy rule for syntactic conjugates (Lemma 6.2).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Contents of lists of pairs -/

/-- The content of a list of pairs `(Y ⊗ X)*`, as a list over `X + Y`. -/
def cListYX (X Y : Ty) : Term ((Y ⊗ X)⋆) ((X ⊕' Y)⋆) :=
  homT ((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))

/-- The content of a list of pairs `(X ⊗ Y)*`, as a list over `X + Y`. -/
def cListXY (X Y : Ty) : Term ((X ⊗ Y)⋆) ((X ⊕' Y)⋆) :=
  homT ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y)))

theorem cmR_eq (X Y : Ty) :
    cmR X Y = ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ cListYX X Y) := rfl

theorem cmL_eq (X Y : Ty) :
    cmL X Y = (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y))) := rfl

/-- The singleton list value `[inl v]`. -/
def inlV {X : Ty} (v : Value X) (Y : Ty) : Value ((X ⊕' Y)⋆) := sing (v ⨟ inl X Y)

/-- Running the scan `shiftL` with the carry `v`. -/
def scanL (X Y : Ty) (v : Value X) {D : Ty} (m : Term D ((Y ⊗ X)⋆)) :
    Term D ((X ⊗ Y)⋆ ⊗ X) :=
  pairL v m ⨟ shiftL X Y

/-! ### Moving values in and out of the concatenation combinator -/

/-- Coherence: inserting a unit on the left of a product and re-associating. -/
theorem unitL_prodF_assocR (D E : Ty) :
    (prodF (unitL D) (Term.id E) ⨟ assocR Ty.unit D E) ≡ₜ unitL (D ⊗ E) := by
  refine ((cancel _ _).1 _ (snd Ty.unit (D ⊗ E))
    ⟨unitL (D ⊗ E), PEq.snd_unitL (D ⊗ E)⟩).2 ?_
  calc ((prodF (unitL D) (Term.id E) ⨟ assocR Ty.unit D E) ⨟ snd Ty.unit (D ⊗ E))
      ≡ₜ (prodF (unitL D) (Term.id E) ⨟ (assocR Ty.unit D E ⨟ snd Ty.unit (D ⊗ E))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (unitL D) (Term.id E) ⨟ prodF (snd Ty.unit D) (Term.id E)) :=
        PEq.compR _ (Term.assocR_snd _ _ _)
    _ ≡ₜ prodF (unitL D ⨟ snd Ty.unit D) (Term.id E ⨟ Term.id E) := PEq.prod_comp _ _ _ _
    _ ≡ₜ prodF (Term.id D) (Term.id E) :=
        PEq.congr_prodF (PEq.unitL_snd D) (PEq.id_comp _)
    _ ≡ₜ Term.id (D ⊗ E) := PEq.prod_id _ _
    _ ≡ₜ (unitL (D ⊗ E) ⨟ snd Ty.unit (D ⊗ E)) := PEq.symm (PEq.unitL_snd _)

/-- A value prepended to the left factor of a concatenation can be prepended to the whole
concatenation. -/
theorem dotL_fdot {D E B : Ty} (w : Value B⋆) (f : Term D B⋆) (g : Term E B⋆) :
    ((dotL w f) ⊙ g) ≡ₜ dotL w (f ⊙ g) := by
  have hL : ((dotL w f) ⊙ g) ≡ₜ
      ((prodF (unitL D) (Term.id E) ⨟ assocR Ty.unit D E) ⨟ (w ⊙ (f ⊙ g))) := by
    calc (prodF ((unitL D ⨟ prodF w f) ⨟ binconcat B) g ⨟ binconcat B)
        ≡ₜ (prodF (unitL D ⨟ (w ⊙ f)) (Term.id E ⨟ g) ⨟ binconcat B) :=
          PEq.compL _ (PEq.congr_prodF (PEq.comp_assoc _ _ _) (PEq.symm (PEq.id_comp _)))
      _ ≡ₜ ((prodF (unitL D) (Term.id E) ⨟ prodF (w ⊙ f) g) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (prodF (unitL D) (Term.id E) ⨟ ((w ⊙ f) ⊙ g)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (unitL D) (Term.id E) ⨟ (assocR Ty.unit D E ⨟ (w ⊙ (f ⊙ g)))) :=
          PEq.compR _ (fdot_assoc _ _ _)
      _ ≡ₜ ((prodF (unitL D) (Term.id E) ⨟ assocR Ty.unit D E) ⨟ (w ⊙ (f ⊙ g))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
  refine hL.trans ?_
  calc ((prodF (unitL D) (Term.id E) ⨟ assocR Ty.unit D E) ⨟ (w ⊙ (f ⊙ g)))
      ≡ₜ (unitL (D ⊗ E) ⨟ (w ⊙ (f ⊙ g))) := PEq.compL _ (unitL_prodF_assocR D E)
    _ ≡ₜ dotL w (f ⊙ g) := PEq.symm (PEq.comp_assoc _ _ _)

/-- A value appended to the right factor of a concatenation can be appended to the whole
concatenation. -/
theorem dotR_fdot {D E B : Ty} (f : Term D B⋆) (g : Term E B⋆) (w : Value B⋆) :
    (f ⊙ (dotR g w)) ≡ₜ dotR (f ⊙ g) w := by
  have hL : (f ⊙ (dotR g w)) ≡ₜ
      ((prodF (Term.id D) (unitR E) ⨟ assocL D E Ty.unit) ⨟ ((f ⊙ g) ⊙ w)) := by
    calc (prodF f ((unitR E ⨟ prodF g w) ⨟ binconcat B) ⨟ binconcat B)
        ≡ₜ (prodF (Term.id D ⨟ f) (unitR E ⨟ (g ⊙ w)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((prodF (Term.id D) (unitR E) ⨟ prodF f (g ⊙ w)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (prodF (Term.id D) (unitR E) ⨟ (f ⊙ (g ⊙ w))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id D) (unitR E) ⨟ (assocL D E Ty.unit ⨟ ((f ⊙ g) ⊙ w))) := by
          refine PEq.compR _ ?_
          calc (f ⊙ (g ⊙ w))
              ≡ₜ (Term.id (D ⊗ (E ⊗ Ty.unit)) ⨟ (f ⊙ (g ⊙ w))) := PEq.symm (PEq.id_comp _)
            _ ≡ₜ ((assocL D E Ty.unit ⨟ assocR D E Ty.unit) ⨟ (f ⊙ (g ⊙ w))) :=
                PEq.compL _ (PEq.symm (PEq.assocL_assocR _ _ _))
            _ ≡ₜ (assocL D E Ty.unit ⨟ (assocR D E Ty.unit ⨟ (f ⊙ (g ⊙ w)))) :=
                PEq.comp_assoc _ _ _
            _ ≡ₜ (assocL D E Ty.unit ⨟ ((f ⊙ g) ⊙ w)) :=
                PEq.compR _ (PEq.symm (fdot_assoc _ _ _))
      _ ≡ₜ ((prodF (Term.id D) (unitR E) ⨟ assocL D E Ty.unit) ⨟ ((f ⊙ g) ⊙ w)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
  refine hL.trans ?_
  calc ((prodF (Term.id D) (unitR E) ⨟ assocL D E Ty.unit) ⨟ ((f ⊙ g) ⊙ w))
      ≡ₜ (unitR (D ⊗ E) ⨟ ((f ⊙ g) ⊙ w)) := PEq.compL _ (PEq.symm (Term.unitR_prod D E))
    _ ≡ₜ dotR (f ⊙ g) w := PEq.symm (PEq.comp_assoc _ _ _)

/-! ### The content of a scan -/

/-- The content of the input of a scan. -/
theorem scanL_cmL {X Y D : Ty} (v : Value X) (m : Term D ((Y ⊗ X)⋆)) :
    (scanL X Y v m ⨟ cmL X Y) ≡ₜ dotL (inlV v Y) (m ⨟ cListYX X Y) := by
  calc ((pairL v m ⨟ shiftL X Y) ⨟ cmL X Y)
      ≡ₜ (pairL v m ⨟ (shiftL X Y ⨟ cmL X Y)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (pairL v m ⨟ cmR X Y) := PEq.compR _ (shiftL_cm X Y)
    _ ≡ₜ dotL (inlV v Y) (m ⨟ cListYX X Y) := by
        rw [cmR_eq]
        calc ((unitL D ⨟ prodF v m) ⨟
              (prodF (inl X Y ⨟ pureT (X ⊕' Y)) (cListYX X Y) ⨟ binconcat (X ⊕' Y)))
            ≡ₜ (((unitL D ⨟ prodF v m) ⨟
                prodF (inl X Y ⨟ pureT (X ⊕' Y)) (cListYX X Y)) ⨟ binconcat (X ⊕' Y)) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((unitL D ⨟ (prodF v m ⨟
                prodF (inl X Y ⨟ pureT (X ⊕' Y)) (cListYX X Y))) ⨟ binconcat (X ⊕' Y)) :=
              PEq.compL _ (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((unitL D ⨟ prodF (v ⨟ (inl X Y ⨟ pureT (X ⊕' Y)))
                (m ⨟ cListYX X Y)) ⨟ binconcat (X ⊕' Y)) :=
              PEq.compL _ (PEq.compR _ (PEq.prod_comp _ _ _ _))
          _ ≡ₜ ((unitL D ⨟ prodF (inlV v Y) (m ⨟ cListYX X Y)) ⨟ binconcat (X ⊕' Y)) :=
              PEq.compL _ (PEq.compR _ (PEq.congr_prodF
                (PEq.symm (PEq.comp_assoc _ _ _)) (PEq.refl _)))

/-- The content of the output of a scan whose final carry is a value. -/
theorem pairR_cmL {X Y D : Ty} (p : Term D ((X ⊗ Y)⋆)) (v : Value X) :
    (pairR p v ⨟ cmL X Y) ≡ₜ dotR (p ⨟ cListXY X Y) (inlV v Y) := by
  rw [cmL_eq]
  calc ((unitR D ⨟ prodF p v) ⨟
        (prodF (cListXY X Y) (inl X Y ⨟ pureT (X ⊕' Y)) ⨟ binconcat (X ⊕' Y)))
      ≡ₜ (((unitR D ⨟ prodF p v) ⨟
          prodF (cListXY X Y) (inl X Y ⨟ pureT (X ⊕' Y))) ⨟ binconcat (X ⊕' Y)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitR D ⨟ (prodF p v ⨟
          prodF (cListXY X Y) (inl X Y ⨟ pureT (X ⊕' Y)))) ⨟ binconcat (X ⊕' Y)) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitR D ⨟ prodF (p ⨟ cListXY X Y)
          (v ⨟ (inl X Y ⨟ pureT (X ⊕' Y)))) ⨟ binconcat (X ⊕' Y)) :=
        PEq.compL _ (PEq.compR _ (PEq.prod_comp _ _ _ _))
    _ ≡ₜ ((unitR D ⨟ prodF (p ⨟ cListXY X Y) (inlV v Y)) ⨟ binconcat (X ⊕' Y)) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _)
          (PEq.symm (PEq.comp_assoc _ _ _))))

/-- **The criterion for computing a scan.**  A scan is provably equal to a pair of a term and
a value as soon as the corresponding identity between the contents holds. -/
theorem scanL_eq_pairR {X Y D : Ty} (v v' : Value X) (m : Term D ((Y ⊗ X)⋆))
    (p : Term D ((X ⊗ Y)⋆))
    (h : dotL (inlV v Y) (m ⨟ cListYX X Y) ≡ₜ dotR (p ⨟ cListXY X Y) (inlV v' Y)) :
    scanL X Y v m ≡ₜ pairR p v' := by
  refine ((cancel _ _).1 _ (cmL X Y) (cmL_injective X Y)).2 ?_
  exact (scanL_cmL v m).trans (h.trans (PEq.symm (pairR_cmL p v')))

/-- The identity between the contents that a computed scan gives. -/
theorem scanL_content {X Y D : Ty} (v v' : Value X) (m : Term D ((Y ⊗ X)⋆))
    (p : Term D ((X ⊗ Y)⋆)) (h : scanL X Y v m ≡ₜ pairR p v') :
    dotL (inlV v Y) (m ⨟ cListYX X Y) ≡ₜ dotR (p ⨟ cListXY X Y) (inlV v' Y) :=
  (PEq.symm (scanL_cmL v m)).trans ((PEq.compL _ h).trans (pairR_cmL p v'))

/-! ### Running a scan over a list with one more element at the end -/

/-- The scan of a list with one more element `(y, x)` at the end: the scan of the list,
followed by the pair of its final carry with `y`. -/
def snocScan (X Y : Ty) (v : Value X) {D E : Ty} (m : Term D ((Y ⊗ X)⋆)) (y : Term E Y) :
    Term (D ⊗ E) ((X ⊗ Y)⋆) :=
  prodF (scanL X Y v m) y ⨟ (assocR ((X ⊗ Y)⋆) X Y ⨟ append (X ⊗ Y))

/-- The content of a list with one more element `(y, x)` at the end. -/
theorem content_fdot_sing {X Y D E : Ty} (m : Term D ((Y ⊗ X)⋆)) (y : Term E Y)
    (x : Value X) :
    ((m ⊙ (pairR y x ⨟ pureT (Y ⊗ X))) ⨟ cListYX X Y) ≡ₜ
      dotR ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) (inlV x Y) := by
  have hsing : ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y) ≡ₜ
      dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y) := by
    calc ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y)
        ≡ₜ (pairR y x ⨟ (pureT (Y ⊗ X) ⨟ cListYX X Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pairR y x ⨟ ((inr X Y ⨟ pureT (X ⊕' Y)) ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))) :=
          PEq.compR _ (homT_pure _)
      _ ≡ₜ ((pairR y x ⨟ prodF (inr X Y ⨟ pureT (X ⊕' Y)) (inl X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (x ⨟ (inl X Y ⨟ pureT (X ⊕' Y))) ⨟
            binconcat (X ⊕' Y)) := PEq.compL _ (pairR_prodF _ _ _ _)
      _ ≡ₜ dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y) :=
          PEq.compL _ (pairR_congr (PEq.refl _) (PEq.symm (PEq.comp_assoc _ _ _)))
  calc ((m ⊙ (pairR y x ⨟ pureT (Y ⊗ X))) ⨟ cListYX X Y)
      ≡ₜ ((m ⨟ cListYX X Y) ⊙ ((pairR y x ⨟ pureT (Y ⊗ X)) ⨟ cListYX X Y)) :=
        fdot_comp_homT _ _ _
    _ ≡ₜ ((m ⨟ cListYX X Y) ⊙ dotR (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y))) (inlV x Y)) :=
        fdot_congr (PEq.refl _) hsing
    _ ≡ₜ dotR ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) (inlV x Y) :=
        dotR_fdot _ _ _

/-- The content of the scan of a list with one more element at the end. -/
theorem content_snocScan {X Y D E : Ty} (v : Value X) (m : Term D ((Y ⊗ X)⋆)) (y : Term E Y) :
    (snocScan X Y v m y ⨟ cListXY X Y) ≡ₜ
      dotL (inlV v Y) ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) := by
  have happ : (append (X ⊗ Y) ⨟ cListXY X Y) ≡ₜ
      (cListXY X Y ⊙ ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y)))) := by
    calc (append (X ⊗ Y) ⨟ cListXY X Y)
        ≡ₜ ((prodF (Term.id ((X ⊗ Y)⋆)) (pureT (X ⊗ Y)) ⨟ binconcat (X ⊗ Y)) ⨟
            cListXY X Y) := PEq.compL _ (PEq.append_def (X ⊗ Y))
      _ ≡ₜ (prodF (Term.id ((X ⊗ Y)⋆)) (pureT (X ⊗ Y)) ⨟
            (binconcat (X ⊗ Y) ⨟ cListXY X Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id ((X ⊗ Y)⋆)) (pureT (X ⊗ Y)) ⨟
            (prodF (cListXY X Y) (cListXY X Y) ⨟ binconcat (X ⊕' Y))) :=
          PEq.compR _ (homT_binconcat _)
      _ ≡ₜ ((prodF (Term.id ((X ⊗ Y)⋆)) (pureT (X ⊗ Y)) ⨟
            prodF (cListXY X Y) (cListXY X Y)) ⨟ binconcat (X ⊕' Y)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id ((X ⊗ Y)⋆) ⨟ cListXY X Y) (pureT (X ⊗ Y) ⨟ cListXY X Y) ⨟
            binconcat (X ⊕' Y)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (cListXY X Y ⊙
            ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y)))) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (homT_pure _))
  have hchain : ((assocR ((X ⊗ Y)⋆) X Y ⨟ append (X ⊗ Y)) ⨟ cListXY X Y) ≡ₜ
      (cmL X Y ⊙ (inr X Y ⨟ pureT (X ⊕' Y))) := by
    calc ((assocR ((X ⊗ Y)⋆) X Y ⨟ append (X ⊗ Y)) ⨟ cListXY X Y)
        ≡ₜ (assocR ((X ⊗ Y)⋆) X Y ⨟ (append (X ⊗ Y) ⨟ cListXY X Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (assocR ((X ⊗ Y)⋆) X Y ⨟
            (cListXY X Y ⊙ ((inl X Y ⨟ pureT (X ⊕' Y)) ⊙ (inr X Y ⨟ pureT (X ⊕' Y))))) :=
          PEq.compR _ happ
      _ ≡ₜ ((cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y))) ⊙ (inr X Y ⨟ pureT (X ⊕' Y))) :=
          PEq.symm (fdot_assoc _ _ _)
  calc (snocScan X Y v m y ⨟ cListXY X Y)
      ≡ₜ (prodF (scanL X Y v m) y ⨟
          ((assocR ((X ⊗ Y)⋆) X Y ⨟ append (X ⊗ Y)) ⨟ cListXY X Y)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (scanL X Y v m) y ⨟ (cmL X Y ⊙ (inr X Y ⨟ pureT (X ⊕' Y)))) :=
        PEq.compR _ hchain
    _ ≡ₜ ((scanL X Y v m ⨟ cmL X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) := fdot_precomp _ _ _ _
    _ ≡ₜ ((dotL (inlV v Y) (m ⨟ cListYX X Y)) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) :=
        fdot_congr (scanL_cmL v m) (PEq.refl _)
    _ ≡ₜ dotL (inlV v Y) ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) :=
        dotL_fdot _ _ _

/-- **Scanning a list with one more element at the end.**  If the last element of the list
carries the value `x`, then the final carry of the scan is `x`. -/
theorem scanL_snoc {X Y D E : Ty} (v : Value X) (m : Term D ((Y ⊗ X)⋆)) (y : Term E Y)
    (x : Value X) :
    scanL X Y v (m ⊙ (pairR y x ⨟ pureT (Y ⊗ X))) ≡ₜ pairR (snocScan X Y v m y) x := by
  refine scanL_eq_pairR v x _ _ ?_
  calc dotL (inlV v Y) ((m ⊙ (pairR y x ⨟ pureT (Y ⊗ X))) ⨟ cListYX X Y)
      ≡ₜ dotL (inlV v Y)
          (dotR ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))) (inlV x Y)) :=
        dotL_congr (PEq.refl _) (content_fdot_sing m y x)
    _ ≡ₜ dotR (dotL (inlV v Y) ((m ⨟ cListYX X Y) ⊙ (y ⨟ (inr X Y ⨟ pureT (X ⊕' Y)))))
          (inlV x Y) := PEq.symm (dotR_dotL _ _ _)
    _ ≡ₜ dotR (snocScan X Y v m y ⨟ cListXY X Y) (inlV x Y) :=
        dotR_congr (PEq.symm (content_snocScan v m y)) (PEq.refl _)

/-! ### Running a scan over a concatenation -/

/-- **Scanning a binary concatenation.**  If the scan of `m₁` with carry `v₀` produces `p₁`
and the carry `v₁`, and the scan of `m₂` with carry `v₁` produces `p₂` and the carry `v₂`,
then the scan of the concatenation with carry `v₀` produces the concatenation of `p₁` and
`p₂`, and the carry `v₂`. -/
theorem scanL_fdot {X Y D₁ D₂ : Ty} (v₀ v₁ v₂ : Value X)
    (m₁ : Term D₁ ((Y ⊗ X)⋆)) (m₂ : Term D₂ ((Y ⊗ X)⋆))
    (p₁ : Term D₁ ((X ⊗ Y)⋆)) (p₂ : Term D₂ ((X ⊗ Y)⋆))
    (h₁ : scanL X Y v₀ m₁ ≡ₜ pairR p₁ v₁)
    (h₂ : scanL X Y v₁ m₂ ≡ₜ pairR p₂ v₂) :
    scanL X Y v₀ (m₁ ⊙ m₂) ≡ₜ pairR (p₁ ⊙ p₂) v₂ := by
  refine scanL_eq_pairR v₀ v₂ _ _ ?_
  have c₁ := scanL_content v₀ v₁ m₁ p₁ h₁
  have c₂ := scanL_content v₁ v₂ m₂ p₂ h₂
  have hm : ((m₁ ⊙ m₂) ⨟ cListYX X Y) ≡ₜ ((m₁ ⨟ cListYX X Y) ⊙ (m₂ ⨟ cListYX X Y)) :=
    fdot_comp_homT _ _ _
  have hp : ((p₁ ⊙ p₂) ⨟ cListXY X Y) ≡ₜ ((p₁ ⨟ cListXY X Y) ⊙ (p₂ ⨟ cListXY X Y)) :=
    fdot_comp_homT _ _ _
  calc dotL (inlV v₀ Y) ((m₁ ⊙ m₂) ⨟ cListYX X Y)
      ≡ₜ dotL (inlV v₀ Y) ((m₁ ⨟ cListYX X Y) ⊙ (m₂ ⨟ cListYX X Y)) :=
        dotL_congr (PEq.refl _) hm
    _ ≡ₜ ((dotL (inlV v₀ Y) (m₁ ⨟ cListYX X Y)) ⊙ (m₂ ⨟ cListYX X Y)) :=
        PEq.symm (dotL_fdot _ _ _)
    _ ≡ₜ ((dotR (p₁ ⨟ cListXY X Y) (inlV v₁ Y)) ⊙ (m₂ ⨟ cListYX X Y)) :=
        fdot_congr c₁ (PEq.refl _)
    _ ≡ₜ ((p₁ ⨟ cListXY X Y) ⊙ (dotL (inlV v₁ Y) (m₂ ⨟ cListYX X Y))) :=
        fdot_dotR_dotL _ _ _
    _ ≡ₜ ((p₁ ⨟ cListXY X Y) ⊙ (dotR (p₂ ⨟ cListXY X Y) (inlV v₂ Y))) :=
        fdot_congr (PEq.refl _) c₂
    _ ≡ₜ dotR ((p₁ ⨟ cListXY X Y) ⊙ (p₂ ⨟ cListXY X Y)) (inlV v₂ Y) := dotR_fdot _ _ _
    _ ≡ₜ dotR ((p₁ ⊙ p₂) ⨟ cListXY X Y) (inlV v₂ Y) := dotR_congr (PEq.symm hp) (PEq.refl _)

/-- **Scanning the concatenation of a list of lists.**  If each block is scanned with the
carry `v` and produces again the carry `v`, and the contents of the block and of its scan
are *syntactically conjugate* through `[v]`, then the scan of the concatenation of a list of
blocks is the concatenation of the scans of the blocks, again with carry `v`. -/
theorem scanL_homT {X Y W : Ty} (v : Value X) (e : Term W ((Y ⊗ X)⋆))
    (p : Term W ((X ⊗ Y)⋆)) (h : Term W ((X ⊕' Y)⋆))
    (hp : (p ⨟ cListXY X Y) ≡ₜ dotL (inlV v Y) h)
    (hq : (e ⨟ cListYX X Y) ≡ₜ dotR h (inlV v Y)) :
    scanL X Y v (homT e) ≡ₜ pairR (homT p) v := by
  refine scanL_eq_pairR v v _ _ ?_
  have hme : (homT e ⨟ cListYX X Y) ≡ₜ homT (dotR h (inlV v Y)) :=
    (homT_comp _ _).trans (homT_congr hq)
  have hmp : (homT p ⨟ cListXY X Y) ≡ₜ homT (dotL (inlV v Y) h) :=
    (homT_comp _ _).trans (homT_congr hp)
  calc dotL (inlV v Y) (homT e ⨟ cListYX X Y)
      ≡ₜ dotL (inlV v Y) (homT (dotR h (inlV v Y))) := dotL_congr (PEq.refl _) hme
    _ ≡ₜ dotR (homT (dotL (inlV v Y) h)) (inlV v Y) :=
        PEq.symm (conjugacy_of_syntactic h (inlV v Y))
    _ ≡ₜ dotR (homT p ⨟ cListXY X Y) (inlV v Y) := dotR_congr (PEq.symm hmp) (PEq.refl _)

/-! ### Scanning a concatenation whose second block is arbitrary -/

/-- Pre-composing a scan. -/
theorem comp_scanL {X Y D D' : Ty} (v : Value X) (f : Term D' D) (m : Term D ((Y ⊗ X)⋆)) :
    (f ⨟ scanL X Y v m) ≡ₜ scanL X Y v (f ⨟ m) := by
  calc (f ⨟ (pairL v m ⨟ shiftL X Y))
      ≡ₜ ((f ⨟ pairL v m) ⨟ shiftL X Y) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (pairL v (f ⨟ m) ⨟ shiftL X Y) := PEq.compL _ (comp_pairL _ _ _)

/-- Congruence for scans. -/
theorem scanL_congr {X Y D : Ty} (v : Value X) {m m' : Term D ((Y ⊗ X)⋆)} (h : m ≡ₜ m') :
    scanL X Y v m ≡ₜ scanL X Y v m' :=
  PEq.compL _ (pairL_congr (PEq.refl _) h)

/-- Combining the outcome of the scan of a first block with the outcome of the scan of the
rest: the two lists are concatenated and the final carry is kept. -/
def catScan (X Y : Ty) : Term ((X ⊗ Y)⋆ ⊗ ((X ⊗ Y)⋆ ⊗ X)) ((X ⊗ Y)⋆ ⊗ X) :=
  assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ prodF (binconcat (X ⊗ Y)) (Term.id X)

/-- The content of a combined scan. -/
theorem catScan_cmL (X Y : Ty) :
    (catScan X Y ⨟ cmL X Y) ≡ₜ (cListXY X Y ⊙ cmL X Y) := by
  have hb : (binconcat (X ⊗ Y) ⨟ cListXY X Y) ≡ₜ (cListXY X Y ⊙ cListXY X Y) :=
    homT_binconcat _
  calc ((assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ prodF (binconcat (X ⊗ Y)) (Term.id X)) ⨟ cmL X Y)
      ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟
          (prodF (binconcat (X ⊗ Y)) (Term.id X) ⨟
            (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y))))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ ((binconcat (X ⊗ Y) ⨟ cListXY X Y) ⊙
          (Term.id X ⨟ (inl X Y ⨟ pureT (X ⊕' Y))))) := PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟
          ((cListXY X Y ⊙ cListXY X Y) ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))) :=
        PEq.compR _ (fdot_congr hb (PEq.id_comp _))
    _ ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ (assocR ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟
          (cListXY X Y ⊙ (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))))) :=
        PEq.compR _ (fdot_assoc _ _ _)
    _ ≡ₜ ((assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ assocR ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X) ⨟
          (cListXY X Y ⊙ (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y))))) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((X ⊗ Y)⋆ ⊗ ((X ⊗ Y)⋆ ⊗ X)) ⨟
          (cListXY X Y ⊙ (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y))))) :=
        PEq.compL _ (PEq.assocL_assocR _ _ _)
    _ ≡ₜ (cListXY X Y ⊙ (cListXY X Y ⊙ (inl X Y ⨟ pureT (X ⊕' Y)))) := PEq.id_comp _
    _ ≡ₜ (cListXY X Y ⊙ cmL X Y) := PEq.refl _

/-- The list produced by a combined scan is the concatenation of the two lists. -/
theorem catScan_fst (X Y : Ty) :
    (catScan X Y ⨟ fst ((X ⊗ Y)⋆) X) ≡ₜ (Term.id ((X ⊗ Y)⋆) ⊙ fst ((X ⊗ Y)⋆) X) := by
  calc ((assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ prodF (binconcat (X ⊗ Y)) (Term.id X)) ⨟
        fst ((X ⊗ Y)⋆) X)
      ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ (prodF (binconcat (X ⊗ Y)) (Term.id X) ⨟
          fst ((X ⊗ Y)⋆) X)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟
          (fst ((X ⊗ Y)⋆ ⊗ (X ⊗ Y)⋆) X ⨟ binconcat (X ⊗ Y))) :=
        PEq.compR _ (PEq.nat_fst _ _)
    _ ≡ₜ ((assocL ((X ⊗ Y)⋆) ((X ⊗ Y)⋆) X ⨟ fst ((X ⊗ Y)⋆ ⊗ (X ⊗ Y)⋆) X) ⨟
          binconcat (X ⊗ Y)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((X ⊗ Y)⋆) ⊙ fst ((X ⊗ Y)⋆) X) :=
        PEq.compL _ (Term.assocL_fst _ _ _)

/-- **Scanning a binary concatenation, with an arbitrary second block.**  If the scan of
`m₁` with carry `v₀` produces `p₁` and the carry `v₁`, then the scan of the concatenation of
`m₁` and `m₂` with carry `v₀` is obtained by concatenating `p₁` with the scan of `m₂` with
carry `v₁`. -/
theorem scanL_fdot_gen {X Y D₁ D₂ : Ty} (v₀ v₁ : Value X)
    (m₁ : Term D₁ ((Y ⊗ X)⋆)) (m₂ : Term D₂ ((Y ⊗ X)⋆)) (p₁ : Term D₁ ((X ⊗ Y)⋆))
    (h₁ : scanL X Y v₀ m₁ ≡ₜ pairR p₁ v₁) :
    scanL X Y v₀ (m₁ ⊙ m₂) ≡ₜ (prodF p₁ (scanL X Y v₁ m₂) ⨟ catScan X Y) := by
  refine ((cancel _ _).1 _ (cmL X Y) (cmL_injective X Y)).2 ?_
  have c₁ := scanL_content v₀ v₁ m₁ p₁ h₁
  calc (scanL X Y v₀ (m₁ ⊙ m₂) ⨟ cmL X Y)
      ≡ₜ dotL (inlV v₀ Y) ((m₁ ⊙ m₂) ⨟ cListYX X Y) := scanL_cmL _ _
    _ ≡ₜ dotL (inlV v₀ Y) ((m₁ ⨟ cListYX X Y) ⊙ (m₂ ⨟ cListYX X Y)) :=
        dotL_congr (PEq.refl _) (fdot_comp_homT _ _ _)
    _ ≡ₜ ((dotL (inlV v₀ Y) (m₁ ⨟ cListYX X Y)) ⊙ (m₂ ⨟ cListYX X Y)) :=
        PEq.symm (dotL_fdot _ _ _)
    _ ≡ₜ ((dotR (p₁ ⨟ cListXY X Y) (inlV v₁ Y)) ⊙ (m₂ ⨟ cListYX X Y)) :=
        fdot_congr c₁ (PEq.refl _)
    _ ≡ₜ ((p₁ ⨟ cListXY X Y) ⊙ (dotL (inlV v₁ Y) (m₂ ⨟ cListYX X Y))) :=
        fdot_dotR_dotL _ _ _
    _ ≡ₜ ((p₁ ⨟ cListXY X Y) ⊙ (scanL X Y v₁ m₂ ⨟ cmL X Y)) :=
        fdot_congr (PEq.refl _) (PEq.symm (scanL_cmL _ _))
    _ ≡ₜ (prodF p₁ (scanL X Y v₁ m₂) ⨟ (cListXY X Y ⊙ cmL X Y)) :=
        PEq.symm (fdot_precomp _ _ _ _)
    _ ≡ₜ (prodF p₁ (scanL X Y v₁ m₂) ⨟ (catScan X Y ⨟ cmL X Y)) :=
        PEq.compR _ (PEq.symm (catScan_cmL X Y))
    _ ≡ₜ ((prodF p₁ (scanL X Y v₁ m₂) ⨟ catScan X Y) ⨟ cmL X Y) :=
        PEq.symm (PEq.comp_assoc _ _ _)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
