import Lax149335Proofs.SimpleCompleteness.SumShuffle
import Lax149335Proofs.Appendix.Drops.SumProdNormalisation
import Lax149335Proofs.GeneralCompleteness.LiftsAndDrops

/-!
# The co-product shuffles, as lifts

Three rebracketings of nested co-products that the appendix uses to combine the leaves of a
case tree pairwise: the interchange `Lax149335Proofs.Term.sumInter` of four summands, and the two
shuffles `Lax149335Proofs.Term.sumSwapMid` and `Lax149335Proofs.Term.sumSwapMid'` that move a summand into
the middle.  All three are lifts, and their action on a co-pairing is recorded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-- The interchange lift of four co-products. -/
def sumInter (A B C D : Ty) : Term ((A ⊕' B) ⊕' (C ⊕' D)) ((A ⊕' C) ⊕' (B ⊕' D)) :=
  sumAssocR A B (C ⊕' D) ⨟
    (sumF (Term.id A) (sumAssocL B C D ⨟
      (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟ sumAssocL A C (B ⊕' D))

theorem isLift_sumInter (A B C D : Ty) : IsLift (sumInter A B C D) :=
  IsLift.comp (IsLift.sumAssocR _ _ _)
    (IsLift.comp
      (IsLift.sumF (IsLift.id _)
        (IsLift.comp (IsLift.sumAssocL _ _ _)
          (IsLift.comp (IsLift.sumF (IsLift.comm _ _) (IsLift.id _))
            (IsLift.sumAssocR _ _ _))))
      (IsLift.sumAssocL _ _ _))

theorem sumInter_either {A B C D Z : Ty} (a : Term A Z) (b : Term B Z) (c : Term C Z)
    (d : Term D Z) :
    (sumInter A B C D ⨟ either (either a c) (either b d)) ≡ₜ
      either (either a b) (either c d) := by
  have hX : ((sumAssocL B C D ⨟ (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟
      either c (either b d)) ≡ₜ either b (either c d) := by
    calc ((sumAssocL B C D ⨟ (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟
            either c (either b d))
        ≡ₜ (sumAssocL B C D ⨟ ((sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D) ⨟
            either c (either b d))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (sumAssocL B C D ⨟ (sumF (comm B C) (Term.id D) ⨟ (sumAssocR C B D ⨟
            either c (either b d)))) := PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (sumAssocL B C D ⨟ (sumF (comm B C) (Term.id D) ⨟ either (either c b) d)) :=
          PEq.compR _ (PEq.compR _ (PEq.symm (either_assocR c b d)))
      _ ≡ₜ (sumAssocL B C D ⨟ either (comm B C ⨟ either c b) (Term.id D ⨟ d)) :=
          PEq.compR _ (PEq.symm (PEq.symm (sumF_either _ _ _ _)))
      _ ≡ₜ (sumAssocL B C D ⨟ either (either b c) d) :=
          PEq.compR _ (either_congr (comm_either c b) (PEq.id_comp d))
      _ ≡ₜ either b (either c d) := PEq.symm (either_assocL b c d)
  calc (sumInter A B C D ⨟ either (either a c) (either b d))
      ≡ₜ (sumAssocR A B (C ⊕' D) ⨟ ((sumF (Term.id A) (sumAssocL B C D ⨟
          (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟ sumAssocL A C (B ⊕' D)) ⨟
          either (either a c) (either b d))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (sumAssocR A B (C ⊕' D) ⨟ (sumF (Term.id A) (sumAssocL B C D ⨟
          (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟ (sumAssocL A C (B ⊕' D) ⨟
          either (either a c) (either b d)))) := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (sumAssocR A B (C ⊕' D) ⨟ (sumF (Term.id A) (sumAssocL B C D ⨟
          (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟
          either a (either c (either b d)))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm (either_assocL a c (either b d))))
    _ ≡ₜ (sumAssocR A B (C ⊕' D) ⨟ either (Term.id A ⨟ a)
          ((sumAssocL B C D ⨟ (sumF (comm B C) (Term.id D) ⨟ sumAssocR C B D)) ⨟
            either c (either b d))) := PEq.compR _ (sumF_either _ _ _ _)
    _ ≡ₜ (sumAssocR A B (C ⊕' D) ⨟ either a (either b (either c d))) :=
        PEq.compR _ (either_congr (PEq.id_comp a) hX)
    _ ≡ₜ either (either a b) (either c d) := PEq.symm (either_assocR a b (either c d))

/-- The lift that moves the third summand of `(A + B) + C` into the middle. -/
def sumSwapMid (A B C : Ty) : Term ((A ⊕' B) ⊕' C) ((A ⊕' C) ⊕' B) :=
  sumAssocR A B C ⨟ (sumF (Term.id A) (comm B C) ⨟ sumAssocL A C B)

theorem isLift_sumSwapMid (A B C : Ty) : IsLift (sumSwapMid A B C) :=
  IsLift.comp (IsLift.sumAssocR _ _ _)
    (IsLift.comp (IsLift.sumF (IsLift.id _) (IsLift.comm _ _)) (IsLift.sumAssocL _ _ _))

theorem sumSwapMid_either {A B C Z : Ty} (a : Term A Z) (b : Term B Z) (c : Term C Z) :
    (sumSwapMid A B C ⨟ either (either a c) b) ≡ₜ either (either a b) c := by
  calc (sumSwapMid A B C ⨟ either (either a c) b)
      ≡ₜ (sumAssocR A B C ⨟ ((sumF (Term.id A) (comm B C) ⨟ sumAssocL A C B) ⨟
          either (either a c) b)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (sumAssocR A B C ⨟ (sumF (Term.id A) (comm B C) ⨟ (sumAssocL A C B ⨟
          either (either a c) b))) := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (sumAssocR A B C ⨟ (sumF (Term.id A) (comm B C) ⨟ either a (either c b))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm (either_assocL a c b)))
    _ ≡ₜ (sumAssocR A B C ⨟ either (Term.id A ⨟ a) (comm B C ⨟ either c b)) :=
        PEq.compR _ (sumF_either _ _ _ _)
    _ ≡ₜ (sumAssocR A B C ⨟ either a (either b c)) :=
        PEq.compR _ (either_congr (PEq.id_comp a) (comm_either c b))
    _ ≡ₜ either (either a b) c := PEq.symm (either_assocR a b c)

/-- The lift that moves the first summand of `A + (B + C)` into the middle. -/
def sumSwapMid' (A B C : Ty) : Term (A ⊕' (B ⊕' C)) (B ⊕' (A ⊕' C)) :=
  sumAssocL A B C ⨟ (sumF (comm A B) (Term.id C) ⨟ sumAssocR B A C)

theorem isLift_sumSwapMid' (A B C : Ty) : IsLift (sumSwapMid' A B C) :=
  IsLift.comp (IsLift.sumAssocL _ _ _)
    (IsLift.comp (IsLift.sumF (IsLift.comm _ _) (IsLift.id _)) (IsLift.sumAssocR _ _ _))

theorem sumSwapMid'_either {A B C Z : Ty} (a : Term A Z) (b : Term B Z) (c : Term C Z) :
    (sumSwapMid' A B C ⨟ either b (either a c)) ≡ₜ either a (either b c) := by
  calc (sumSwapMid' A B C ⨟ either b (either a c))
      ≡ₜ (sumAssocL A B C ⨟ ((sumF (comm A B) (Term.id C) ⨟ sumAssocR B A C) ⨟
          either b (either a c))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (sumAssocL A B C ⨟ (sumF (comm A B) (Term.id C) ⨟ (sumAssocR B A C ⨟
          either b (either a c)))) := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (sumAssocL A B C ⨟ (sumF (comm A B) (Term.id C) ⨟ either (either b a) c)) :=
        PEq.compR _ (PEq.compR _ (PEq.symm (either_assocR b a c)))
    _ ≡ₜ (sumAssocL A B C ⨟ either (comm A B ⨟ either b a) (Term.id C ⨟ c)) :=
        PEq.compR _ (sumF_either _ _ _ _)
    _ ≡ₜ (sumAssocL A B C ⨟ either (either a b) c) :=
        PEq.compR _ (either_congr (comm_either b a) (PEq.id_comp c))
    _ ≡ₜ either a (either b c) := PEq.symm (either_assocL a b c)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
