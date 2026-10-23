import Lax149335.GuardedTerms

/-!
---
title: Reduction to nonempty summands
type: lemma
---
**Lemma 6.5.** In the situation of Lemma 6.4, one can further assume without loss of
generality that all the terms $f_i$ and $g_i$ are nonempty.

# Formalization notes

As for Lemma 6.4, the statement is a reduction: if the conjugacy rule holds for co-pairings
of $k$-guarded nonempty terms whose input type has list nesting depth at most $D$, then it
holds for all co-pairings of $k$-guarded terms whose input type has list nesting depth at
most $D$. The assumption that $B$ is a finite alphabet is not needed.
-/

namespace Lax149335.NonemptyReduction

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory Lax149335.SimpleRationalTerms Lax149335.GuardedTerms

/-- **Lemma 6.5.** The conjugacy rule for co-pairings of `k`-guarded terms follows from the
conjugacy rule for co-pairings of `k`-guarded nonempty terms. -/
axiom wlog_nonempty {B : Ty} (w : Value B⋆) (hw : 0 < valLength w) (D : ℕ)
    (H : ∀ (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As),
      Ty.listDepth (sumTyOf A₀ As) ≤ D →
      KGuarded (valLength w) B f₀ → KGuarded (valLength w) B g₀ →
      fs.All (fun _ f => KGuarded (valLength w) B f) →
      gs.All (fun _ g => KGuarded (valLength w) B g) →
      NonemptyOutput f₀ → NonemptyOutput g₀ →
      fs.All (fun _ f => NonemptyOutput f) → gs.All (fun _ g => NonemptyOutput g) →
      dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs) →
      dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs)))
    (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As)
    (hD : Ty.listDepth (sumTyOf A₀ As) ≤ D)
    (hf₀ : KGuarded (valLength w) B f₀) (hg₀ : KGuarded (valLength w) B g₀)
    (hfs : fs.All (fun _ f => KGuarded (valLength w) B f))
    (hgs : gs.All (fun _ g => KGuarded (valLength w) B g))
    (hfg : dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs)) :
    dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs))

end Lax149335.NonemptyReduction
