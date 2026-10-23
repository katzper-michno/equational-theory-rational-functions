import Lax149335.LiftsAndDrops
import Lax149335.EquationalTheory

/-!
---
title: Exchange
type: lemma
---
**Lemma (Exchange).** Every composition of the form drop-lift is equivalent to a
composition of the form lift-drop.
-/

namespace Lax149335.Exchange

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.LiftsAndDrops

/-- A drop followed by a lift is provably equivalent to a lift followed by a
drop. -/
axiom exchange {A B C : Ty} (d : Term A B) (l : Term B C) (hd : IsDrop d) (hl : IsLift l) :
    ∃ (D : Ty) (l' : Term A D) (d' : Term D C), IsLift l' ∧ IsDrop d' ∧ (d ⨟ l) ≡ₜ (l' ⨟ d')

end Lax149335.Exchange
