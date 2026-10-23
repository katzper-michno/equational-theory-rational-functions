import Lax149335.InjectiveTerms

/-!
---
title: Cancelling injective and surjective terms
type: lemma
---
**Lemma 5.5.** For all terms $g_1, g_2 : A \to B$,
$$
\begin{aligned}
g_1 \equiv g_2 &\quad\text{iff}\quad g_1 \mathbin{;} f \equiv g_2 \mathbin{;} f
  &&\text{for every injective } f : B \to C, \\
g_1 \equiv g_2 &\quad\text{iff}\quad f \mathbin{;} g_1 \equiv f \mathbin{;} g_2
  &&\text{for every surjective } f : C \to A.
\end{aligned}
$$
-/

namespace Lax149335.Cancellation

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.InjectiveTerms

/-- **Lemma 5.5.** Injective terms can be cancelled on the right and surjective terms on
the left. -/
axiom cancel {A B : Ty} (g₁ g₂ : Term A B) :
    (∀ (C : Ty) (f : Term B C), ProvablyInjective f → (g₁ ≡ₜ g₂ ↔ (g₁ ⨟ f) ≡ₜ (g₂ ⨟ f))) ∧
    (∀ (C : Ty) (f : Term C A), ProvablySurjective f → (g₁ ≡ₜ g₂ ↔ (f ⨟ g₁) ≡ₜ (f ⨟ g₂)))

end Lax149335.Cancellation
