import Lax149335.SimpleRationalFunctions

/-!
---
title: Conjugacy completeness
type: theorem
---
**Theorem 2.6 (Conjugacy completeness).** Two simple rational terms define the same function
if and only if they are equivalent with respect to the least equivalence relation $\equiv$
on simple rational terms that satisfies the following rules (where $f, g, h$ are simple
rational terms, $w, v$ are strings and $\varepsilon$ is the empty string):

1. *Congruence:* $\equiv$ is preserved by co-pairing, concatenation, homomorphism and
   adding constants.
2. *Concatenation monoidality:* $(f \cdot w) \cdot v \equiv f \cdot wv$,
   $w \cdot (v \cdot f) \equiv wv \cdot f$, $f \cdot \varepsilon \equiv f \equiv
   \varepsilon \cdot f$, $(w \cdot f) \cdot v \equiv w \cdot (f \cdot v)$,
   $(f \cdot w) \odot g \equiv f \odot (w \cdot g)$,
   $w \cdot (f \odot g) \equiv (w \cdot f) \odot g$,
   $(f \odot g) \cdot w \equiv f \odot (g \cdot w)$, and
   $[] \cdot w \equiv w \cdot []$.
3. *Constants and co-pairing:* $w \cdot \langle f_1, f_2 \rangle \equiv
   \langle w \cdot f_1, w \cdot f_2 \rangle$ and $\langle f_1, f_2 \rangle \cdot w
   \equiv \langle f_1 \cdot w, f_2 \cdot w \rangle$.
4. *Case splitting:* if $\langle f_1 \odot h, f_2 \odot h \rangle \equiv
   \langle g_1 \odot h, g_2 \odot h \rangle$ then
   $\langle f_1, f_2 \rangle \odot h \equiv \langle g_1, g_2 \rangle \odot h$, and
   symmetrically on the other side.
5. *Conjugacy:* if $f \cdot w \equiv w \cdot g$ then
   $(\mathrm{hom}\, f) \cdot w \equiv w \cdot (\mathrm{hom}\, g)$.
-/

namespace Lax149335.ConjugacyCompleteness

open Lax149335.Types Lax149335.SimpleRationalFunctions

namespace SimpleTerm

/-- The equivalence `≡` of simple rational terms from Theorem 2.6: the least relation closed
under (1) congruence, (2) concatenation monoidality, (3) constants and co-pairing, (4) case
splitting and (5) conjugacy. -/
inductive SEq {Bs : Type} : {A : Ty} → SimpleTerm Bs A → SimpleTerm Bs A → Prop
  -- (1) congruence, together with the equivalence relation rules
  | refl {A : Ty} (f : SimpleTerm Bs A) : SEq f f
  | symm {A : Ty} {f g : SimpleTerm Bs A} : SEq f g → SEq g f
  | trans {A : Ty} {f g h : SimpleTerm Bs A} : SEq f g → SEq g h → SEq f h
  | congr_either {A₁ A₂ : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂} :
      SEq f₁ g₁ → SEq f₂ g₂ → SEq (.either f₁ f₂) (.either g₁ g₂)
  | congr_conc {A₁ A₂ : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂} :
      SEq f₁ g₁ → SEq f₂ g₂ → SEq (.conc f₁ f₂) (.conc g₁ g₂)
  | congr_hom {A : Ty} {f g : SimpleTerm Bs A} : SEq f g → SEq (.hom f) (.hom g)
  | congr_pre {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq f g → SEq (.pre w f) (.pre w g)
  | congr_post {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq f g → SEq (.post f w) (.post g w)
  -- (2) concatenation monoidality
  | post_post {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.post (.post f w) v) (.post f (w ++ v))
  | pre_pre {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.pre w (.pre v f)) (.pre (w ++ v) f)
  | post_nil {A : Ty} (f : SimpleTerm Bs A) : SEq (.post f []) f
  | pre_nil {A : Ty} (f : SimpleTerm Bs A) : SEq (.pre [] f) f
  | pre_post {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.post (.pre w f) v) (.pre w (.post f v))
  | conc_shift {A₁ A₂ : Ty} (f : SimpleTerm Bs A₁) (g : SimpleTerm Bs A₂) (w : List Bs) :
      SEq (.conc (.post f w) g) (.conc f (.pre w g))
  | pre_conc {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.pre w (.conc f₁ f₂)) (.conc (.pre w f₁) f₂)
  | post_conc {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.post (.conc f₁ f₂) w) (.conc f₁ (.post f₂ w))
  | move_empty (w : List Bs) :
      SEq (.post (.empty : SimpleTerm Bs Ty.unit) w) (.pre w .empty)
  -- (3) constants and copairing
  | pre_either {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.pre w (.either f₁ f₂)) (.either (.pre w f₁) (.pre w f₂))
  | post_either {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.post (.either f₁ f₂) w) (.either (.post f₁ w) (.post f₂ w))
  -- (4) case splitting
  | case_left {A₁ A₂ A : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂}
      {h : SimpleTerm Bs A} :
      SEq (.either (.conc f₁ h) (.conc f₂ h)) (.either (.conc g₁ h) (.conc g₂ h)) →
      SEq (.conc (.either f₁ f₂) h) (.conc (.either g₁ g₂) h)
  | case_right {A₁ A₂ A : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂}
      {h : SimpleTerm Bs A} :
      SEq (.either (.conc h f₁) (.conc h f₂)) (.either (.conc h g₁) (.conc h g₂)) →
      SEq (.conc h (.either f₁ f₂)) (.conc h (.either g₁ g₂))
  -- (5) conjugacy
  | conjugacy {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq (.post f w) (.pre w g) → SEq (.post (.hom f) w) (.pre w (.hom g))

/-- Notation `f ≃ₛ g` for the equivalence of simple rational terms. -/
infix:50 " ≃ₛ " => SEq

end SimpleTerm

/-- **Theorem 2.6.** Two simple rational terms define the same function if and only if they
are equivalent. -/
axiom conjugacy_completeness {Bs : Type} {A : Ty} (f g : SimpleTerm Bs A) :
    f.den = g.den ↔ f ≃ₛ g

end Lax149335.ConjugacyCompleteness
