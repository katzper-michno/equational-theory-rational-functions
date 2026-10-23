import Lax149335Proofs.SimpleCompleteness.ValueExtractionProof
import Lax149335Proofs.Appendix.Bundles.Window

/-!
# The proof of Lemma 6.1 (completeness for simple rational terms)

This file completes the proof of Lemma 6.1: for simple rational terms, denotational equality
implies provable equality (the completeness rule (17)) and provable `w`-conjugacy is lifted
by the homomorphism combinator (the conjugacy rule (18)).  The two rules are proved together
by induction on the list nesting depth of the input type:

* the completeness rule at input types of list nesting depth at most `d` follows from the
  conjugacy rule at input types of list nesting depth smaller than `d`, by the completeness
  of the equational theory of Theorem 2.6 (`Lax149335Proofs.completeness_rule_of_conjBelow`);
* the conjugacy rule at input types of list nesting depth at most `d` follows from the
  completeness rule at input types of list nesting depth at most `d`
  (`Lax149335Proofs.conj_hom_of_kcopair`).

The second step is the argument of the paper.  After the two reductions of Lemmas 6.4 and 6.5
the two terms are co-pairings of `k`-guarded terms with nonempty outputs, where `k` is the
length of `w`.  Their `k`-fold concatenation powers distribute into co-pairings of `k`-fold
products of `k`-guarded terms, and every such product provably starts with a value of length
at least `k`, respectively ends with one; since the outputs of the powers start with `w`,
respectively end with `w`, the powers are provably of the form `w · H` and `H' · w`.  The
completeness rule identifies `H` and `H'`, so Lemma 6.2 applies to the powers, and the bundle
isomorphism of Lemma 6.7 transports the conclusion from the powers back to the two terms.

The statement of Lemma 6.1 itself, `Lax149335Proofs.completeness_simple`, is at the end of this
file; it is stated here rather than in `Lax149335Proofs.SimpleCompleteness.Statements` because its proof
uses the material of that file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Two facts about conjugate words -/

/-- If `s · w = w · t` and `w` is no longer than `s`, then `w` is a prefix of `s`. -/
theorem prefix_of_word_conj {α : Type} {s t w : List α} (h : s ++ w = w ++ t)
    (hlen : w.length ≤ s.length) : w <+: s := by
  have h1 : w <+: s ++ w := by rw [h]; exact List.prefix_append w t
  rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append s w) with h3 | h3
  · exact h3
  · exact (h3.eq_of_length_le hlen) ▸ List.prefix_refl s

/-- If `s · w = w · t` and `w` is no longer than `t`, then `w` is a suffix of `t`. -/
theorem suffix_of_word_conj {α : Type} {s t w : List α} (h : s ++ w = w ++ t)
    (hlen : w.length ≤ t.length) : w <:+ t := by
  have h1 : w <:+ w ++ t := by rw [← h]; exact List.suffix_append s w
  rcases List.suffix_or_suffix_of_suffix h1 (List.suffix_append w t) with h3 | h3
  · exact h3
  · exact (h3.eq_of_length_le hlen) ▸ List.suffix_refl t

/-- A prefix that is no longer than the first part of a concatenation is a prefix of that
first part. -/
theorem prefix_of_prefix_append {α : Type} {w u t : List α} (h : w <+: u ++ t)
    (hlen : w.length ≤ u.length) : w <+: u := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append u t) with h3 | h3
  · exact h3
  · exact (h3.eq_of_length_le hlen) ▸ List.prefix_refl u

/-- A suffix that is no longer than the second part of a concatenation is a suffix of that
second part. -/
theorem suffix_of_suffix_append {α : Type} {w t v : List α} (h : w <:+ t ++ v)
    (hlen : w.length ≤ v.length) : w <:+ v := by
  rcases List.suffix_or_suffix_of_suffix h (List.suffix_append t v) with h3 | h3
  · exact h3
  · exact (h3.eq_of_length_le hlen) ▸ List.suffix_refl v

/-! ### Matching pairs of co-pairings -/

namespace KCopair2

variable {k : ℕ} {B : Ty}

/-- The left term of a matching pair of co-pairings never produces the empty list. -/
theorem nonempty_left : {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G → NonemptyOutput F := by
  intro X F G h
  induction h with
  | leaf _ _ hnf _ => exact hnf
  | node _ _ ih₁ ih₂ =>
      rintro (x | x)
      · simpa using ih₁ x
      · simpa using ih₂ x

/-- The right term of a matching pair of co-pairings never produces the empty list. -/
theorem nonempty_right : {X : Ty} → {F G : Term X B⋆} → KCopair2 k B F G → NonemptyOutput G := by
  intro X F G h
  induction h with
  | leaf _ _ _ hng => exact hng
  | node _ _ ih₁ ih₂ =>
      rintro (x | x)
      · simpa using ih₁ x
      · simpa using ih₂ x

/-- Two `n`-ary co-pairings of `k`-guarded terms with nonempty outputs are a matching pair of
co-pairings. -/
theorem of_copair : (As : List Ty) → (A₀ : Ty) → (f₀ g₀ : Term A₀ B⋆) →
    (fs gs : Cases B⋆ As) → KGuarded k B f₀ → KGuarded k B g₀ →
    NonemptyOutput f₀ → NonemptyOutput g₀ →
    fs.All (fun _ f => KGuarded k B f) → gs.All (fun _ g => KGuarded k B g) →
    fs.All (fun _ f => NonemptyOutput f) → gs.All (fun _ g => NonemptyOutput g) →
    KCopair2 k B (copair f₀ fs) (copair g₀ gs)
  | [], _, _, _, .nil, .nil, hf, hg, hnf, hng, _, _, _, _ => KCopair2.leaf hf hg hnf hng
  | (_ :: As), _, _, _, .cons f₁ fs₁, .cons g₁ gs₁, hf, hg, hnf, hng, hkfs, hkgs, hnfs, hngs =>
      KCopair2.node (KCopair2.leaf hf hg hnf hng)
        (of_copair As _ f₁ g₁ fs₁ gs₁ hkfs.1 hkgs.1 hnfs.1 hngs.1 hkfs.2 hkgs.2 hnfs.2 hngs.2)

end KCopair2

/-! ### The concatenation powers -/

/-- The `j`-th concatenation power of a term with nonempty outputs produces at least `j`
letters. -/
theorem pow_homMap_den_length {B X : Ty} {F : Term X B⋆} (hF : NonemptyOutput F) :
    (j : ℕ) → ∀ z : ⟦(Term.TyF.pow j).app X⟧,
      j ≤ (((Term.TyF.pow j).homMap F).den z).length
  | 0 => by intro _; exact Nat.zero_le _
  | (j + 1) => by
      rintro ⟨x, z⟩
      have h1 := pow_homMap_den_length hF j z
      have h2 : 1 ≤ (F.den x).length := by
        rcases hd : F.den x with _ | ⟨a, l⟩
        · exact absurd hd (hF x)
        · simp
      have h3 : (((Term.TyF.pow (j + 1)).homMap F).den (x, z)).length =
          (F.den x).length + (((Term.TyF.pow j).homMap F).den z).length := by
        simp [Term.TyF.pow, Term.TyF.homMap]
      omega

/-! ### The leaves of the joint decomposition -/

/-- A product of `j ≥ k` `k`-guarded nonempty terms all of whose outputs start with the value
`w` of length `k` is provably `w` followed by an equationally simple term. -/
theorem leaf_dotL {B : Ty} {w : Value B⋆} {j : ℕ} {Y : Ty} {T : Term Y B⋆}
    (hT : KProdT (valLength w) B j T) (hj : valLength w ≤ j)
    (hpre : ∀ y : ⟦Y⟧, w.den () <+: T.den y) :
    ∃ H : Term Y B⋆, EqSimple B H ∧ T ≡ₜ Term.dotL w H := by
  obtain ⟨u, H, hlen, hH, hTu⟩ := hT.dotL_factor
  rw [min_eq_right hj] at hlen
  have hpre' : w.den () <+: u.den () := by
    have h2 := hpre (Ty.someElem Y)
    rw [congrFun (PEq.sound hTu) (Ty.someElem Y)] at h2
    simp only [Term.den_dotL] at h2
    exact prefix_of_prefix_append h2 (by simpa [valLength] using hlen)
  obtain ⟨r, hr⟩ := hpre'
  refine ⟨Term.dotL (encV B⋆ r) H, EqSimple.dotL _ hH, ?_⟩
  refine hTu.trans ?_
  refine (Term.dotL_congr ?_ (PEq.refl H)).trans (PEq.symm (Term.dotL_dotL w (encV B⋆ r) H))
  exact value_eq_of_den _ _ (by simp only [Term.den_dotL, den_encV]; exact hr.symm)

/-- A product of `j ≥ k` `k`-guarded nonempty terms all of whose outputs end with the value
`w` of length `k` is provably an equationally simple term followed by `w`. -/
theorem leaf_dotR {B : Ty} {w : Value B⋆} {j : ℕ} {Y : Ty} {T : Term Y B⋆}
    (hT : KProdT (valLength w) B j T) (hj : valLength w ≤ j)
    (hsuf : ∀ y : ⟦Y⟧, w.den () <:+ T.den y) :
    ∃ H : Term Y B⋆, EqSimple B H ∧ T ≡ₜ Term.dotR H w := by
  obtain ⟨v, H, hlen, hH, hTv⟩ := hT.dotR_factor
  rw [min_eq_right hj] at hlen
  have hsuf' : w.den () <:+ v.den () := by
    have h2 := hsuf (Ty.someElem Y)
    rw [congrFun (PEq.sound hTv) (Ty.someElem Y)] at h2
    simp only [Term.den_dotR] at h2
    exact suffix_of_suffix_append h2 (by simpa [valLength] using hlen)
  obtain ⟨r, hr⟩ := hsuf'
  refine ⟨Term.dotR H (encV B⋆ r), EqSimple.dotR _ hH, ?_⟩
  refine hTv.trans ?_
  refine (Term.dotR_congr (PEq.refl H) ?_).trans (PEq.symm (Term.dotR_dotR H (encV B⋆ r) w))
  exact value_eq_of_den _ _ (by simp only [Term.den_dotL, den_encV]; exact hr.symm)

/-! ### The conjugacy rule for co-pairings of `k`-guarded nonempty terms -/

/-- **The main step of the conjugacy rule (18) of Lemma 6.1.**  Given the completeness rule
for input types of list nesting depth at most `d`, the conjugacy rule holds for matching
pairs of co-pairings of `k`-guarded terms with nonempty outputs on an input type of list
nesting depth at most `d`.

The cancellation lemma (Lemma 5.5) and Lemma 6.2 are taken as hypotheses `h55` and `h62`. -/
theorem conj_hom_of_kcopair (h55 : type_of% @Lax149335.Cancellation.cancel) (h62 : type_of% @Lax149335.ConjugacyRule.conjugacy_of_syntactic)
    {B : Ty} {d : ℕ} (hconj : ConjBelow B d) {X : Ty}
    (hX : X.listDepth ≤ d) {w : Value B⋆} (m : ℕ) (hm : valLength w = m + 1)
    (k : ℕ) (hk : m ≤ k)
    (hiso : ∀ A : Ty, ProvableIso (Term.TyF.concatMap
      (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) A))
    {F G : Term X B⋆} (h : KCopair2 (m + 1) B F G) (hFG : dotR F w ≡ₜ dotL w G) :
    dotR (homT F) w ≡ₜ dotL w (homT G) := by
  -- the `k+1`-fold concatenation powers of `F` and `G`, for a bundle size `k+1 ≥ |w|`
  have hconjk : dotR ((Term.TyF.pow (k + 1)).homMap F) w ≡ₜ
      dotL w ((Term.TyF.pow (k + 1)).homMap G) :=
    ProvConjugate.homMap (Term.TyF.pow (k + 1)) (Term.TyF.pow_listFree (k + 1)) hFG
  have hden : ∀ z : ⟦(Term.TyF.pow (k + 1)).app X⟧,
      (dotR ((Term.TyF.pow (k + 1)).homMap F) w).den z =
        (dotL w ((Term.TyF.pow (k + 1)).homMap G)).den z :=
    fun z => congrFun (PEq.sound hconjk) z
  have hwlen : (w.den ()).length = m + 1 := hm
  -- the outputs of the powers start, respectively end, with `w`
  have hpre : ∀ z : ⟦(Term.TyF.pow (k + 1)).app X⟧,
      w.den () <+: ((Term.TyF.pow (k + 1)).homMap F).den z := by
    intro z
    have h1 := hden z
    simp only [Term.den_dotR, Term.den_dotL] at h1
    refine prefix_of_word_conj h1 ?_
    have := pow_homMap_den_length h.nonempty_left (k + 1) z
    omega
  have hsuf : ∀ z : ⟦(Term.TyF.pow (k + 1)).app X⟧,
      w.den () <:+ ((Term.TyF.pow (k + 1)).homMap G).den z := by
    intro z
    have h1 := hden z
    simp only [Term.den_dotR, Term.den_dotL] at h1
    refine suffix_of_word_conj h1 ?_
    have := pow_homMap_den_length h.nonempty_right (k + 1) z
    omega
  -- the joint decomposition of the two powers into co-pairings of common shape
  have hJC : JointCases B (fun {Y} T S => ∃ H H' : Term Y B⋆, EqSimple B H ∧ EqSimple B H' ∧
      T ≡ₜ Term.dotL w H ∧ S ≡ₜ Term.dotR H' w)
      ((Term.TyF.pow (k + 1)).homMap F) ((Term.TyF.pow (k + 1)).homMap G) := by
    refine JointCases.mono ?_ (JointCases.addDen (fun l => w.den () <+: l)
      (fun l => w.den () <:+ l) (h.pow_jointCases (k + 1)) hpre hsuf)
    rintro Y T S ⟨⟨hT, hS⟩, hQL, hQR⟩
    rw [← hm] at hT hS
    obtain ⟨H, hH, hTH⟩ := leaf_dotL hT (by omega) hQL
    obtain ⟨H', hH', hSH⟩ := leaf_dotR hS (by omega) hQR
    exact ⟨H, H', hH, hH', hTH, hSH⟩
  obtain ⟨Z, p, hp, hdZ, hct⟩ := hJC.toIso
  obtain ⟨H, H', hH, hH', hTp, hSp⟩ := hct.collapse
  -- the two extracted terms have the same denotation, so they are provably equal
  have hdenH : H.den = H'.den := by
    funext z
    have h1 := hden (p.den z)
    have h2 := congrFun (PEq.sound hTp) z
    have h3 := congrFun (PEq.sound hSp) z
    simp only [Term.den_comp, Term.den_dotR, Term.den_dotL] at h1 h2 h3
    rw [h2, h3] at h1
    simp only [List.append_eq, List.append_assoc] at h1
    exact List.append_cancel_right (List.append_cancel_left h1)
  have hHH' : H ≡ₜ H' := by
    obtain ⟨sH, hsH, heH⟩ := hH
    obtain ⟨sH', hsH', heH'⟩ := hH'
    have hd : sH.den = sH'.den := by
      rw [← PEq.sound heH, ← PEq.sound heH']
      exact hdenH
    exact heH.trans ((completeness_rule_of_conjBelow hconj
      (le_trans hdZ (le_trans (pow_app_listDepth X (k + 1)) hX)) sH sH' hsH hsH' hd).trans
      (PEq.symm heH'))
  -- the powers are syntactically conjugate after the isomorphism, so Lemma 6.2 applies
  have hpowconj : dotR (homT ((Term.TyF.pow (k + 1)).homMap F)) w ≡ₜ
      dotL w (homT ((Term.TyF.pow (k + 1)).homMap G)) := by
    have hsyn := h62 H w
    have e1 : homT (p ⨟ (Term.TyF.pow (k + 1)).homMap F) ≡ₜ homT (Term.dotL w H) :=
      Term.homT_congr hTp
    have e2 : homT (p ⨟ (Term.TyF.pow (k + 1)).homMap G) ≡ₜ homT (Term.dotR H w) :=
      Term.homT_congr (hSp.trans (Term.dotR_congr (PEq.symm hHH') (PEq.refl w)))
    have h3 : dotR (homT (p ⨟ (Term.TyF.pow (k + 1)).homMap F)) w ≡ₜ
        dotL w (homT (p ⨟ (Term.TyF.pow (k + 1)).homMap G)) :=
      (Term.dotR_congr e1 (PEq.refl w)).trans
        (hsyn.trans (Term.dotL_congr (PEq.refl w) (PEq.symm e2)))
    obtain ⟨p', -, hp'p⟩ := hp
    have hcancel : ∀ Fh : Term (((Term.TyF.pow (k + 1)).app X)⋆) (B⋆),
        (Term.listF p' ⨟ (Term.listF p ⨟ Fh)) ≡ₜ Fh := by
      intro Fh
      calc (Term.listF p' ⨟ (Term.listF p ⨟ Fh))
          ≡ₜ ((Term.listF p' ⨟ Term.listF p) ⨟ Fh) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.listF (p' ⨟ p) ⨟ Fh) := PEq.compL _ (PEq.list_comp _ _)
        _ ≡ₜ (Term.listF (Term.id _) ⨟ Fh) := PEq.compL _ (PEq.congr_listF hp'p)
        _ ≡ₜ (Term.id _ ⨟ Fh) := PEq.compL _ (PEq.list_id _)
        _ ≡ₜ Fh := PEq.id_comp _
    refine Term.conj_of_factor (Term.listF p') _ _ _ _ w ?_ ?_ h3
    · exact PEq.symm ((PEq.compR _ (Term.homT_precomp p _)).trans (hcancel _))
    · exact PEq.symm ((PEq.compR _ (Term.homT_precomp p _)).trans (hcancel _))
  -- the short remainder of a bundle decomposition is handled by the list-free case
  have hlt : dotR ((Term.TyF.lt k).homMap F) w ≡ₜ dotL w ((Term.TyF.lt k).homMap G) :=
    ProvConjugate.homMap (Term.TyF.lt k) (Term.TyF.lt_listFree k) hFG
  have hprod : dotR (homT ((Term.TyF.pow (k + 1)).homMap F) ⊙ (Term.TyF.lt k).homMap F) w ≡ₜ
      dotL w (homT ((Term.TyF.pow (k + 1)).homMap G) ⊙ (Term.TyF.lt k).homMap G) :=
    ProvConjugate.fdot hpowconj hlt
  -- and the bundle isomorphism of Lemma 6.7 transports the conclusion back
  obtain ⟨psi', -, hpsi2⟩ := hiso X
  have hsurj : ProvablySurjective (Term.TyF.concatMap
      (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X) := ⟨psi', hpsi2⟩
  refine ((h55 (dotR (homT F) w) (dotL w (homT G))).2 _ _ hsurj).2 ?_
  have hcmF : (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
      homT F) ≡ₜ (homT ((Term.TyF.pow (k + 1)).homMap F) ⊙ (Term.TyF.lt k).homMap F) :=
    Term.TyF.concatMap_homT _ F
  have hcmG : (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
      homT G) ≡ₜ (homT ((Term.TyF.pow (k + 1)).homMap G) ⊙ (Term.TyF.lt k).homMap G) :=
    Term.TyF.concatMap_homT _ G
  calc (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
        dotR (homT F) w)
      ≡ₜ dotR (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
          homT F) w := Term.comp_dotR _ _ _
    _ ≡ₜ dotR (homT ((Term.TyF.pow (k + 1)).homMap F) ⊙ (Term.TyF.lt k).homMap F) w :=
        Term.dotR_congr hcmF (PEq.refl w)
    _ ≡ₜ dotL w (homT ((Term.TyF.pow (k + 1)).homMap G) ⊙ (Term.TyF.lt k).homMap G) := hprod
    _ ≡ₜ dotL w (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
          homT G) := Term.dotL_congr (PEq.refl w) (PEq.symm hcmG)
    _ ≡ₜ (Term.TyF.concatMap (.prod (.list (Term.TyF.pow (k + 1))) (Term.TyF.lt k)) X ⨟
          dotL w (homT G)) := PEq.symm (Term.comp_dotL _ _ _)

/-! ### Lemma 6.1 -/

/-- The induction step for the conjugacy rule: the conjugacy rule for input types of list
nesting depth smaller than `d` implies the conjugacy rule for input types of list nesting
depth smaller than `d + 1`.

Lemmas 5.5, 6.2, 6.4, 6.5 and 6.7 are taken as hypotheses. -/
theorem conj_step (h55 : type_of% @Lax149335.Cancellation.cancel) (h62 : type_of% @Lax149335.ConjugacyRule.conjugacy_of_syntactic)
    (h64 : type_of% @Lax149335.GuardedReduction.wlog_kguarded) (h65 : type_of% @Lax149335.NonemptyReduction.wlog_nonempty)
    (h67 : type_of% @Lax149335.BundleLemma.concatMap_bundle_iso_arbitrarily_large')
    {B : Ty} {d : ℕ} (hconj : ConjBelow B d) : ConjBelow B (d + 1) := by
  intro A hA f g hf hg w hfg
  have hA' : A.listDepth ≤ d := by omega
  rcases Nat.eq_zero_or_pos (valLength w) with hk | hk
  · -- the value `w` is empty, and the conjugacy assumption just says that `f ≡ g`
    have hwnil : w ≡ₜ nilT B := by
      refine value_eq_of_den _ _ ?_
      have h0 : (w.den ()).length = 0 := hk
      simp only [Term.den_nilT]
      exact List.eq_nil_of_length_eq_zero h0
    have hfg' : f ≡ₜ g :=
      ((PEq.symm ((Term.dotR_congr (PEq.refl f) hwnil).trans (Term.dotR_nil f))).trans hfg).trans
        ((Term.dotL_congr hwnil (PEq.refl g)).trans (Term.dotL_nil g))
    calc dotR (homT f) w
        ≡ₜ dotR (homT f) (nilT B) := Term.dotR_congr (PEq.refl _) hwnil
      _ ≡ₜ homT f := Term.dotR_nil _
      _ ≡ₜ homT g := Term.homT_congr hfg'
      _ ≡ₜ dotL (nilT B) (homT g) := PEq.symm (Term.dotL_nil _)
      _ ≡ₜ dotL w (homT g) := Term.dotL_congr (PEq.symm hwnil) (PEq.refl _)
  · -- the value `w` is nonempty: reduce to co-pairings of `k`-guarded nonempty terms
    obtain ⟨m, hm⟩ : ∃ m, valLength w = m + 1 := ⟨valLength w - 1, by omega⟩
    refine h64 w hk ?_ f g hf hg hfg
    intro A₀ As f₀ g₀ fs gs hdep hkf hkg hkfs hkgs hc
    refine h65 w hk A.listDepth ?_ A₀ As f₀ g₀ fs gs hdep hkf hkg hkfs hkgs hc
    intro A₁ As₁ f₁ g₁ fs₁ gs₁ hdep₁ hkf₁ hkg₁ hkfs₁ hkgs₁ hnf₁ hng₁ hnfs₁ hngs₁ hc₁
    have hK := KCopair2.of_copair As₁ A₁ f₁ g₁ fs₁ gs₁ hkf₁ hkg₁ hnf₁ hng₁ hkfs₁ hkgs₁ hnfs₁
      hngs₁
    rw [hm] at hK
    -- Lemma 6.7 is available for arbitrarily large bundle sizes; one that is at least the
    -- length of `w` is enough
    obtain ⟨k, hk, hiso⟩ := h67 m
    exact conj_hom_of_kcopair h55 h62 hconj (le_trans hdep₁ hA') m hm k hk hiso hK hc₁

/-- **Lemma 6.1 (Completeness for simple rational terms).**  For all simple rational terms
`f, g : A → B*` and every value `w : 1 → B*`, denotational equality implies provable
equality (17), and provable `w`-conjugacy is lifted by the homomorphism combinator (18).

The assumption that `B` is a finite alphabet is kept because the paper states the lemma for
finite alphabets, but it is not used: the two rules are proved by an induction on the list
nesting depth of the input type which never appeals to it.

This is the proof of the lemma from Lemmas 5.5, 6.2, 6.4, 6.5 and 6.7, which are taken as
hypotheses; `Lax149335Proofs.completeness_simple` below discharges them. -/
theorem completeness_simple_of (h55 : type_of% @Lax149335.Cancellation.cancel) (h62 : type_of% @Lax149335.ConjugacyRule.conjugacy_of_syntactic)
    (h64 : type_of% @Lax149335.GuardedReduction.wlog_kguarded) (h65 : type_of% @Lax149335.NonemptyReduction.wlog_nonempty)
    (h67 : type_of% @Lax149335.BundleLemma.concatMap_bundle_iso_arbitrarily_large')
    {A B : Ty} (_ : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsSimple B f) (hg : IsSimple B g) (w : Value B⋆) :
    (f.den = g.den → f ≡ₜ g) ∧
    (dotR f w ≡ₜ dotL w g → dotR (homT f) w ≡ₜ dotL w (homT g)) := by
  have key : ∀ d : ℕ, ConjBelow B d := by
    intro d
    induction d with
    | zero => intro A hA; omega
    | succ d ih => exact conj_step h55 h62 h64 h65 h67 ih
  exact ⟨fun hden => completeness_rule_of_conjBelow (key A.listDepth) le_rfl f g hf hg hden,
    key (A.listDepth + 1) (by omega) f g hf hg w⟩

/-- **Lemma 6.1 (Completeness for simple rational terms).** -/
theorem completeness_simple {A B : Ty} (hB : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsSimple B f) (hg : IsSimple B g) (w : Value B⋆) :
    (f.den = g.den → f ≡ₜ g) ∧
    (dotR f w ≡ₜ dotL w g → dotR (homT f) w ≡ₜ dotL w (homT g)) :=
  completeness_simple_of cancel conjugacy_of_syntactic wlog_kguarded wlog_nonempty
    concatMap_bundle_iso_arbitrarily_large' hB f g hf hg w

end Lax149335Proofs

bridge_export Lax149335Proofs
