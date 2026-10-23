import Lean
import Lax149335

/-!
# Names of the concepts in the proof development

The proof development refers to the notions of the paper by short names, such as `Ty`,
`Term`, `Term.either` or `PEq`. The notions themselves are defined in the concept package,
each under the name of its concept module: `Lax149335.Types.Ty`,
`Lax149335.Terms.Term`, `Lax149335.DerivedTerms.Term.either`,
`Lax149335.EquationalTheory.PEq`, and so on.

The command `bridge_concepts` below makes every definition of the concept package available
in the proof development under its short name, as an *alias* `Lax149335Proofs.Ty`,
`Lax149335Proofs.Term`, … . The command `bridge_export`, issued at the end of every file of
the development, makes the lemmas that the file proves about a concept available for
generalized field notation, e.g. `h.symm` for `h : f ≡ₜ g`. Aliases are not declarations,
so neither command adds anything to the environment beyond names.
-/

open Lean Elab Command

namespace Lax149335Proofs.Bridge

/-- Register every proper prefix of `n` as a namespace. -/
def registerPrefixes (n : Name) : CommandElabM Unit := do
  let mut p := n.getPrefix
  while !p.isAnonymous do
    modifyEnv fun env => env.registerNamespace p
    p := p.getPrefix

/-- `bridge_concepts C => P` aliases every definition `C.M.rest` of a concept module `C.M`
as `P.rest`. In addition, when `rest` is `X.y` and `P.X` is an alias of a constant `D` of
another concept module, it aliases `C.M.rest` as `D.y`, for generalized field notation. -/
elab "bridge_concepts " src:ident " => " dst:ident : command => do
  let s := src.getId
  let d := dst.getId
  let mut targets : Array (Name × Name) := #[]
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless s.isPrefixOf m && m != s do continue
    for n in env.header.moduleData[i]!.constNames do
      unless m.isPrefixOf n do continue
      if n.isInternalDetail then continue
      if let some (.axiomInfo _) := env.find? n then continue
      targets := targets.push (n, n.replacePrefix m .anonymous)
  for (n, rest) in targets do
    let a := d ++ rest
    modifyEnv fun env => addAlias env a n
    registerPrefixes a
  let env ← getEnv
  for (n, rest) in targets do
    match rest with
    | .str x y =>
      unless x.isAnonymous do
        for c in getAliases env (d ++ x) (skipProtected := false) do
          if c != n.getPrefix then
            modifyEnv fun env => addAlias env (.str c y) n
    | _ => pure ()

/-- `bridge_export P` aliases every constant `P.X.y` declared in the current module, where
`P.X` is an alias of a constant `D`, as `D.y`, for generalized field notation. -/
elab "bridge_export " dst:ident : command => do
  let env ← getEnv
  let d := dst.getId
  for (n, _) in env.constants.map₂.toList do
    if n.isInternalDetail then continue
    unless d.isPrefixOf n do continue
    match n with
    | .str pre last =>
      for c in getAliases env pre (skipProtected := false) do
        modifyEnv fun env => addAlias env (.str c last) n
    | _ => pure ()

end Lax149335Proofs.Bridge

bridge_concepts Lax149335 => Lax149335Proofs
