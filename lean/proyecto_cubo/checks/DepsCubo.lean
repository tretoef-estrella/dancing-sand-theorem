import RequestProject.MainTheorem.All
import RequestProject.BaiCounts.All
import RequestProject.PodiumCor.All
import RequestProject.Mirror.All
import RequestProject.FoldLaw.All
import RequestProject.OddParts.All
import RequestProject.Windows.All

/-! Dependency cone of the headline theorems of «The Dancing Sand Theorem» (Grepy Escribano,
10 October 2026; modelled on the Chaise's `DepsPares.lean`). For each headline theorem: the number of
project declarations (namespace `RequestProject.*` modules) in its transitive cone, and how many come
from each module. The last command gives the union cone of all headline theorems together. -/

open Lean Elab Command

partial def collect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    for c in ci.getUsedConstantsAsSet.toList do
      acc := collect env c acc
    return acc

def report (env : Environment) (s : NameSet) (title : String) : CommandElabM Unit := do
  let mut mods : Std.HashMap Name Nat := {}
  let mut total := 0
  for n in s.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        total := total + 1
        mods := mods.insert m (mods.getD m 0 + 1)
    | none => pure ()
  logInfo m!"{title}: project decls in cone: {total}; modules: {mods.size}"
  for (m, c) in mods.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"{m} {c}"

elab "#deps " id:ident : command => do
  let env ← getEnv
  report env (collect env id.getId {}) id.getId.toString

elab "#depsall " ids:ident* : command => do
  let env ← getEnv
  let mut s : NameSet := {}
  for i in ids do
    s := collect env i.getId s
  report env s "UNION"

#deps MainTheorem.M1
#deps Windows.theorem_D_i
#deps BaiCounts.B2
#deps PodiumCor.G1
#deps Mirror.Y2
#deps FoldLaw.DW
#deps FoldLaw.DW'
#deps FoldLaw.R
#deps OddParts.B1
#deps OddParts.C5
#depsall MainTheorem.M1 MainTheorem.M2 Windows.theorem_D_i BaiCounts.B1 BaiCounts.B2 PodiumCor.G1 PodiumCor.G2 PodiumCor.G3 Mirror.Y2 FoldLaw.H FoldLaw.DW FoldLaw.DW' FoldLaw.L1 FoldLaw.R OddParts.B1 OddParts.C5
