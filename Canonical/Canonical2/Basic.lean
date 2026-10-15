module

public import Lean.Expr
public import Lean.Meta.Basic
public import Canonical.Canonical2.Util
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.SimpTrace
import Lean.Elab.Tactic.Grind.Main
import Lean.Elab.Tactic.Grind.Param
import Lean.Meta.Tactic.ExposeNames
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
import Canonical.Symbols

open Lean Meta Expr Elab Tactic

namespace Canonical2

public section

def automateSimp (mvar : MVarId) (suggestions : Array Name) (closerOnly : Bool) : MetaM NameSet := mvar.run do
  let mut argsArray := #[]
  for sugg in suggestions do
    let ident := mkIdent sugg
    let candidates ← resolveGlobalConst ident
    for candidate in candidates do
      let arg ← `(Parser.Tactic.simpLemma| $(mkCIdentFrom ident candidate (canonical := true)):term)
      argsArray := argsArray.push arg
  let stx ← if argsArray.isEmpty then `(tactic| simp_all) else `(tactic| simp_all [$argsArray,*])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (simpMVar, stats) ← simpAll mvar ctx simprocs
  let stx ← mkSimpCallStx (← `(tactic| simp_all)) stats.usedTheorems
  if let some simpMVar := simpMVar then
    if closerOnly then throwError "failed"
    mvar.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax (← `(term| by
      $stx
      exact $(TSyntax.mk .missing))))) (← instantiateMVars (.mvar simpMVar)))
    return {}
  else
    let stx ← `(term| by $stx:tactic)
    mvar.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax stx)) (← instantiateMVars (.mvar mvar)))
    collectConstants stx mvar

def preprocess (mvar : MVarId) : MetaM Unit := do
  let mvar := (← mvar.introNP (getIntrosSize (← mvar.getType))).2
  let mvar ← mvar.exposeNames
  try let _ ← mvar.applyRfl
  catch _ =>
    try let _ ← automateSimp mvar #[] false
    catch _ => return

def grindPremise (declName : Name) : MetaM Bool := do try
    let _ ← Lean.Elab.Tactic.addEMatchTheorem (← Grind.mkDefaultParams {})
      (mkIdent declName) declName (.default false) false
    return true
  catch _ => return false

def automateGrind (mvar : MVarId) (premises : Array Name) : MetaM NameSet := do
  let premises ← premises.filterM grindPremise
  let cc : Array (TSyntax `Lean.Parser.Tactic.grindParam) ← premises.mapM
    (Grind.globalDeclToGrindParamSyntax · (.default false) false)
  let stx ← mvar.run do evalGrindTraceCore (← `(tactic| grind? [$cc,*])) (useSorry := false)
  let stx := stx[stx.size - 2]!
  mvar.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax (← `(term| by $stx:tactic)))) (← instantiateMVars (.mvar mvar)))
  collectConstants stx mvar

def automateLibrarySearch (mvar : MVarId) : MetaM NameSet := do
  if let some _ ← mvar.withContext do LibrarySearch.librarySearch mvar then
    throwError "No proof found."
  return {}

def automateTasks (mvar : MVarId) (names : Array Name) (_timeout : UInt64 := 30) : MetaM (List (MetaTask (NameSet))) := do
  return [← (automateGrind mvar names).toTask, ← (automateLibrarySearch mvar).toTask]

def automate (mvar : MVarId) (names : Array Name) (timeout : UInt64 := 30) : MetaM (MetaTask Unit) := do
  let tasks ← automateTasks mvar names timeout
  MetaM.toTask (cancel := tasks.forM (·.cancel)) do
    if let .ok (_, state, ctx) := (← CancelableTask.race tasks).task.get then
      modifyThe Core.State (fun _ => state)
      modifyThe Meta.State (fun _ => ctx)
      return
    else
      throwError "No proof found."

def sorryToMVar (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := fun sub => do
    if isSorry sub then
      return .done (← mkFreshExprMVar (userName := `h) (← inferType sub))
    else return .continue
  )

def assignLet (mvar : MVarId) (name : Name) (type : Expr) : MetaM (MVarId × MVarId × FVarId) := do
  let value ← mkFreshExprMVar (userName := name) (kind := .syntheticOpaque) type
  withLetDecl name type value (nondep := true) fun fvar => do
    let body ← mkFreshExprMVar (userName := ((← getMCtx).getDecl mvar).userName) (kind := .syntheticOpaque) (← mvar.getType)
    mvar.assign (← mkLambdaFVars #[fvar] (usedLetOnly := false) (generalizeNondepLet := false) body)
    return (value.mvarId!, body.mvarId!, fvar.fvarId!)

def addSubgoal (mvar' : MVarId) (name : Name) (type : Expr) (clear : Array Name) : MetaM FVarId := do
  let mvar ← mvar'.withContext do
    let sorted ← sortFVarIds (← clear.mapM (fun x => do pure (← getFVarFromUserName x).fvarId!))
    sorted.reverse.foldlM MVarId.tryClear mvar'
  if ← mvar'.isAssigned then
    let cc : Array (TSyntax `ident) := clear.map mkIdent
    mvar'.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax (← `(term| by
    clear $cc*
    exact $(TSyntax.mk .missing))))) (← instantiateMVars (.mvar mvar')))
  mvar.withContext do
    let (value, _, h) ← assignLet mvar name (← sorryToMVar type)
    let _ ← preprocess value
    return h
