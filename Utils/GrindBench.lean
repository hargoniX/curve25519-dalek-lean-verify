import Mathlib.Init
import Mathlib.Tactic.TacticAnalysis
import Lean.Meta.Tactic.Grind.Main

register_option linter.tacticAnalysis.grindBench : Bool := {
  defValue := true
}

namespace GrindBench

open Mathlib Lean Grind Elab Meta

def maxHeartbeats : Nat := 20000

def grindConfig : Grind.Config := { ring := false, linarith := false }

def forbiddenEmatchDecls : Array Name := #[]

structure TheoremStats where
  theoremName : String
  moduleName : String
  success : Bool
  timeMs : Nat

def TheoremStats.toCsv (stats : TheoremStats) : String :=
  s!"{stats.theoremName},{stats.moduleName},{stats.success},{stats.timeMs}\n"

structure EmatchStats where
  theoremName : String
  moduleName : String
  counters: Array (Grind.Origin × Nat)

def EmatchStats.toCsv (stats : EmatchStats) : String := Id.run do
  let mut s := ""
  for (origin, count) in stats.counters do
    let origin :=
      match origin with
      | .decl name => name.toString
      | .fvar .. | .local .. => "local_theorem"
      | .stx .. => unreachable!
    s := s ++ s!"{stats.theoremName},{stats.moduleName},{origin},{count}\n"
  return s

structure State where
  fileCounter : Std.TreeMap String Nat := {}
  theoremCounter : Std.TreeMap String Nat := {}
  deriving Inhabited

initialize grindBenchRef : IO.Ref State ← IO.mkRef {}

@[tacticAnalysis linter.tacticAnalysis.grindBench]
def grindBench : TacticAnalysis.Config where
  run nodes := do
    let filePath ← getFileName
    let some dir := System.FilePath.parent filePath | return ()
    let some fileName := System.FilePath.fileStem filePath | return ()

    let fileIdx : Nat ← grindBenchRef.modifyGet fun s =>
      let currIdx := s.theoremCounter.getD filePath 0
      (currIdx, { s with theoremCounter := s.theoremCounter.insert filePath (currIdx + 1) })

    let goalCsv ← IO.FS.Handle.mk (dir / s!"{fileName}_{fileIdx}.goals.csv") .write
    goalCsv.putStrLn "theorem,module,success,timems"
    let ematchCsv ← IO.FS.Handle.mk (dir / s!"{fileName}_{fileIdx}.ematch.csv") .write
    ematchCsv.putStrLn "theorem,module,ematchthm,count"

    for node in nodes do
      let some declName := node.ctxI.parentDecl? | continue
      if ← isBlackListed declName then continue

      let identifier := s!"{fileName}_{declName}"
      let idx : Nat ← grindBenchRef.modifyGet fun s =>
        let currIdx := s.theoremCounter.getD identifier 0
        (currIdx, { s with theoremCounter := s.theoremCounter.insert identifier (currIdx + 1) })
      let identifier := s!"{identifier}_{idx}"

      let mut localIdx := 0
      for goal in node.tacI.goalsBefore do
        let (success, counters, timeMs) ← node.ctxI.runTactic node.tacI goal fun goal => do
          let params ← Grind.mkDefaultParams grindConfig
          let params := {
            params with
              extensions := params.extensions.map fun s =>
                { s with
                  ematch := forbiddenEmatchDecls.foldl (init := s.ematch) (·.erase <| .decl ·)
                }
          }
          let startMs ← IO.monoMsNow
          let result ← analyzeTarget goal params
          let endMs ← IO.monoMsNow
          let time := endMs - startMs
          match result with
          | some result =>
            return (result.failure?.isNone, result.counters.thm.toArray, time)
          | none =>
            return (true, #[], time)
        let theoremName := s!"{identifier}_{localIdx}"
        goalCsv.putStr <| TheoremStats.toCsv <| {
          theoremName := theoremName
          moduleName := filePath
          success := success
          timeMs := timeMs
        }
        ematchCsv.putStr <| EmatchStats.toCsv {
          theoremName := theoremName
          moduleName := filePath
          counters := counters
        }
        localIdx := localIdx + 1
where
  analyzeTarget (mvar : MVarId) (params : Grind.Params) : MetaM (Option Grind.Result) := do
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := maxHeartbeats * 1000 }) do
        withCurrHeartbeats do
          let res ← Grind.main mvar params
          return some res)
      (fun _ => return none)

  isBlackListed (declName : Name) : Command.CommandElabM Bool := do
    match ← findDeclarationRanges? declName with
    | some _ =>
      let env ← getEnv
      let isPrivate := (`_private).isPrefixOf declName
      pure (declName.isInternal && !isPrivate)
      <||> (pure <| isAuxRecursor env declName)
      <||> (pure <| isNoConfusion env declName)
      <||> (pure <| declName.isInternalDetail && !isPrivate)
      <||> isRec declName
      <||> isMatcher declName
    | none => return true

end GrindBench
