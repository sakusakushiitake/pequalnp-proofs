import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

private def words (line : String) : List String :=
  line.splitOn " " |>.filter (· != "")

-- The CNF exporter emits one clause per line and no DIMACS comments.
private def parseDimacs (data : String) : Except String (CNF Nat) := do
  let lines := data.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (· != "")
  let header :: clauses := lines | throw "missing DIMACS header"
  let ["p", "cnf", variables, count] := words header | throw "invalid DIMACS header"
  let some n := variables.toNat? | throw "invalid variable count"
  let some m := count.toNat? | throw "invalid clause count"
  if clauses.length != m then throw "clause count mismatch"
  let result ← clauses.toArray.mapM fun line => do
    let "0" :: tokens := (words line).reverse | throw "clause lacks zero terminator"
    let lits ← tokens.reverse.mapM fun token => do
      let some i := token.toInt? | throw "invalid literal"
      if i == 0 || i.natAbs > n then throw "literal outside DIMACS variable range"
      return (i.natAbs - 1, i > 0)
    return CNF.Clause.ofLiterals lits
  return ⟨result⟩

def main (args : List String) : IO UInt32 := do
  let [cnfPath, certPath] := args | throw (IO.userError "usage: checker .cnf .lrat")
  let .ok cnf := parseDimacs (← IO.FS.readFile cnfPath)
    | throw (IO.userError s!"invalid DIMACS: {cnfPath}")
  let .ok cert := LRAT.parseLRATProof (← IO.FS.readBinFile certPath)
    | throw (IO.userError s!"invalid LRAT: {certPath}")
  if LRAT.check cert cnf then
    IO.println s!"Verified UNSAT: {cnfPath} ({cert.size} LRAT actions)"
    return 0
  else
    IO.eprintln s!"LRAT certificate rejected: {cnfPath}"
    return 1
