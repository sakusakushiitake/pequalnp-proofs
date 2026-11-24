import Research.FiveUpperGroup1
import Research.FiveUpperGroup2
import Research.FiveUpperGroup3
import Research.FiveUpperGroup4
import Research.FiveUpperGroup5
import Research.FiveUpperGroup6

namespace PlaneResearch.FiveUpperAtlas
open PlaneResearch.FiveUpperTables
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rows : List Row := FiveUpperGroup1.rows ++ FiveUpperGroup2.rows ++ FiveUpperGroup3.rows ++
  FiveUpperGroup4.rows ++ FiveUpperGroup5.rows ++ FiveUpperGroup6.rows

theorem cardinality : rows.length=180 := by decide +kernel
set_option maxRecDepth 10000 in
theorem distinct_tables : (rows.map Prod.fst).Nodup := by decide +kernel

theorem all_checked : rows.all checked=true := by
  simp [rows,FiveUpperGroup1.verified,FiveUpperGroup2.verified,FiveUpperGroup3.verified,
    FiveUpperGroup4.verified,FiveUpperGroup5.verified,FiveUpperGroup6.verified]

theorem explicit_upper (r : Row) (mem : r ∈ rows) :
    (circuit r).size=r.2.1 ∧ Monotone2 (circuit r) ∧
    ∀ x : Fin 5 → Bool, (circuit r).eval (List.ofFn x)=r.1.testBit (code x) :=
  checked_sound r (List.all_eq_true.mp all_checked r mem)

end PlaneResearch.FiveUpperAtlas
