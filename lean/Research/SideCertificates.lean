import Research.SideTables

namespace PlaneResearch.SideCertificates
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace seven234

def R : Finset (Table 7) := {0,1,2,4,8,16,32,127}
def T : Finset (Table 7) := {5,11,22,24,34,44,49}
def plan : List (Table 7 × List (Finset (Table 7))) := [
  (11,[{3},{9},{10},{116},{15,27},{15,43},{15,59},{15,75},{15,91},{15,107},{15,123},{27,43},{27,47},{27,75},{27,79},{27,107},{27,111},{31,43},{31,75},{31,107},{43,75},{43,79},{43,91},{43,95},{47,75},{47,91},{59,75},{59,79},{63,75}]),
  (22,[{6},{18},{20},{105},{23,30},{23,54},{23,62},{23,86},{23,94},{23,118},{23,126},{30,54},{30,55},{30,86},{30,87},{30,118},{30,119},{31,54},{31,86},{31,118},{54,86},{54,87},{54,94},{54,95},{55,86},{55,94},{62,86},{62,87},{63,86}]),
  (44,[{12},{36},{40},{83},{45,46},{45,60},{45,62},{45,108},{45,110},{45,124},{45,126},{46,60},{46,61},{46,108},{46,109},{46,124},{46,125},{47,60},{47,108},{47,124},{60,108},{60,109},{60,110},{60,111},{61,108},{61,110},{62,108},{62,109},{63,108}]),
  (49,[{17},{33},{48},{78},{51,53},{51,57},{51,61},{51,113},{51,117},{51,121},{51,125},{53,57},{53,59},{53,113},{53,115},{53,121},{53,123},{55,57},{55,113},{55,121},{57,113},{57,115},{57,117},{57,119},{59,113},{59,117},{61,113},{61,115},{63,113}])]

private lemma full_plan : checkPlan R T plan = true := by decide +kernel
private lemma fails : possible 3 ∅ (plan.map Prod.snd) = false := by decide +kernel

theorem lower (gs : List Gate) (w : List (Table 7)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : 11 ≤ gs.length := by
  have needed : ∀ v ∈ plan, v.1 ∈ T := by
    intro v hv
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl
    all_goals decide
  have h := recipe_lower R T 3 plan (by decide) (by decide) (by decide) needed
    (recipes_checked R T plan full_plan) fails gs w ok raw hit
  have card : T.card = 7 := by decide
  simpa only [card] using h

end seven234

namespace seven468

def R : Finset (Table 6) := {0,1,2,4,8,16,63}
def T : Finset (Table 6) := {5,6,11,12,17,18,24}
def plan : List (Table 6 × List (Finset (Table 6))) := [
  (11,[{3},{9},{10},{52},{15,27},{15,43},{15,59},{27,43},{27,47},{31,43}])]

private lemma full_plan : checkPlan R T plan = true := by decide +kernel
private lemma fails : possible 0 ∅ (plan.map Prod.snd) = false := by decide +kernel

theorem lower (gs : List Gate) (w : List (Table 6)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : 8 ≤ gs.length := by
  have needed : ∀ v ∈ plan, v.1 ∈ T := by
    intro v hv
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    all_goals decide
  have h := recipe_lower R T 0 plan (by decide) (by decide) (by decide) needed
    (recipes_checked R T plan full_plan) fails gs w ok raw hit
  have card : T.card = 7 := by decide
  simpa only [card] using h

end seven468

namespace eight468

def R : Finset (Table 6) := {0,1,2,4,8,16,63}
def T : Finset (Table 6) := {3,5,6,10,12,18,20,25}
def plan : List (Table 6 × List (Finset (Table 6))) := [
  (25,[{9},{17},{24},{38},{27,29},{27,57},{27,61},{29,57},{29,59},{31,57}])]

private lemma full_plan : checkPlan R T plan = true := by decide +kernel
private lemma fails : possible 0 ∅ (plan.map Prod.snd) = false := by decide +kernel

theorem lower (gs : List Gate) (w : List (Table 6)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : 9 ≤ gs.length := by
  have needed : ∀ v ∈ plan, v.1 ∈ T := by
    intro v hv
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    all_goals decide
  have h := recipe_lower R T 0 plan (by decide) (by decide) (by decide) needed
    (recipes_checked R T plan full_plan) fails gs w ok raw hit
  have card : T.card = 8 := by decide
  simpa only [card] using h

end eight468

end PlaneResearch.SideCertificates
