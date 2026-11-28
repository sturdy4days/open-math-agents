import OMAStatements.S_mo_239951
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Koen's counterexample in MathOverflow answer 241706 to question 239951
uses the two parts of a regular complete bipartite graph. On the graph
with four vertices in each part the sign vector has eigenvalue -3/5.
-/

namespace BipartiteMetropolis
open OMA.S_mo_239951

def graph : SimpleGraph (Fin 8) where
  Adj i j := (i.val < 4 ∧ 4 ≤ j.val) ∨ (j.val < 4 ∧ 4 ≤ i.val)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> exact (Nat.not_lt_of_ge h.2) h.1⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem connected : graph.Connected := by
  apply graph.connected_iff_exists_forall_reachable.mpr
  refine ⟨0, fun i => ?_⟩
  by_cases hi : i.val < 4
  · have a : graph.Adj (0 : Fin 8) 4 := by decide
    have b : graph.Adj (4 : Fin 8) i := Or.inr ⟨hi, by decide⟩
    exact a.reachable.trans b.reachable
  · exact (show graph.Adj (0 : Fin 8) i from Or.inl ⟨by decide, Nat.le_of_not_lt hi⟩).reachable

theorem degree_four : ∀ i, graph.degree i = 4 := by decide

def signs (i : Fin 8) : ℝ := if i.val < 4 then 1 else -1

theorem eigen : (transition graph).mulVec signs = (-3 / 5 : ℝ) • signs := by
  funext i
  have diag (v : Fin 8) :
      (∑ k ∈ graph.neighborFinset v, (1 : ℝ) / ((max (graph.degree v) (graph.degree k) : ℕ) + 1)) = 4/5 := by
    simp only [degree_four, max_self, Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
    norm_num
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply,
      transition, diag, degree_four, graph, signs, Fin.isValue] <;> simp +decide <;> norm_num

end BipartiteMetropolis

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239951.main) := by
  intro all
  have nz : BipartiteMetropolis.signs ≠ 0 := by
    intro h
    have w := congrFun h (0 : Fin 8)
    norm_num [BipartiteMetropolis.signs] at w
  have h := all (Fin 8) BipartiteMetropolis.graph BipartiteMetropolis.connected
    (-3/5) BipartiteMetropolis.signs nz BipartiteMetropolis.eigen
  norm_num at h
