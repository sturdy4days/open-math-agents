import ActualChild
import ArticleBoth
import Mathlib.Tactic.FinCases

/-! All upper bounds in the published small-values table, using the compiled order-eight
and order-nine certificate and explicit blockers at orders eleven and twelve. -/

open SimpleGraph
namespace E1182Complete
open OMA.R_Erdos1182_erdos_1182_variants_small_values_R2

/-- Every vertex order from four through twelve has the claimed upper edge bound. -/
theorem upper_table (k : Fin 9) :
    Erdos1182.f (k.val + 4) ≤ (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k := by
  classical
  have small := (show H3 from OMA.solution)
  have blockers := SmallTable.Blockers.combineFamilies small.1 small.2 (by
    intro j
    fin_cases j
    · obtain ⟨r,m,tri,cap⟩ := E1182Ten.ten
      exact ⟨r,_,tri,fun f _ => cap f⟩
    · exact explicit_hosts fixed_hosts 0
    · exact explicit_hosts fixed_hosts 1)
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  have large : 2 ≤ n := by dsimp [n]; omega
  have critical : n-1≤q+1 := by fin_cases k <;> decide
  unfold Erdos1182.f
  apply csSup_le'
  rintro z ⟨B,connected,rfl,good⟩
  change B.edgeSet.ncard ≤ q
  by_contra! high
  obtain ⟨T,sub,ct,size⟩ := SmallTable.Dense.intermediate connected critical (by omega)
  obtain ⟨C,free,miss⟩ := blockers k T ct size
  exact miss (((SmallTable.Dense.good_iff large connected).mp good C free).mono_left sub)

/-- The upper half of every lower-case extremal value in the article, orders two through twelve. -/
theorem article_upper_table (i : Fin 11) :
    Erdos1182.f (i.val+2) ≤ (![1,2,5,8,12,16,20,27,33,41,49] : Fin 11 → ℕ) i := by
  fin_cases i
  · exact OMA.f_two.le
  · exact SmallTable.Dense.base.le
  · exact upper_table 0
  · exact upper_table 1
  · exact upper_table 2
  · exact upper_table 3
  · exact upper_table 4
  · exact upper_table 5
  · exact upper_table 6
  · exact upper_table 7
  · exact upper_table 8

/-- The published parent already supplies the sparse upper bounds independently. -/
theorem article_both_upper_tables (i : Fin 11) :
    Erdos1182.F (i.val+2) ≤ (![1,2,5,7,8,11,11,16,18,23,23] : Fin 11 → ℕ) i ∧
    Erdos1182.f (i.val+2) ≤ (![1,2,5,8,12,16,20,27,33,41,49] : Fin 11 → ℕ) i := by
  refine ⟨?_, article_upper_table i⟩
  fin_cases i
  · exact OMA.F_two.le
  · exact SmallTable.Sparse.upper3
  · exact SmallTable.Sparse.upper4
  · exact SmallTable.Sparse.upper5
  · exact SmallTable.Sparse.upper6
  · exact SmallTable.Sparse.upper7
  · exact SmallTable.Sparse.upper8
  · exact SmallTable.Sparse.upper9
  · exact SmallTable.Sparse.upper10
  · exact SmallTable.Sparse.upper11
  · exact SmallTable.Sparse.upper12

theorem original_of_two_remaining (sparse : H1) (census : H2) :
    type_of% @Erdos1182.erdos_1182.variants.small_values :=
  OMA.R_Erdos1182_erdos_1182_variants_small_values_R2.main sparse census OMA.solution fixed_hosts

end E1182Complete
#print axioms E1182Complete.upper_table
#print axioms E1182Complete.article_upper_table
#print axioms E1182Complete.article_both_upper_tables
#print axioms E1182Complete.original_of_two_remaining
