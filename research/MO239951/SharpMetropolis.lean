import OMAStatements.S_mo_239951
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-!
# Sharp lower eigenvalue bound for the Metropolis-Hastings walk on a finite graph

Ronn3y gives the bound (1-Δ)/(1+Δ) via Gershgorin's circles in MathOverflow
answer 240451. Koen exhibits the equality examples K_{d,d} in answer 241706.
This file proves the bound for the registered operator of @etaubman, formalizes
those examples at every positive degree, and characterizes all connected equality
cases. A connected graph attains the bound exactly when it is regular and bipartite.
For an eigenvector attaining it, the absolute value is constant, and signs switch
across every edge. Evaluation at any vertex is injective on this eigenspace.

Source question: https://mathoverflow.net/q/239951
Row bound: https://mathoverflow.net/a/240451
Sharp family: https://mathoverflow.net/a/241706
-/

open Finset OMA.S_mo_239951

namespace MetropolisSharp
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edge (i j : V) : ℝ :=
  if G.Adj i j then 1 / ((max (G.degree i) (G.degree j) : ℕ) + 1) else 0

noncomputable def load (i : V) : ℝ := ∑ j, edge G i j

omit [DecidableEq V] in
lemma edge_nonneg (i j : V) : 0 ≤ edge G i j := by unfold edge; split <;> positivity
omit [DecidableEq V] in
lemma edge_pos {i j : V} (h : G.Adj i j) : 0 < edge G i j := by simp only [edge, if_pos h]; positivity

omit [DecidableEq V] in
lemma load_eq (i : V) : load G i = ∑ j ∈ G.neighborFinset i,
    (1 : ℝ) / ((max (G.degree i) (G.degree j) : ℕ) + 1) := by
  rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rfl

lemma row (v : V → ℝ) (i : V) : (transition G).mulVec v i =
    (1 - load G i) * v i + ∑ j, edge G i j * v j := by
  have hij (j : V) : transition G i j * v j =
      (if j = i then (1-load G i)*v i else 0) + edge G i j * v j := by
    by_cases h : i=j
    · subst j
      simp [transition, load_eq, edge]
    · simp [transition, edge, h, Ne.symm h, ite_mul]
  simp only [Matrix.mulVec, dotProduct, hij, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

omit [DecidableEq V] in
lemma load_le (i : V) : load G i ≤ (G.degree i : ℝ)/((G.degree i : ℝ)+1) := by
  rw [load_eq]
  calc
    _ ≤ ∑ _j ∈ G.neighborFinset i, (1 : ℝ)/((G.degree i : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
      exact le_max_left _ _
    _ = _ := by simp [SimpleGraph.card_neighborFinset_eq_degree, div_eq_mul_inv]

end MetropolisSharp

open Finset OMA.S_mo_239951
namespace MetropolisSharp
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The row estimate at a positive extremum includes its equality conditions. -/
theorem positive_extreme {D : ℕ} {l : ℝ} (w : V → ℝ) (i : V) (hi : 0 < w i)
    (small : ∀ j, -w i ≤ w j) (deg : G.degree i ≤ D)
    (eig : (transition G).mulVec w = l • w) :
    (1 - (D : ℝ))/(1 + D) ≤ l ∧
    (l = (1 - (D : ℝ))/(1 + D) → G.degree i = D ∧ ∀ j, G.Adj i j → w j = -w i) := by
  let L := load G i
  have eval := congrFun eig i
  rw [row] at eval
  change (1-L)*w i + ∑ j, edge G i j*w j = l*w i at eval
  have gap : ∑ j, edge G i j*(w j+w i) = (l-(1-2*L))*w i := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    change (∑ j, edge G i j*w j) + L*w i = _
    linear_combination eval
  have term (j : V) : 0 ≤ edge G i j*(w j+w i) :=
    mul_nonneg (edge_nonneg G i j) (by linarith [small j])
  have minrow : 1-2*L ≤ l := by
    have nonneg := Finset.sum_nonneg (s := Finset.univ) (fun j _ => term j)
    rw [gap] at nonneg
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left nonneg hi)
  have hcast : (G.degree i : ℝ) ≤ D := by exact_mod_cast deg
  have loadD : L ≤ (D : ℝ)/((D : ℝ)+1) :=
    (load_le G i).trans ((div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith))
  have hD : (1 - (D : ℝ))/(1 + D) = 1 - 2*((D : ℝ)/((D : ℝ)+1)) := by
    field_simp
    ring
  rw [hD]
  refine ⟨by linarith, fun heq => ?_⟩
  have eqload : L = (D : ℝ)/((D : ℝ)+1) := by linarith
  refine ⟨?_, ?_⟩
  · by_contra hn
    have hlt : (G.degree i : ℝ) < D := by exact_mod_cast lt_of_le_of_ne deg hn
    have t : (G.degree i : ℝ)/((G.degree i : ℝ)+1) < (D : ℝ)/((D : ℝ)+1) :=
      (div_lt_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
    exact (lt_of_le_of_lt (load_le G i) t).ne eqload
  · intro j adj
    have zero : ∑ k, edge G i k*(w k+w i) = 0 := by rw [gap, heq, eqload]; ring
    have hz := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg term).mp zero) j
    change edge G i j*(w j+w i) = 0 at hz
    have := (mul_eq_zero.mp hz).resolve_left (edge_pos G adj).ne'
    linarith

theorem abs_extreme {D : ℕ} {l : ℝ} (v : V → ℝ) (i : V) (hi : 0 < |v i|)
    (large : ∀ j, |v j| ≤ |v i|) (deg : G.degree i ≤ D)
    (eig : (transition G).mulVec v = l • v) :
    (1 - (D : ℝ))/(1 + D) ≤ l ∧
    (l = (1 - (D : ℝ))/(1 + D) → G.degree i = D ∧ ∀ j, G.Adj i j → v j = -v i) := by
  by_cases s : 0 ≤ v i
  · rw [abs_of_nonneg s] at hi large
    exact positive_extreme G v i hi (fun j => (abs_le.mp (large j)).1) deg eig
  · rw [abs_of_neg (lt_of_not_ge s)] at hi large
    have neig : (transition G).mulVec (-v) = l • (-v) := by rw [Matrix.mulVec_neg, eig, smul_neg]
    obtain ⟨bound,eqcond⟩ := positive_extreme G (-v) i hi (fun j => by
      change - -v i ≤ -v j
      linarith [(abs_le.mp (large j)).2]) deg neig
    refine ⟨bound, fun eq => ⟨(eqcond eq).1,fun j adj => ?_⟩⟩
    have r := (eqcond eq).2 j adj
    change -v j = - -v i at r
    linarith

omit [DecidableEq V] in
theorem extremal_vertex (v : V → ℝ) (nz : v ≠ 0) :
    ∃ i, 0 < |v i| ∧ ∀ j, |v j| ≤ |v i| := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact nz (funext h)
  obtain ⟨i,_,best⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) ⟨j,Finset.mem_univ j⟩
  exact ⟨i,lt_of_lt_of_le (abs_pos.mpr hj) (best j (Finset.mem_univ _)),fun k => best k (Finset.mem_univ _)⟩

theorem lower_bound (D : ℕ) (deg : ∀ i, G.degree i ≤ D) (l : ℝ) (v : V → ℝ)
    (nz : v ≠ 0) (eig : (transition G).mulVec v = l • v) : (1-(D:ℝ))/(1+D) ≤ l := by
  obtain ⟨i,hi,hmax⟩ := extremal_vertex v nz
  exact (abs_extreme G v i hi hmax (deg i) eig).1

end MetropolisSharp

namespace BipartiteMetropolis
open OMA.S_mo_239951

/-- On a regular graph, a vector alternating across every edge attains the
lower endpoint determined by the degree. -/
theorem regular_bipartite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (regular : ∀ i, G.degree i = d)
    (s : V → ℝ) (opposite : ∀ i j, G.Adj i j → s j = -s i) :
    (transition G).mulVec s = ((1-(d:ℝ))/(1+d)) • s := by
  classical
  funext i
  have row (j : V) :
      (transition G i j) * s j =
        (if i=j then (1-(d:ℝ)/(d+1)) * s i else 0) +
        (if j ∈ G.neighborFinset i then (1/((d:ℝ)+1)) * (-s i) else 0) := by
    by_cases ij : i=j
    · subst j
      simp [transition, regular, nsmul_eq_mul, div_eq_mul_inv]
    · by_cases edge : G.Adj i j
      · simp [transition, ij, edge, regular, opposite i j edge]
      · simp [transition, ij, edge]
  simp only [Matrix.mulVec, dotProduct, row, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, regular]
  have pos : (0:ℝ) < d+1 := by positivity
  have pos' : (0:ℝ) < 1+d := by positivity
  field_simp
  ring

/-- A two-coloring supplies a nonzero sign eigenvector on a nonempty graph. -/
theorem attainable_of_bipartite {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (regular : ∀ i, G.degree i = d)
    (bipartite : G.IsBipartite) :
    ∃ s : V → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ s ≠ 0 ∧
      (transition G).mulVec s = ((1-(d:ℝ))/(1+d)) • s := by
  classical
  obtain ⟨color⟩ := bipartite
  let s (v : V) : ℝ := if color v = 0 then 1 else -1
  have hasSign (i : V) : s i = 1 ∨ s i = -1 := by
    dsimp [s]
    split <;> simp
  refine ⟨s, hasSign, ?_, regular_bipartite G d regular s ?_⟩
  · intro h
    obtain ⟨i⟩ := ‹Nonempty V›
    have hi := congrFun h i
    rcases hasSign i with hi' | hi' <;> simp [hi'] at hi
  · intro i j adj
    have distinct := color.valid adj
    have values (i : V) : color i = 0 ∨ color i = 1 := by
      have bound := (color i).isLt
      rcases (show (color i).val = 0 ∨ (color i).val = 1 by omega) with h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases values i with a|a <;> rcases values j with b|b <;> simp_all [s]

end BipartiteMetropolis

namespace MetropolisSharp
open OMA.S_mo_239951
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On a connected graph, equality forces constant absolute value of the eigenvector,
alternating signs across all edges, and the same degree at every vertex. -/
theorem rigidity (D : ℕ) (degrees : ∀ i, G.degree i ≤ D) (connected : G.Connected)
    (v : V → ℝ) (nz : v ≠ 0) (eig : (transition G).mulVec v = ((1-(D:ℝ))/(1+D)) • v) :
    (∀ i, G.degree i = D) ∧ (∃ M : ℝ, 0 < M ∧ ∀ i, |v i| = M) ∧
      ∀ i j, G.Adj i j → v j = -v i := by
  obtain ⟨i,hi,maximal⟩ := extremal_vertex v nz
  have at_max {a : V} (h : |v a| = |v i|) :
      G.degree a = D ∧ ∀ b, G.Adj a b → v b = -v a :=
    (abs_extreme G v a (h ▸ hi) (fun j => h ▸ maximal j) (degrees a) eig).2 rfl
  have same (j : V) : |v j| = |v i| := by
    have visit := (SimpleGraph.reachable_iff_reflTransGen ..).mp (connected.preconnected i j)
    induction visit with
    | refl => rfl
    | tail _ adj ih => rw [(at_max ih).2 _ adj, abs_neg, ih]
  exact ⟨fun a => (at_max (same a)).1, ⟨|v i|,hi,same⟩, fun a => (at_max (same a)).2⟩

/-- The sharp universal lower bound is attained by a connected graph exactly
when it is regular of the specified degree and bipartite. -/
theorem eigenvalue_iff (D : ℕ) (degrees : ∀ i, G.degree i ≤ D) (connected : G.Connected) :
    (∃ v : V → ℝ, v ≠ 0 ∧ (transition G).mulVec v = ((1-(D:ℝ))/(1+D)) • v) ↔
      (∀ i, G.degree i = D) ∧ G.IsBipartite := by
  classical
  constructor
  · rintro ⟨v,nz,eig⟩
    obtain ⟨regular,⟨M,hM,mag⟩,flip⟩ := rigidity G D degrees connected v nz eig
    refine ⟨regular, ⟨SimpleGraph.Coloring.mk (fun a => if 0 < v a then (0 : Fin 2) else 1) ?_⟩⟩
    intro a b edge
    have nonzero : v a ≠ 0 := abs_pos.mp (by rw [mag]; exact hM)
    rw [flip a b edge]
    rcases lt_or_gt_of_ne nonzero with h | h <;> simp [h, not_lt.mpr h.le]
  · rintro ⟨regular,bip⟩
    have : Nonempty V := connected.nonempty
    obtain ⟨s,_,nz,eig⟩ := BipartiteMetropolis.attainable_of_bipartite G D regular bip
    exact ⟨s,nz,eig⟩

/-- The registered lower bound does hold on all graphs of maximum degree at most three. -/
theorem subcubic {l : ℝ} {v : V → ℝ} (degrees : ∀ i, G.degree i ≤ 3) (nz : v ≠ 0)
    (eig : (transition G).mulVec v = l • v) : -(1/2 : ℝ) ≤ l := by
  have bound := lower_bound G 3 degrees l v nz eig
  norm_num at bound ⊢
  exact bound

theorem degree_bound {l : ℝ} {v : V → ℝ} (nz : v ≠ 0)
    (eig : (transition G).mulVec v = l • v) :
    (1 - (G.maxDegree : ℝ))/(1 + G.maxDegree) ≤ l :=
  lower_bound G G.maxDegree G.degree_le_maxDegree l v nz eig

theorem equality_at_maximum_degree (connected : G.Connected) :
    (∃ v : V → ℝ, v ≠ 0 ∧ (transition G).mulVec v =
        ((1 - (G.maxDegree : ℝ))/(1 + G.maxDegree)) • v) ↔
      (∀ i, G.degree i = G.maxDegree) ∧ G.IsBipartite :=
  eigenvalue_iff G G.maxDegree G.degree_le_maxDegree connected

/-- A single coordinate determines the entire extremal eigenvector, including zero. -/
theorem simple_at_bound (d : ℕ) (degrees : ∀ i, G.degree i ≤ d) (connected : G.Connected)
    (x : V) : Function.Injective (fun v : {u : V → ℝ //
        (transition G).mulVec u = ((1-(d:ℝ))/(1+d)) • u} => v.1 x) := by
  rintro ⟨v,ev⟩ ⟨w,ew⟩ same
  apply Subtype.ext
  by_contra different
  have nz : v-w ≠ 0 := sub_ne_zero.mpr different
  have eig : (transition G).mulVec (v-w) = ((1-(d:ℝ))/(1+d)) • (v-w) := by
    rw [Matrix.mulVec_sub, ev, ew, smul_sub]
  obtain ⟨_,⟨M,pos,mag⟩,_⟩ := rigidity G d degrees connected _ nz eig
  have z := mag x
  change v x = w x at same
  simp [Pi.sub_apply, same] at z
  linarith

end MetropolisSharp

namespace BipartiteMetropolis
open OMA.S_mo_239951
open scoped Classical

/-- The complete balanced bipartite graph attains the lower bound at every positive degree. -/
theorem complete_family (d : ℕ) (hd : 0 < d) :
    let G := completeBipartiteGraph (Fin d) (Fin d)
    G.Connected ∧ G.IsBipartite ∧ (∀ i, G.degree i = d) ∧
      ∃ s : Fin d ⊕ Fin d → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ s ≠ 0 ∧
        (transition G).mulVec s = ((1 - (d:ℝ))/(1+d)) • s := by
  classical
  let G := completeBipartiteGraph (Fin d) (Fin d)
  let z : Fin d := ⟨0,hd⟩
  let _ : Nonempty (Fin d) := ⟨z⟩
  have cross (i j : Fin d) : G.Adj (.inl i) (.inr j) := by simp [G]
  have connected : G.Connected := by
    apply G.connected_iff_exists_forall_reachable.mpr
    refine ⟨.inl z, ?_⟩
    rintro (x|x)
    · exact (cross z z).reachable.trans (cross x z).symm.reachable
    · exact (cross z x).reachable
  have bip : G.IsBipartite := by
    simpa [G,SimpleGraph.IsBipartite] using
      (SimpleGraph.CompleteBipartiteGraph.bicoloring (Fin d) (Fin d)).colorable
  have degree (i : Fin d ⊕ Fin d) : G.degree i = d := by
    rw [← G.card_neighborFinset_eq_degree]
    rcases i with x|x
    · have h : G.neighborFinset (.inl x) =
          (Finset.univ : Finset (Fin d)).map Function.Embedding.inr := by
        ext (a|b) <;> simp [G]
      rw [h]
      simp
    · have h : G.neighborFinset (.inr x) =
          (Finset.univ : Finset (Fin d)).map Function.Embedding.inl := by
        ext (a|b) <;> simp [G]
      rw [h]
      simp
  exact ⟨connected,bip,degree,attainable_of_bipartite G d degree bip⟩

end BipartiteMetropolis
