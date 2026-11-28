import HardinProof
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

section

namespace GridAnti.Hardin

def onRim {n m : ℕ} (v : Cell n m) : Prop :=
  (v.1.val=0 ∨ v.1.val+1=n) ∨ (v.2.val=0 ∨ v.2.val+1=m)

instance {n m : ℕ} (v : Cell n m) : Decidable (onRim v) := by
  unfold onRim
  infer_instance


private def pos {n m : ℕ} (v : Cell n m) : ℕ × ℕ := (v.1.val, v.2.val)

private theorem pos_injective {n m : ℕ} : Function.Injective (@pos n m) :=
  fun _ _ h => Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

/-- A perimeter vertex has at most two neighbours along the rim and one away from it. -/
private theorem rim_candidates {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (v : Cell n m) (hv : onRim v) : ∃ a b f : ℕ × ℕ, ∀ z ∈ neighbors v,
    (onRim z → pos z = a ∨ pos z = b) ∧ (¬onRim z → pos z = f) := by
  obtain ⟨i,j⟩ := v
  let inward (k : ℕ) := if k=0 then 1 else k-1
  by_cases hi : i.val=0 ∨ i.val+1=n
  · by_cases hj : j.val=0 ∨ j.val+1=m
    · refine ⟨(inward i.val,j.val),(i.val,inward j.val),(0,0),?_⟩
      rintro ⟨k,l⟩ hk
      have ha := (Finset.mem_filter.mp hk).2
      simp only [Adj, Fin.ext_iff] at ha
      simp only [onRim, pos, Prod.mk.injEq]
      have := i.isLt; have := j.isLt; have := k.isLt; have := l.isLt
      simp only [inward]
      split_ifs <;> omega
    · refine ⟨(i.val,j.val-1),(i.val,j.val+1),(inward i.val,j.val),?_⟩
      rintro ⟨k,l⟩ hk
      have ha := (Finset.mem_filter.mp hk).2
      simp only [Adj, Fin.ext_iff] at ha
      simp only [onRim, pos, Prod.mk.injEq]
      have := i.isLt; have := j.isLt; have := k.isLt; have := l.isLt
      simp only [inward]
      split_ifs <;> omega
  · have hj : j.val=0 ∨ j.val+1=m := hv.resolve_left hi
    refine ⟨(i.val-1,j.val),(i.val+1,j.val),(i.val,inward j.val),?_⟩
    rintro ⟨k,l⟩ hk
    have ha := (Finset.mem_filter.mp hk).2
    simp only [Adj, Fin.ext_iff] at ha
    simp only [onRim, pos, Prod.mk.injEq, inward]
    have := i.isLt; have := j.isLt; have := k.isLt; have := l.isLt
    split <;> omega

theorem rim_neighbors_le_two {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) (v : Cell n m)
    (hv : onRim v) : ((neighbors v).filter onRim).card ≤ 2 := by
  obtain ⟨a,b,_,h⟩ := rim_candidates hn hm v hv
  have sub : ((neighbors v).filter onRim).image pos ⊆ {a,b} := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hw
    simpa using (h w h1).1 h2
  exact (Finset.card_image_of_injective _ pos_injective).symm.le.trans
    ((Finset.card_le_card sub).trans Finset.card_le_two)

private theorem nonrim_neighbors_le_one {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (v : Cell n m) (hv : onRim v) : ((neighbors v).filter (fun z => ¬onRim z)).card ≤ 1 := by
  obtain ⟨_,_,f,h⟩ := rim_candidates hn hm v hv
  have sub : ((neighbors v).filter (fun z => ¬onRim z)).image pos ⊆ {f} := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hw
    simpa using (h w h1).2 h2
  exact (Finset.card_image_of_injective _ pos_injective).symm.le.trans
    ((Finset.card_le_card sub).trans (by simp))

theorem rim_degree_le_three {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (v : Cell n m) (hv : onRim v) : (neighbors v).card ≤ 3 := by
  have h1 := rim_neighbors_le_two hn hm v hv
  have h2 := nonrim_neighbors_le_one hn hm v hv
  have h3 := Finset.card_filter_add_card_filter_not onRim (s:=neighbors v)
  omega

theorem rim_has_opposite {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (c : Cell n m → Bool) (happy : Happy c) (v : Cell n m) (hv : onRim v) :
    ∃ z ∈ neighbors v, onRim z ∧ c z ≠ c v := by
  by_contra! h
  have hh := happy v
  have hl := neighbor_lower (by omega : 2 ≤ n) (by omega : 2 ≤ m) v
  by_cases corner : (v.1.val=0 ∨ v.1.val+1=n) ∧ (v.2.val=0 ∨ v.2.val+1=m)
  · simp only [if_pos corner] at hl
    have empty : ((neighbors v).filter (fun z => c z ≠ c v)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
      apply hd (h z hz ?_)
      have adj := (Finset.mem_filter.mp hz).2
      unfold onRim
      simp only [Adj,Fin.ext_iff] at adj
      omega
    unfold opp at hh
    rw [empty, Finset.card_empty] at hh
    omega
  · simp only [if_neg corner] at hl
    have sub : ((neighbors v).filter fun z => c z ≠ c v) ⊆
        (neighbors v).filter (fun z => ¬onRim z) := by
      intro z hz
      obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz,fun hr => hd (h z hz hr)⟩
    have small := (Finset.card_le_card sub).trans (nonrim_neighbors_le_one hn hm v hv)
    change opp c v ≤ 1 at small
    omega

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin
open Finset

private theorem side_ends (n : ℕ) (large : 2 ≤ n) :
    (univ.filter (fun i : Fin n => i.val=0 ∨ i.val+1=n)).card = 2 := by
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have diff : first≠last := by
    intro h
    have := congrArg Fin.val h; simp only [first,last] at this; omega
  have eq : univ.filter (fun i : Fin n => i.val=0 ∨ i.val+1=n) = {first,last} := by
    ext i
    simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton,Fin.ext_iff,first,last]
    omega
  simp [eq,diff]

theorem rim_card {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m) :
    (univ.filter (@onRim n m)).card + 4 = 2*n + 2*m := by
  let outside (k : ℕ) (i : Fin k) := i.val=0 ∨ i.val+1=k
  have xends : (univ.filter (outside n)).card=2 := side_ends n (by omega)
  have yends : (univ.filter (outside m)).card=2 := side_ends m (by omega)
  have xsum := card_filter_add_card_filter_not (s:=univ) (outside n)
  have ysum := card_filter_add_card_filter_not (s:=univ) (outside m)
  have allsum := card_filter_add_card_filter_not (s:=univ) (@onRim n m)
  simp only [card_univ,Fintype.card_fin,Fintype.card_prod] at xsum ysum allsum
  have eq : univ.filter (fun v : Cell n m => ¬onRim v) =
      (univ.filter (fun i => ¬outside n i)) ×ˢ (univ.filter (fun j => ¬outside m j)) := by
    ext v
    simp [onRim,outside]
  rw [eq,card_product] at allsum
  generalize (univ.filter fun i => ¬outside n i).card = X at *
  generalize (univ.filter fun i => ¬outside m i).card = Y at *
  rw [xends] at xsum; rw [yends] at ysum
  rw [← xsum,← ysum] at allsum ⊢
  nlinarith

end GridAnti.Hardin
end

section

namespace GridAnti.Hardin.Perimeter
open Finset

private theorem corner_count_le {n m : ℕ} (T : Finset (Cell n m)) :
    (T.filter atCorner).card ≤ 4 := by
  let p : Cell n m → ℕ × ℕ := fun q => (q.1.val,q.2.val)
  have inj : Function.Injective p := fun a b h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  let C : Finset (ℕ × ℕ) := {(0,0),(0,m-1),(n-1,0),(n-1,m-1)}
  have sub : (T.filter atCorner).image p ⊆ C := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨_,h⟩ := mem_filter.mp hv
    obtain ⟨a,b⟩ := h
    simp only [C, p, mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  exact (card_image_of_injective _ inj).symm.le.trans ((card_le_card sub).trans card_le_four)

private theorem reverse_adj {n m : ℕ} (v z : Cell n m) : Adj v z ↔ Adj z v := by
  unfold Adj
  grind

private theorem flip_edges {n m : ℕ} (T F : Finset (Cell n m)) :
    (∑ v ∈ T, (F.filter (Adj v)).card) = ∑ w ∈ F, (T.filter (Adj w)).card := by
  calc
    _ = ∑ v ∈ T, ∑ w ∈ F, (if Adj v w then 1 else 0 : ℕ) := by simp
    _ = ∑ w ∈ F, ∑ v ∈ T, (if Adj v w then 1 else 0 : ℕ) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro w hw
      simp_rw [reverse_adj _ w]
      simp

/-- If every boundary one touches a boundary zero, and all boundary cells have
at most two boundary neighbors, at least a third of the boundary is zero. -/
private theorem cover_rim {n m : ℕ} (R : Cell n m → Prop) [DecidablePred R]
    (c : Cell n m → Bool) (T F : Finset (Cell n m))
    (hT : ∀ v, v ∈ T ↔ c v = true) (hF : ∀ v, v ∈ F ↔ c v ≠ true)
    (deg : ∀ v, R v → ((neighbors v).filter R).card ≤ 2)
    (cover : ∀ v, R v → ∃ z ∈ neighbors v, R z ∧ c z ≠ c v) :
    (T.filter R).card ≤ 2*(F.filter R).card := by
  classical
  let A := T.filter R
  let B := F.filter R
  have touch (v) (hv : v ∈ A) : 1 ≤ (B.filter (Adj v)).card := by
    obtain ⟨hvt,hvr⟩ := mem_filter.mp hv
    obtain ⟨z,hz,hzr,opp⟩ := cover v hvr
    refine Finset.card_pos.mpr ⟨z,mem_filter.mpr ⟨mem_filter.mpr ⟨(hF z).mpr ?_,hzr⟩,
      (mem_filter.mp hz).2⟩⟩
    rwa [(hT v).mp hvt] at opp
  have cap (v) (hv : v ∈ B) : (A.filter (Adj v)).card ≤ 2 := by
    refine (card_le_card (show A.filter (Adj v) ⊆ (neighbors v).filter R from ?_)).trans
      (deg v (mem_filter.mp hv).2)
    intro z hz
    obtain ⟨ha,adj⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,adj⟩,(mem_filter.mp ha).2⟩
  have left := sum_le_sum (s:=A) (f:=fun _ => 1) (g:=fun v => (B.filter (Adj v)).card) touch
  have right := sum_le_sum (s:=B) (f:=fun v => (A.filter (Adj v)).card) (g:=fun _ => 2) cap
  rw [flip_edges A B] at left
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at left right
  change A.card ≤ 2*B.card
  omega

/-- Count all opposite-colored edges, charging a lost incidence at each boundary zero. -/
theorem configuration_bound {n m : ℕ} (hn : 2≤n) (hm : 2≤m)
    (R : Cell n m → Prop) [DecidablePred R] (c : Cell n m → Bool) (happy : Happy c)
    (rim_count : (univ.filter R).card+4=2*n+2*m)
    (deg : ∀ v, R v → (neighbors v).card ≤ 3)
    (on_deg : ∀ v, R v → ((neighbors v).filter R).card ≤ 2)
    (cover : ∀ v, R v → ∃ z ∈ neighbors v, R z ∧ c z ≠ c v) :
    9*ones c+n+m ≤ 6*n*m+8 := by
  classical
  let T := univ.filter (fun v => c v=true)
  let F := univ.filter (fun v => c v≠true)
  have part : T.card+F.card=n*m := by
    simpa [T,F] using (card_filter_add_card_filter_not (fun v => c v=true) (s:=univ))
  have rim : (T.filter R).card+(F.filter R).card=(univ.filter R).card := by
    rw [show T.filter R=(univ.filter R).filter (fun v => c v=true) from filter_comm _ _ _,
      show F.filter R=(univ.filter R).filter (fun v => c v≠true) from filter_comm _ _ _]
    exact card_filter_add_card_filter_not _
  have coverage := cover_rim R c T F (by simp [T]) (by simp [F]) on_deg cover
  have low (v : Cell n m) : 2 ≤ opp c v + (if atCorner v then 1 else 0) := by
    have hd := neighbor_lower hn hm v
    change if atCorner v then _ else _ at hd
    have hh := happy v
    by_cases h : atCorner v <;> simp [h] at hd ⊢ <;> omega
  have penalty (v : Cell n m) : (T.filter (Adj v)).card + (if R v then 1 else 0) ≤ 4 := by
    have h := card_le_card (show T.filter (Adj v) ⊆ neighbors v from fun _ hz =>
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩)
    by_cases hv : R v
    · have := deg v hv
      simp [hv]
      omega
    · simpa [hv] using h.trans (degree_le_four v)
  have exactly : (∑ v ∈ T, opp c v) = ∑ w ∈ F, (T.filter (Adj w)).card := by
    rw [← flip_edges T F]
    apply sum_congr rfl
    intro v hv
    have hv' := (mem_filter.mp hv).2
    apply congrArg Finset.card
    ext w
    simp [neighbors,F,hv',and_comm]
  have lo := sum_le_sum (s:=T) (f:=fun _ => 2)
    (g:=fun v => opp c v + if atCorner v then 1 else 0) (fun v _ => low v)
  have hi := sum_le_sum (s:=F)
    (f:=fun w => (T.filter (Adj w)).card + if R w then 1 else 0) (g:=fun _ => 4)
    (fun w _ => penalty w)
  simp only [sum_const,nsmul_eq_mul,sum_add_distrib,sum_boole,Nat.cast_id] at hi lo
  change T.card*2 ≤ (∑ v ∈ T,opp c v)+(T.filter atCorner).card at lo
  change (∑ w ∈ F,(T.filter (Adj w)).card)+(F.filter R).card ≤ F.card*4 at hi
  have corners := corner_count_le T
  change 9*T.card+n+m ≤ 6*n*m+8
  rw [Nat.mul_assoc 6 n m]
  omega

end GridAnti.Hardin.Perimeter
end

section

namespace GridAnti.Hardin
open Finset

/-- The finite upper estimate loses at least a linear perimeter contribution. -/
theorem best_perimeter {n m : ℕ} (hn : 5≤n) (hm : 5≤m) :
    9*best n m+n+m ≤ 6*n*m+8 := by
  classical
  have hn3 : 3≤n := by omega
  have hm3 : 3≤m := by omega
  have configurations (c : Cell n m → Bool) (happy : Happy c) :
      9*ones c+n+m ≤ 6*n*m+8 :=
    Perimeter.configuration_bound (by omega) (by omega) onRim c happy (rim_card hn hm)
      (rim_degree_le_three hn3 hm3) (rim_neighbors_le_two hn3 hm3) (rim_has_opposite hn3 hm3 c happy)
  have nle : n ≤ n*m := by
    simpa using Nat.mul_le_mul_left n (show 1≤m by omega)
  have mle : m ≤ n*m := by
    simpa using Nat.mul_le_mul_right m (show 1≤n by omega)
  have le : n+m ≤ 6*n*m+8 := by rw [Nat.mul_assoc]; omega
  have bound : best n m ≤ (6*n*m+8-(n+m))/9 := by
    apply Finset.sup_le
    intro c hc
    have := configurations c (mem_filter.mp hc).2
    omega
  omega

end GridAnti.Hardin
end

section

namespace GridAnti.Hardin

/-- Explicit constants for convergence from below, conditional on the perimeter
edge count. The phase construction supplies the other side of the estimate. -/
theorem density_gap_of_perimeter {n m : ℕ} (hn : 8≤n) (hm : 8≤m)
    (upper : 9*best n m+n+m ≤ 6*n*m+8) :
    (1/(n:ℝ) + 1/(m:ℝ))/18 ≤ 2/3 - (best n m:ℝ)/((n:ℝ)*m) ∧
    2/3 - (best n m:ℝ)/((n:ℝ)*m) ≤ (2/3)*(1/(n:ℝ)+1/(m:ℝ)) := by
  have n8 : (8:ℝ) ≤ n := by exact_mod_cast hn
  have m8 : (8:ℝ) ≤ m := by exact_mod_cast hm
  have np : 0 < (n:ℝ) := by linarith
  have mp : 0 < (m:ℝ) := by linarith
  have up : 9*(best n m:ℝ)+n+m ≤ 6*(n:ℝ)*m+8 := by exact_mod_cast upper
  have lo : 2*(n:ℝ)*m+8 ≤ 3*(best n m:ℝ)+2*n+2*m := by
    exact_mod_cast sharp_phase_lower (n:=n) (m:=m) (by omega) (by omega)
  constructor <;> field_simp <;> nlinarith only [n8,m8,up,lo]

end GridAnti.Hardin
end

namespace GridAnti.Hardin

/-- The density deficit has the order of the reciprocal side lengths. -/
theorem density_gap {n m : ℕ} (hn : 8≤n) (hm : 8≤m) :
    (1/(n:ℝ) + 1/(m:ℝ))/18 ≤ 2/3 - (best n m:ℝ)/((n:ℝ)*m) ∧
    2/3 - (best n m:ℝ)/((n:ℝ)*m) ≤ (2/3)*(1/(n:ℝ)+1/(m:ℝ)) :=
  density_gap_of_perimeter hn hm (best_perimeter (by omega) (by omega))

end GridAnti.Hardin
