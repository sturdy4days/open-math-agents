import Submission

/-!
# Interior structure of minimum fair paintings

Every optimal painting has at most four painted-to-painted neighbor incidences
in the inset-five square. When the side length is one modulo three, there
are none. At those lengths, a single diagonal congruence class determines
the painted cells throughout that square apart from its four corner cells.
The proof takes the full A344719 solution in the companion Submission module.
-/

namespace FairGrid
open Finset OMA.S_oeis_a344719 GridStrip

theorem center_uncharged {n : ℕ} (q : Cell n)
    (hx : 5≤q.1.val) (hy : 5≤q.2.val) (hrx : 5≤q.1.rev.val) (hry : 5≤q.2.rev.val)
    (d : Fin 4) : Wedge.paidWeight ((Wedge.orient d).symm q) = 0 := by
  have zero {v : Cell n} (h : 5≤v.2.val) : Wedge.paidWeight v=0 := by
    simp [Wedge.paidWeight,not_lt_of_ge h]
  fin_cases d
  · exact zero hy
  · exact zero hrx
  · exact zero hry
  · exact zero hx

theorem four_sides_omit {n : ℕ} (loss : Cell n → ℕ) (q : Cell n)
    (hx : 5≤q.1.val) (hy : 5≤q.2.val) (hrx : 5≤q.1.rev.val) (hry : 5≤q.2.rev.val) :
    (∑ d : Fin 4, Wedge.sideCost d loss) + 2*loss q ≤ 2*∑z,loss z := by
  let reduced := fun z : Cell n => if z=q then 0 else loss z
  have side (d : Fin 4) : Wedge.sideCost d reduced = Wedge.sideCost d loss := by
    apply sum_congr rfl
    intro z _
    by_cases hit : Wedge.orient d z=q
    · have pos : z=(Wedge.orient d).symm q := ((Wedge.orient d).eq_symm_apply).mpr hit
      simp [pos, center_uncharged q hx hy hrx hry]
    · simp [reduced,hit]
  have split : ∑z,loss z = loss q + ∑z,reduced z := by
    calc
      _ = ∑z, ((if z=q then loss q else 0)+reduced z) := by
        apply sum_congr rfl
        intro z _
        by_cases h : z=q <;> simp [h,reduced]
      _ = _ := by simp [sum_add_distrib]
  have h := Wedge.four_sides reduced
  simp only [side] at h
  rw [split]
  omega

theorem center_budget {n : ℕ} (hn : 7≤n) (P : Finset (Cell n)) (fair : Fair P)
    (sides : ∀ d : Fin 4, 4*n ≤ Wedge.sideCost d (localLoss P) +
        (leftTax P d + rightTax P d) + 6)
    (q : Cell n) (hx : 5≤q.1.val) (hy : 5≤q.2.val)
    (hrx : 5≤q.1.rev.val) (hry : 5≤q.2.rev.val) :
    2*(n^2+4*n) + localLoss P q ≤ 2*(3*P.card+14) := by
  have sep := four_sides_omit (localLoss P) q hx hy hrx hry
  rw [Fin.sum_univ_four] at sep
  have total := total_loss P fair
  have a := sides 0
  have b := sides 1
  have c := sides 2
  have d := sides 3
  have ha : rightTax P 0 + leftTax P 1 = 8 := rotated_tax hn P 0
  have hb : rightTax P 1 + leftTax P 2 = 8 := rotated_tax hn P 1
  have hc : rightTax P 2 + leftTax P 3 = 8 := rotated_tax hn P 2
  have hd : rightTax P 3 + leftTax P 0 = 8 := rotated_tax hn P 3
  omega

theorem clear_of_center_budget {n : ℕ} (hn : 7≤n) (hr : n%3=1) (P : Finset (Cell n))
    (size : P.card ≤ ((n+2)^2+2)/3-6)
    (budget : ∀ q : Cell n, 5≤q.1.val → 5≤q.2.val → 5≤q.1.rev.val → 5≤q.2.rev.val →
      2*(n^2+4*n)+localLoss P q ≤ 2*(3*P.card+14)) :
    ∀ q∈P, 5≤q.1.val → 5≤q.2.val → 5≤q.1.rev.val → 5≤q.2.rev.val →
      (P.filter (adjacent q ·)).card = 0 := by
  have modn : (n^2+4*n)%3=2 := by simp [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hr]
  rw [show (n+2)^2=n^2+4*n+4 by ring] at size
  intro q hq a b c d
  have val := budget q a b c d
  simp only [localLoss,if_pos hq] at val
  omega

end FairGrid

namespace FairGrid
open OMA.S_oeis_a344719 GridStrip

theorem optimal_clear {n : ℕ} (hn : 7≤n) (hr : n%3=1) (P : Finset (Cell n))
    (fair : Fair P) (size : P.card ≤ ((n+2)^2+2)/3-6) :
    ∀ q∈P, 5≤q.1.val → 5≤q.2.val → 5≤q.1.rev.val → 5≤q.2.rev.val →
      (P.filter (adjacent q ·)).card = 0 := by
  apply clear_of_center_budget hn hr P size
  apply center_budget hn P fair
  intro d
  let paint := Wedge.ink P d
  have w := word_bound hn (word (n:=n) paint) (word_zero paint) (word_end paint)
    (word_masks paint) (word_legal hn paint (Wedge.board_fair P d fair))
  rwa [total_charge hn P d] at w

end FairGrid

namespace FairGrid
open Finset OMA.S_oeis_a344719 GridStrip
/-- The inset-five square. Its cells are charged to none of the boundary strips. -/
def deepCells (n : ℕ) : Finset (Cell n) :=
  univ.filter fun q => 5≤q.1.val ∧ 5≤q.2.val ∧ 5≤q.1.rev.val ∧ 5≤q.2.rev.val

theorem four_sides_omit_core {n : ℕ} (loss : Cell n → ℕ) :
    (∑ d : Fin 4, Wedge.sideCost d loss) + 2*(∑ q ∈ deepCells n,loss q) ≤ 2*∑q,loss q := by
  let reduced := fun z : Cell n => if z∈deepCells n then 0 else loss z
  have side (d : Fin 4) : Wedge.sideCost d reduced = Wedge.sideCost d loss := by
    apply sum_congr rfl
    intro z _
    by_cases hit : Wedge.orient d z∈deepCells n
    · obtain ⟨a,b,c,e⟩ := (mem_filter.mp hit).2
      have zr := center_uncharged (Wedge.orient d z) a b c e d
      simp only [Equiv.symm_apply_apply] at zr
      rw [zr,zero_mul,zero_mul]
    · simp [reduced,hit]
  have split : ∑z,loss z = (∑z∈deepCells n, loss z) + ∑z,reduced z := by
    calc
      _ = ∑z, ((if z∈deepCells n then loss z else 0)+reduced z) := by
        apply sum_congr rfl
        intro z _
        by_cases h : z∈deepCells n <;> simp [h,reduced]
      _ = _ := by rw [sum_add_distrib,←sum_filter,filter_mem_eq_inter,univ_inter]
  have h := Wedge.four_sides reduced
  simp only [side] at h
  rw [split]
  omega

theorem core_loss_bound {n : ℕ} (hn : 7≤n) (P : Finset (Cell n)) (fair : Fair P) :
    2*(n^2+4*n) + (∑q ∈ deepCells n, localLoss P q) ≤ 2*(3*P.card+14) := by
  have each (d : Fin 4) : 4*n ≤ Wedge.sideCost d (localLoss P) +
      (leftTax P d + rightTax P d) + 6 := by
    let paint := Wedge.ink P d
    have h := word_bound hn (word (n:=n) paint) (word_zero paint) (word_end paint)
      (word_masks paint) (word_legal hn paint (Wedge.board_fair P d fair))
    rwa [total_charge hn P d] at h
  have side := four_sides_omit_core (localLoss P)
  rw [Fin.sum_univ_four] at side
  have total := total_loss P fair
  have a := each 0
  have b := each 1
  have c := each 2
  have d := each 3
  have ha : rightTax P 0 + leftTax P 1 = 8 := rotated_tax hn P 0
  have hb : rightTax P 1 + leftTax P 2 = 8 := rotated_tax hn P 1
  have hc : rightTax P 2 + leftTax P 3 = 8 := rotated_tax hn P 2
  have hd : rightTax P 3 + leftTax P 0 = 8 := rotated_tax hn P 3
  omega

/-- An optimal board has at most four painted-to-painted neighbor incidences
in its inset-five square. The count is zero in the divisible residue class. -/
theorem optimal_defects {n : ℕ} (hn : 7≤n) (P : Finset (Cell n)) (fair : Fair P)
    (size : P.card ≤ ((n+2)^2+2)/3-6) :
    (∑q ∈ deepCells n, localLoss P q) ≤ if n%3=1 then 0 else 4 := by
  have budget := core_loss_bound hn P fair
  rw [show (n+2)^2=n^2+4*n+4 by ring] at size
  split_ifs with h
  · have modn : (n^2+4*n)%3=2 := by simp [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,h]
    omega
  · omega

end FairGrid

namespace FairGrid.Rigidity

/-- The local fair equation in a region with no adjacent painted cells.
Coordinates are natural numbers; its center is `(x+1,y+1)`. -/
def eqAt (p : ℕ → ℕ → ℕ) (x y : ℕ) : Prop :=
  2 * p (x+1) (y+1) + p x (y+1) + p (x+2) (y+1) + p (x+1) y + p (x+1) (y+2) = 2

/-- The five local equations on a plus sign force one painted cell in each
central three-cell segment. Opposite painted neighbors leave a perpendicular
white neighbor with at most one painted neighbor. -/
theorem cross_window {p : ℕ → ℕ → ℕ} (bit : ∀ x y, p x y ≤ 1) (x y : ℕ)
    (w : eqAt p x (y+1)) (e : eqAt p (x+2) (y+1))
    (s : eqAt p (x+1) y) (n : eqAt p (x+1) (y+2)) (c : eqAt p (x+1) (y+1)) :
    p (x+1) (y+2) + p (x+2) (y+2) + p (x+3) (y+2) = 1 ∧
    p (x+2) (y+1) + p (x+2) (y+2) + p (x+2) (y+3) = 1 := by
  unfold eqAt at *
  have hw := bit (x+1) (y+2)
  have he := bit (x+3) (y+2)
  have hs := bit (x+2) (y+1)
  have hn := bit (x+2) (y+3)
  have hn₂ := bit (x+2) (y+4)
  have he₂ := bit (x+4) (y+2)
  have hc := bit (x+2) (y+2)
  simp only [Nat.add_assoc] at *
  norm_num at *
  by_cases paint : p (x+2) (y+2) = 1
  · omega
  · have lr : p (x+1) (y+2) + p (x+3) (y+2) ≤ 1 := by
      by_contra! h
      have l : p (x+1) (y+2) = 1 := by omega
      have r : p (x+3) (y+2) = 1 := by omega
      omega
    have ud : p (x+2) (y+1) + p (x+2) (y+3) ≤ 1 := by
      by_contra! h
      have d : p (x+2) (y+1) = 1 := by omega
      have u : p (x+2) (y+3) = 1 := by omega
      omega
    omega

/-- A finite binary word whose three-cell windows contain exactly one paint
has period 3, including both endpoints. -/
theorem periodic {f : ℕ → ℕ} {w : ℕ}
    (one : ∀ i, i+2<w → f i + f (i+1) + f (i+2) = 1) :
    ∀ i<w, f i = f (i%3) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases small : i<3
    · rw [Nat.mod_eq_of_lt small]
    · have u := one (i-3) (by omega)
      have v := one (i-2) (by omega)
      have prev := ih (i-3) (by omega) (by omega)
      have a : i-3+1 = i-2 := by omega
      have b : i-3+2 = i-2+1 := by omega
      have c : i-2+2 = i := by omega
      have modEq : (i-3)%3 = i%3 := by omega
      rw [a,b] at u
      rw [c] at v
      rw [← modEq, ←prev]
      omega

/-- Every three-by-three pattern with one paint in each row and column is a
diagonal class modulo 3. -/
theorem residue_square : ∀ z : Fin 3 → Fin 3 → Bool,
    (∀ i, (z i 0).toNat + (z i 1).toNat + (z i 2).toNat = 1) →
    (∀ j, (z 0 j).toNat + (z 1 j).toNat + (z 2 j).toNat = 1) →
    ∃ slope phase : Fin 3, slope ≠ 0 ∧ ∀ i j,
      (z i j = true ↔ (i.val + slope.val * j.val)%3 = phase.val) := by decide +kernel

end FairGrid.Rigidity


namespace FairGrid.Rigidity

/-- Every residue mod 3 has a representative in the three inner columns. -/
private def rep (x : ℕ) : ℕ := if x%3=0 then 3 else x%3

private theorem rep_bounds (x : ℕ) : 0 < rep x ∧ rep x ≤ 3 ∧ rep x % 3 = x % 3 := by
  unfold rep
  split <;> omega

private theorem rep_mod (x : ℕ) : rep (x%3) = rep x := by simp [rep]

/-- If every inner row and every inner column contains exactly one paint in
each three-cell window, one diagonal class describes the full square except
possibly its four corners. Representatives 1, 2, 3 are inner for width ≥ 5. -/
theorem windows_to_stripe {p : ℕ → ℕ → ℕ} (bit : ∀ x y, p x y ≤ 1) {w : ℕ} (wide : 5 ≤ w)
    (hor : ∀ y, 0<y → y+1<w → ∀ x, x+2<w → p x y + p (x+1) y + p (x+2) y = 1)
    (ver : ∀ x, 0<x → x+1<w → ∀ y, y+2<w → p x y + p x (y+1) + p x (y+2) = 1) :
    ∃ slope phase : Fin 3, slope ≠ 0 ∧ ∀ x y, x<w → y<w →
      ((0<x ∧ x+1<w) ∨ (0<y ∧ y+1<w)) →
      (p x y = 1 ↔ (x + slope.val * y)%3 = phase.val) := by
  let z (i j : Fin 3) := decide (p (rep i.val) (rep j.val) = 1)
  have valZ (i j : Fin 3) : (z i j).toNat = p (rep i.val) (rep j.val) := by
    have h := bit (rep i.val) (rep j.val)
    by_cases paint : p (rep i.val) (rep j.val) = 1
    · simp [z,paint]
    · have hh : p (rep i.val) (rep j.val) = 0 := by omega
      simp [z,hh]
  obtain ⟨s,t,hs,ht⟩ := residue_square z (fun i => by
    simp only [valZ]
    have b := rep_bounds i.val
    have H := ver (rep i.val) (by omega) (by omega) 1 (by omega)
    change p (rep i.val) 3 + p (rep i.val) 1 + p (rep i.val) 2 = 1
    norm_num at H
    omega) (fun j => by
    simp only [valZ]
    have b := rep_bounds j.val
    have H := hor (rep j.val) (by omega) (by omega) 1 (by omega)
    change p 3 (rep j.val) + p 1 (rep j.val) + p 2 (rep j.val) = 1
    norm_num at H
    omega)
  refine ⟨s,t,hs,?_⟩
  intro x y hx hy inner
  have repx := rep_bounds x
  have repy := rep_bounds y
  have hr (u v : ℕ) (hu : u<w) (hv : 0<v ∧ v+1<w) : p u v = p (rep u) v := by
    have b := rep_bounds u
    have a := periodic (f:=fun t => p t v) (hor v hv.1 hv.2) u hu
    have c := periodic (f:=fun t => p t v) (hor v hv.1 hv.2) (rep u) (by omega)
    simpa [b.2.2] using a.trans (show p (u%3) v = p (rep u) v by simpa only [b.2.2] using c.symm)
  have vr (u v : ℕ) (hu : 0<u ∧ u+1<w) (hv : v<w) : p u v = p u (rep v) := by
    have b := rep_bounds v
    have a := periodic (f:=p u) (ver u hu.1 hu.2) v hv
    have c := periodic (f:=p u) (ver u hu.1 hu.2) (rep v) (by omega)
    exact a.trans (by simpa only [b.2.2] using c.symm)
  have same : p x y = p (rep x) (rep y) := by
    rcases inner with h|h
    · exact (vr _ _ h hy).trans (hr _ _ hx ⟨repy.1,by omega⟩)
    · exact (hr _ _ hx h).trans (vr _ _ ⟨repx.1,by omega⟩ hy)
  have spec := ht ⟨x%3,by omega⟩ ⟨y%3,by omega⟩
  change (z ⟨x%3,_⟩ ⟨y%3,_⟩ = true ↔ (x%3 + s.val*(y%3))%3 = t.val) at spec
  simp only [z, rep_mod, decide_eq_true_eq] at spec
  have congruence : (x%3 + s.val*(y%3))%3 = (x+s.val*y)%3 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [same,←congruence]
  exact spec

/-- `eqAt p i j` refers to the center `(i+1,j+1)`. Restricting it to the
square of centers `1..w` forces one stripe until the four outer corners. -/
theorem box_stripe {p : ℕ → ℕ → ℕ} (bit : ∀ x y, p x y ≤ 1) {w : ℕ} (wide : 5 ≤ w)
    (localEq : ∀ i j, i<w → j<w → eqAt p i j) :
    ∃ slope phase : Fin 3, slope ≠ 0 ∧ ∀ x y, x<w → y<w →
      ((0<x ∧ x+1<w) ∨ (0<y ∧ y+1<w)) →
      (p (x+1) (y+1) = 1 ↔ (x+slope.val*y)%3 = phase.val) := by
  apply windows_to_stripe (p:=fun i j => p (i+1) (j+1)) (fun _ _ => bit _ _) wide
  · intro y y0 yw x xw
    have E := (cross_window bit x (y-1) (localEq _ _ (by omega) (by omega))
        (localEq _ _ (by omega) (by omega)) (localEq _ _ (by omega) (by omega))
        (localEq _ _ (by omega) (by omega)) (localEq _ _ (by omega) (by omega))).1
    simpa only [show y-1+2 = y+1 by omega] using E
  · intro x x0 xw y yw
    have E := (cross_window bit (x-1) y (localEq _ _ (by omega) (by omega))
        (localEq _ _ (by omega) (by omega)) (localEq _ _ (by omega) (by omega))
        (localEq _ _ (by omega) (by omega)) (localEq _ _ (by omega) (by omega))).2
    simpa only [show x-1+2 = x+1 by omega] using E

end FairGrid.Rigidity


namespace FairGrid.Rigidity
open OMA.S_oeis_a344719 PaintingRows

/-- Exact fairness supplies the five-cell equation at a white vertex; zero
painted–painted incidence supplies the same equation at a painted vertex. -/
theorem painted_eqAt {n : ℕ} (P : Finset (Cell n)) (fair : Fair P) (i j : Fin n)
    (clear : (i,j) ∈ P → (P.filter (fun u => adjacent u (i,j))).card = 0) :
    eqAt (fun x y => (lit P x y).toNat) i.val j.val := by
  have s := neighbor_sum P i j
  simp only [eqAt]
  rw [lit_at P i j]
  by_cases h : (i,j)∈P
  · have z := clear h
    simp only [h,decide_true,Bool.toNat_true] at *
    omega
  · have z := fair (i,j) h
    simp [h] at *
    omega

/-- A fair painting with no painted–painted incidence in an interior square
has one common diagonal class there, up to the four corners. The zero-based
coordinates `x,y` in the conclusion are relative to the start of the square. -/
theorem painted_core {n : ℕ} (P : Finset (Cell n)) (fair : Fair P)
    (base width : ℕ) (fit : base+width≤n) (wide : 5≤width)
    (clear : ∀ v ∈ P, base≤v.1.val → v.1.val<base+width →
       base≤v.2.val → v.2.val<base+width → (P.filter (fun u => adjacent u v)).card = 0) :
    ∃ slope phase : Fin 3, slope ≠ 0 ∧ ∀ (x y : ℕ) (hx : x<width) (hy : y<width),
      ((0<x ∧ x+1<width) ∨ (0<y ∧ y+1<width)) →
      ((⟨base+x,by omega⟩,⟨base+y,by omega⟩) ∈ P ↔ (x+slope.val*y)%3=phase.val) := by
  let q (i j : ℕ) := (lit P (base+i) (base+j)).toNat
  have bits (i j : ℕ) : q i j ≤ 1 := by
    dsimp [q]; cases lit P (base+i) (base+j) <;> decide
  have localEq (i j : ℕ) (hi : i<width) (hj : j<width) : eqAt q i j := by
    let v : Fin n := ⟨base+i,by omega⟩
    let w : Fin n := ⟨base+j,by omega⟩
    have E := painted_eqAt P fair v w (fun hv => clear _ hv (by dsimp [v]; omega)
      (by dsimp [v]; omega) (by dsimp [w]; omega) (by dsimp [w]; omega))
    simpa only [eqAt,q,v,w,Nat.add_assoc] using E
  obtain ⟨s,t,hs,ht⟩ := box_stripe bits wide localEq
  refine ⟨s,t,hs,?_⟩
  intro x y hx hy inner
  let v : Fin n := ⟨base+x,by omega⟩
  let w : Fin n := ⟨base+y,by omega⟩
  have L := lit_at P v w
  have E := ht x y hx hy inner
  change (q (x+1) (y+1) = 1 ↔ _) at E
  dsimp only [q] at E
  change lit P (base+x+1) (base+y+1) = decide ((v,w) ∈ P) at L
  rw [←Nat.add_assoc,←Nat.add_assoc,L] at E
  simpa only [Bool.toNat_eq_one,decide_eq_true_eq] using E

/-- In particular, on an n by n square the zero-loss core starting at inset 5
forces a common absolute phase right up to its fifth-offset sides. -/
theorem painted_core_five {n : ℕ} (hn : 15≤n) (P : Finset (Cell n)) (fair : Fair P)
    (clear : ∀ v ∈ P, 5≤v.1.val → v.1.val+5<n → 5≤v.2.val → v.2.val+5<n →
      (P.filter (fun u => adjacent u v)).card = 0) :
    ∃ slope phase : Fin 3, slope ≠ 0 ∧ ∀ v : Cell n,
      5≤v.1.val → v.1.val+5<n → 5≤v.2.val → v.2.val+5<n →
      ((6≤v.1.val ∧ v.1.val+6<n) ∨ (6≤v.2.val ∧ v.2.val+6<n)) →
      (v ∈ P ↔ (v.1.val+slope.val*v.2.val)%3=phase.val) := by
  obtain ⟨s,t,hs,ht⟩ := painted_core P fair 5 (n-10) (by omega) (by omega)
    (fun v hv h1 h2 h3 h4 => clear v hv h1 (by omega) h3 (by omega))
  refine ⟨s,⟨(t.val+5+5*s.val)%3,by omega⟩,hs,?_⟩
  rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩ a b c d away
  change 5≤x at a; change x+5<n at b; change 5≤y at c; change y+5<n at d
  change (6≤x ∧ x+6<n) ∨ (6≤y ∧ y+6<n) at away
  have E := ht (x-5) (y-5) (by omega) (by omega) (by omega)
  have e1 : 5+(x-5)=x := by omega
  have e2 : 5+(y-5)=y := by omega
  simp only [e1,e2] at E
  refine E.trans ?_
  change ((x-5)+s.val*(y-5))%3=t.val ↔ (x+s.val*y)%3=(t.val+5+5*s.val)%3
  have bt := t.isLt
  fin_cases s <;> simp at * <;> omega

end FairGrid.Rigidity


namespace FairGrid.Rigidity
open OMA.S_oeis_a344719

/-- A single absolute phase and diagonal orientation describe the entire
inset-five square away from its four corners. -/
def diagonalOnCore {n : ℕ} (P : Finset (Cell n)) (sp : Fin 3 × Fin 3) : Prop :=
  sp.1 ≠ 0 ∧ ∀ q : Cell n,
    5 ≤ q.1.val → q.1.val + 5 < n → 5 ≤ q.2.val → q.2.val + 5 < n →
    ((6 ≤ q.1.val ∧ q.1.val + 6 < n) ∨ (6 ≤ q.2.val ∧ q.2.val + 6 < n)) →
    (q ∈ P ↔ (q.1.val + sp.1.val * q.2.val) % 3 = sp.2.val)

/-- Reading a three-by-three interior square identifies both parameters. -/
theorem diagonalOnCore_unique {n : ℕ} (hn : 15 ≤ n) (P : Finset (Cell n))
    {a b : Fin 3 × Fin 3} (ha : diagonalOnCore P a) (hb : diagonalOnCore P b) : a=b := by
  have separate : ∀ x y : Fin 3 × Fin 3,
      (∀ i j : Fin 3,
        ((6+i.val) + x.1.val*(6+j.val))%3=x.2.val ↔
        ((6+i.val) + y.1.val*(6+j.val))%3=y.2.val) → x=y := by decide +kernel
  apply separate
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  let v : Cell n := (⟨6+i.val,by omega⟩,⟨6+j.val,by omega⟩)
  have valid : ∀ sp, diagonalOnCore P sp →
      (v ∈ P ↔ ((6+i.val) + sp.1.val*(6+j.val))%3=sp.2.val) := by
    intro sp hp
    apply hp.2 v <;> dsimp [v] <;> omega
  exact (valid a ha).symm.trans (valid b hb)

/-- On a fair board, zero painted neighbor count inside the core forces a
unique diagonal orientation and phase. -/
theorem unique_diagonal_of_clear {n : ℕ} (hn : 15 ≤ n) (P : Finset (Cell n)) (fair : Fair P)
    (clear : ∀ q ∈ P, 5 ≤ q.1.val → 5 ≤ q.2.val → 5 ≤ q.1.rev.val → 5 ≤ q.2.rev.val →
      (P.filter (adjacent q ·)).card = 0) :
    ∃! sp : Fin 3 × Fin 3, diagonalOnCore P sp := by
  obtain ⟨s,t,hs,ht⟩ := painted_core_five hn P fair (by
    intro q hq h₁ h₂ h₃ h₄
    have vanish := clear q hq h₁ h₃
      (by simp only [Fin.rev]; omega) (by simp only [Fin.rev]; omega)
    have flip (v : Cell n) : adjacent v q = adjacent q v := adjacent_symm _ _
    simpa only [flip] using vanish)
  have hit : diagonalOnCore P (s,t) := ⟨hs,ht⟩
  exact ⟨(s,t),hit,fun _ other => diagonalOnCore_unique hn P other hit⟩

end FairGrid.Rigidity

namespace FairGrid.Rigidity
open OMA.S_oeis_a344719

/-- In orders congruent to one modulo three, every minimum fair painting
has a unique diagonal orientation and phase throughout its inset-five
square, apart from the four corner cells of that square. -/
theorem unique_diagonal_of_minimum {n : ℕ} (large : 15 ≤ n) (congruence : n%3=1)
    (P : Finset (Cell n)) (fair : Fair P) (minimum : P.card = a n) :
    ∃! sp : Fin 3 × Fin 3, diagonalOnCore P sp := by
  have hn : 7 ≤ n := by omega
  have size := minimum.le.trans (A344719Stripes.minimum_le n hn)
  exact unique_diagonal_of_clear large P fair (optimal_clear hn congruence P fair size)

end FairGrid.Rigidity

theorem FairGrid.Rigidity.optimal_defect_count {n : ℕ} (hn : 7≤n)
    (P : Finset (OMA.S_oeis_a344719.Cell n)) (fair : OMA.S_oeis_a344719.Fair P)
    (minimum : P.card = OMA.S_oeis_a344719.a n) :
    (∑q ∈ FairGrid.deepCells n, FairGrid.localLoss P q) ≤ if n%3=1 then 0 else 4 :=
  FairGrid.optimal_defects hn P fair (minimum.le.trans (A344719Stripes.minimum_le n hn))

/-- Directed incidences count one endpoint for each interior painted cell, so
a painted edge entirely within the inset contributes twice. -/
theorem FairGrid.Rigidity.optimal_painted_incidences {n : ℕ} (hn : 7≤n)
    (P : Finset (OMA.S_oeis_a344719.Cell n)) (fair : OMA.S_oeis_a344719.Fair P)
    (minimum : P.card = OMA.S_oeis_a344719.a n) :
    (∑q ∈ (FairGrid.deepCells n).filter (· ∈ P),
        (P.filter (OMA.S_oeis_a344719.adjacent q ·)).card) ≤
      if n%3=1 then 0 else 4 := by
  refine le_trans ?_ (optimal_defect_count hn P fair minimum)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro q _
  by_cases h : q∈P <;> simp [FairGrid.localLoss,h]

#print axioms FairGrid.Rigidity.optimal_painted_incidences
#print axioms FairGrid.Rigidity.optimal_defect_count
#print axioms FairGrid.Rigidity.unique_diagonal_of_minimum
