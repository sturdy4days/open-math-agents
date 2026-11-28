import OMAStatements.S_oeis_a344719

/-!
## Striped paintings attaining the proposed formula

Source: OEIS A344719, due to Dmitry Kamenetsky. Shinji Oda (2026-10-04)
described obtaining the upper bound by duplicating a three-row and three-column band on sides
21, 22, and 23. Here the independently generated finite boards for sides
7 through 15 are checked directly. The last three already have a band
whose duplication preserves all four neighbor indicators. Counting its three
rows and columns gives the exact change in the number of painted cells.
-/
namespace FairGrid
open Finset OMA.S_oeis_a344719

private def pos {n : ℕ} (q : Cell n) : ℤ × ℤ :=
  (q.1.val,q.2.val)

private theorem pos_injective (n : ℕ) : Function.Injective (@pos n) := by
  intro x y h
  exact Prod.ext (Fin.ext (Int.ofNat.inj (congrArg Prod.fst h)))
    (Fin.ext (Int.ofNat.inj (congrArg Prod.snd h)))

/-- Coordinates outside the square do not contribute any painted neighbor. -/
theorem neighbor_signed {n : ℕ} (P : Finset (Cell n)) (q : Cell n) :
    (P.filter (fun v => adjacent v q)).card =
      let r : ℤ := q.1.val
      let c : ℤ := q.2.val
      let has (a b : ℤ) : Prop := ∃ v ∈ P, (v.1.val : ℤ) = a ∧ (v.2.val : ℤ) = b
      (if has r (c-1) then 1 else 0) + (if has r (c+1) then 1 else 0) +
      (if has (r-1) c then 1 else 0) + (if has (r+1) c then 1 else 0) := by
  classical
  let r : ℤ := q.1.val
  let c : ℤ := q.2.val
  let D : Finset (ℤ × ℤ) := {(r,c-1),(r,c+1),(r-1,c),(r+1,c)}
  let has (a : ℤ × ℤ) : Prop := ∃ v ∈ P, (v.1.val : ℤ) = a.1 ∧ (v.2.val : ℤ) = a.2
  have step (v : Cell n) : adjacent v q = true ↔ pos v ∈ D := by
    simp only [adjacent, decide_eq_true_eq, D, mem_insert, mem_singleton, pos, Prod.mk.injEq, r, c, Fin.ext_iff]
    omega
  have he : (P.filter (fun v => adjacent v q)).image pos = D.filter has := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
      obtain ⟨hv,adj⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨(step v).mp adj,v,hv,rfl,rfl⟩
    · intro hz
      obtain ⟨hz,v,hv,h1,h2⟩ := mem_filter.mp hz
      have hzv : pos v = z := Prod.ext h1 h2
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,(step v).mpr (hzv ▸ hz)⟩,hzv⟩
  rw [← Finset.card_image_of_injective _ (pos_injective n), he]
  conv_lhs => rw [← Nat.cast_id (D.filter has).card, ← Finset.sum_boole (R := ℕ)]
  have n1 : (r,c-1) ∉ ({(r,c+1),(r-1,c),(r+1,c)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  have n2 : (r,c+1) ∉ ({(r-1,c),(r+1,c)} : Finset (ℤ × ℤ)) := by simp [Prod.mk.injEq]
  have n3 : (r-1,c) ∉ ({(r+1,c)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  simp only [D, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, sum_singleton]
  ac_rfl

/-- Evaluate all four neighbor indicators for a finite-board Boolean painting. -/
theorem neighbor_model {n : ℕ} (paint : ℕ → ℕ → Bool) (q : Cell n) :
    ((univ.filter (fun v : Cell n => paint v.1.val v.2.val)).filter (fun v => adjacent v q)).card =
      let r := q.1.val
      let c := q.2.val
      (if 0 < c ∧ paint r (c-1) then 1 else 0) +
      (if c+1 < n ∧ paint r (c+1) then 1 else 0) +
      (if 0 < r ∧ paint (r-1) c then 1 else 0) +
      (if r+1 < n ∧ paint (r+1) c then 1 else 0) := by
  classical
  rw [neighbor_signed]
  dsimp only
  have general (a b : ℤ) : (∃ v ∈ (univ.filter (fun v : Cell n => paint v.1.val v.2.val)),
      (v.1.val : ℤ) = a ∧ (v.2.val : ℤ) = b) ↔
      0 ≤ a ∧ a < (n : ℤ) ∧ 0 ≤ b ∧ b < (n : ℤ) ∧ paint a.toNat b.toNat := by
    constructor
    · rintro ⟨v,hv,rfl,rfl⟩
      have := v.1.isLt
      have := v.2.isLt
      simp only [mem_filter,mem_univ,true_and] at hv
      exact ⟨by omega,by omega,by omega,by omega,by simpa using hv⟩
    · rintro ⟨ha,ha',hb,hb',h⟩
      let v : Cell n := (⟨a.toNat,by omega⟩,⟨b.toNat,by omega⟩)
      exact ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩,by simpa [v] using Int.toNat_of_nonneg ha,by simpa [v] using Int.toNat_of_nonneg hb⟩
  have hr := q.1.isLt
  have hc := q.2.isLt
  let r := q.1.val
  let c := q.2.val
  have tm1 (z : ℕ) : (↑z-1 : ℤ).toNat = z-1 := by omega
  have tp1 (z : ℕ) : (↑z+1 : ℤ).toNat = z+1 := by omega
  have left : (0 ≤ (q.1.val : ℤ) ∧ ↑q.1.val < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ)-1 ∧ (q.2.val : ℤ)-1 < (n : ℤ) ∧ paint q.1.val (q.2.val-1)) ↔
      (0 < q.2.val ∧ paint q.1.val (q.2.val-1)) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have right : (0 ≤ (q.1.val : ℤ) ∧ ↑q.1.val < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ)+1 ∧ (q.2.val : ℤ)+1 < (n : ℤ) ∧ paint q.1.val (q.2.val+1)) ↔
      (q.2.val+1 < n ∧ paint q.1.val (q.2.val+1)) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have up : (0 ≤ (q.1.val : ℤ)-1 ∧ (q.1.val : ℤ)-1 < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ) ∧ (q.2.val : ℤ) < (n : ℤ) ∧ paint (q.1.val-1) q.2.val) ↔
      (0 < q.1.val ∧ paint (q.1.val-1) q.2.val) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have down : (0 ≤ (q.1.val : ℤ)+1 ∧ (q.1.val : ℤ)+1 < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ) ∧ (q.2.val : ℤ) < (n : ℤ) ∧ paint (q.1.val+1) q.2.val) ↔
      (q.1.val+1 < n ∧ paint (q.1.val+1) q.2.val) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  simp only [general,Int.toNat_natCast,tm1,tp1,left,right,up,down]

end FairGrid

namespace A344719Stripes

/-- Lattice coordinates start at 1. The zero row and zero column are padding. -/
def foldAxis (b i : ℕ) : ℕ := if i < b+3 then i else i-3

def pump (b : ℕ) (g : ℕ → ℕ → Bool) (x y : ℕ) := g (foldAxis b x) (foldAxis b y)

def Seam {α : Type*} (b : ℕ) (f : ℕ → α) := f (b-1) = f (b+2) ∧ f b = f (b+3)

def Seams (b : ℕ) (g : ℕ → ℕ → Bool) :=
  (∀ y, Seam b (fun x => g x y)) ∧ (∀ x, Seam b (g x))

def Good (n : ℕ) (g : ℕ → ℕ → Bool) : Prop :=
  (∀ x y, (x=0 ∨ y=0 ∨ n < x ∨ n < y) → g x y = false) ∧
  (∀ x y, 0 < x → x ≤ n → 0 < y → y ≤ n → g x y = false →
    (g x (y-1)).toNat + (g x (y+1)).toNat +
    (g (x-1) y).toNat + (g (x+1) y).toNat = 2) ∧
  ∀ x y, 3 ≤ x → x+2 ≤ n → 3 ≤ y → y+2 ≤ n → g x y = decide (x%3 = y%3)

theorem foldAxis_left {α : Type*} (b i : ℕ) (hb : 0 < b)
    (f : ℕ → α) (seam : Seam b f) :
    f (foldAxis b (i-1)) = f (foldAxis b i - 1) := by
  by_cases hi : i = b+3
  · subst i
    convert seam.1.symm using 1 <;> dsimp [foldAxis] <;> congr 1 <;> split_ifs <;> omega
  · congr 1
    unfold foldAxis
    split_ifs <;> omega

theorem foldAxis_right {α : Type*} (b i : ℕ) (f : ℕ → α) (seam : Seam b f) :
    f (foldAxis b (i+1)) = f (foldAxis b i + 1) := by
  by_cases hi : i = b+2
  · subst i
    convert seam.2 using 1 <;> dsimp [foldAxis] <;> congr 1 <;> split_ifs <;> omega
  · congr 1
    unfold foldAxis
    split_ifs <;> omega

theorem pump_seams (b : ℕ) (hb : 0 < b) (g : ℕ → ℕ → Bool) (hs : Seams b g) :
    Seams b (pump b g) := by
  have a : foldAxis b (b - 1) = b-1 := if_pos (by omega)
  have e : foldAxis b b = b := if_pos (by omega)
  have c : foldAxis b (b + 2) = b+2 := if_pos (by omega)
  have d : foldAxis b (b + 3) = b := by unfold foldAxis; split_ifs <;> omega
  constructor
  · intro y
    simpa [Seam, pump, a,e,c,d] using (hs.1 (foldAxis b y)).1
  · intro x
    simpa [Seam, pump, a,e,c,d] using (hs.2 (foldAxis b x)).1

theorem pump_good (n b : ℕ) (hb : 3 ≤ b) (bound : b+4 ≤ n)
    (g : ℕ → ℕ → Bool) (h : Good n g) (hs : Seams b g) :
    Good (n+3) (pump b g) := by
  have boundary (i : ℕ) : i=0 ∨ n+3 < i → foldAxis b i=0 ∨ n < foldAxis b i := by
    unfold foldAxis
    split_ifs <;> omega
  have inside (i : ℕ) (a : 0 < i) (c : i ≤ n+3) : 0 < foldAxis b i ∧ foldAxis b i ≤ n := by
    unfold foldAxis
    split_ifs <;> omega
  have interior (i : ℕ) (a : 3 ≤ i) (c : i+2 ≤ n+3) : 3 ≤ foldAxis b i ∧ foldAxis b i+2 ≤ n := by
    unfold foldAxis
    split_ifs <;> omega
  have residue (i : ℕ) : foldAxis b i%3 = i%3 := by
    unfold foldAxis
    split_ifs <;> omega
  refine ⟨?_,?_,?_⟩
  · intro x y conditions
    apply h.1
    rcases conditions with hx|hy|hx|hy
    · exact (boundary x (.inl hx)).elim Or.inl (fun v => .inr (.inr (.inl v)))
    · exact (boundary y (.inl hy)).elim (fun v => .inr (.inl v)) (fun v => .inr (.inr (.inr v)))
    · exact (boundary x (.inr hx)).elim Or.inl (fun v => .inr (.inr (.inl v)))
    · exact (boundary y (.inr hy)).elim (fun v => .inr (.inl v)) (fun v => .inr (.inr (.inr v)))
  · intro x y x0 xn y0 yn off
    obtain ⟨X0,Xn⟩ := inside x x0 xn
    obtain ⟨Y0,Yn⟩ := inside y y0 yn
    have a := foldAxis_left b y (by omega) _ (hs.2 (foldAxis b x))
    have c := foldAxis_right b y _ (hs.2 (foldAxis b x))
    have d := foldAxis_left b x (by omega) _ (hs.1 (foldAxis b y))
    have e := foldAxis_right b x _ (hs.1 (foldAxis b y))
    dsimp only [pump]
    rw [a,c,d,e]
    exact h.2.1 _ _ X0 Xn Y0 Yn off
  · intro x y x0 xn y0 yn
    obtain ⟨X0,Xn⟩ := interior x x0 xn
    obtain ⟨Y0,Yn⟩ := interior y y0 yn
    simpa only [pump,residue] using h.2.2 _ _ X0 Xn Y0 Yn

end A344719Stripes

/-! Counting painted cells when a three-row and a three-column band are duplicated. -/

namespace A344719Stripes

open Finset

def line (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f (i+1)

def band (b : ℕ) (f : ℕ → ℕ) : ℕ := f b + f (b+1) + f (b+2)

def total (n : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  line n fun x => line n fun y => (g x y).toNat

def bands (n b : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  (band b fun x => line n fun y => (g x y).toNat) +
  (line n fun x => band b fun y => (g x y).toNat)

def core (b : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  band b fun x => band b fun y => (g x y).toNat

theorem line_succ (n) (f : ℕ → ℕ) : line (n+1) f = line n f + f (n+1) := by
  simp [line, sum_range_succ]

private theorem line_add (n) (f g : ℕ → ℕ) :
    (line n fun i => f i + g i) = line n f + line n g := by simp [line, sum_add_distrib]

private theorem band_add (b) (f g : ℕ → ℕ) :
    (band b fun i => f i + g i) = band b f + band b g := by simp only [band]; omega

private theorem band_fold (b) (f : ℕ → ℕ) : (band b fun i => f (foldAxis b i)) = band b f := by
  simp (disch := omega) only [band, foldAxis, if_pos]

theorem line_fold (n b : ℕ) (hn : b+2 ≤ n) (f : ℕ → ℕ) :
    (line (n+3) fun i => f (foldAxis b i)) = line n f + band b f := by
  induction n, hn using Nat.le_induction with
  | base =>
    have base : (line (b+2) fun i => f (foldAxis b i)) = line (b+2) f := by
      unfold line
      apply Finset.sum_congr rfl
      intro i hi
      have lim := Finset.mem_range.mp hi
      simp only [foldAxis, if_pos (by omega : i+1 < b+3)]
    rw [line_succ, line_succ, line_succ, base]
    simp (disch := omega) only [band, foldAxis, if_neg]
    simp only [show b+2+1-3=b by omega, show b+2+2-3=b+1 by omega,
      show b+2+3-3=b+2 by omega]
    omega
  | succ n hn ih =>
    rw [show n+1+3=(n+3)+1 by omega, line_succ, ih, line_succ n f]
    simp only [foldAxis, if_neg (by omega : ¬n+3+1 < b+3), show n+3+1-3=n+1 by omega]
    omega

theorem pump_total (n b : ℕ) (g : ℕ → ℕ → Bool) (_hb : 0 < b) (hn : b+2 ≤ n) :
    total (n+3) (pump b g) = total n g + bands n b g + core b g := by
  let row x := line n (fun y => (g x y).toNat)
  let strip x := band b (fun y => (g x y).toNat)
  have inner (x : ℕ) : (line (n+3) fun y => (pump b g x y).toNat) =
      row (foldAxis b x) + strip (foldAxis b x) :=
    line_fold n b hn (fun y => (g (foldAxis b x) y).toNat)
  change (line (n+3) fun x => line (n+3) fun y => (pump b g x y).toNat) = _
  simp_rw [inner]
  rw [line_fold n b hn (fun x => row x + strip x), line_add, band_add]
  change _ = line n row + (band b row + line n strip) + band b strip
  omega

theorem pump_bands (n b : ℕ) (g : ℕ → ℕ → Bool) (_hb : 0 < b) (hn : b+2 ≤ n) :
    bands (n+3) b (pump b g) = bands n b g + 2*core b g := by
  let row x := line n (fun y => (g x y).toNat)
  let strip x := band b (fun y => (g x y).toNat)
  have inner (x : ℕ) : (line (n+3) fun y => (pump b g x y).toNat) =
      row (foldAxis b x) + strip (foldAxis b x) :=
    line_fold n b hn (fun y => (g (foldAxis b x) y).toNat)
  have retained (x : ℕ) : (band b fun y => (pump b g x y).toNat) = strip (foldAxis b x) :=
    band_fold b (fun y => (g (foldAxis b x) y).toNat)
  change (band b fun x => line (n+3) fun y => (pump b g x y).toNat) +
      (line (n+3) fun x => band b fun y => (pump b g x y).toNat) = _
  simp_rw [inner, retained]
  rw [band_fold b (fun x => row x + strip x), band_add, line_fold n b hn strip]
  change _ = (band b row + line n strip) + 2*band b strip
  omega

theorem pump_core (b : ℕ) (g : ℕ → ℕ → Bool) : core b (pump b g) = core b g := by
  let strip x := band b (fun y => (g x y).toNat)
  have retained (x : ℕ) : (band b fun y => (pump b g x y).toNat) = strip (foldAxis b x) :=
    band_fold b (fun y => (g (foldAxis b x) y).toNat)
  change (band b fun x => band b fun y => (pump b g x y).toNat) = _
  simp_rw [retained]
  exact band_fold b strip

end A344719Stripes

namespace A344719Stripes

def board (n : ℕ) (rows : List ℕ) (x y : ℕ) : Bool :=
  decide (0 < x ∧ x ≤ n ∧ 0 < y ∧ y ≤ n) && ((rows[x-1]?).getD 0).testBit (y-1)

def SeedTest (n : ℕ) (g : ℕ → ℕ → Bool) (r c : Fin n) : Prop :=
  let x := r.val+1
  let y := c.val+1
  (g x y = false →
    (g x (y-1)).toNat + (g x (y+1)).toNat +
    (g (x-1) y).toNat + (g (x+1) y).toNat = 2) ∧
  (3 ≤ x → x+2 ≤ n → 3 ≤ y → y+2 ≤ n → g x y = decide (x%3=y%3))

instance (n : ℕ) (g : ℕ → ℕ → Bool) (r c : Fin n) : Decidable (SeedTest n g r c) := by
  unfold SeedTest; infer_instance

theorem board_good (n : ℕ) (rows : List ℕ)
    (h : ∀ r c : Fin n, SeedTest n (board n rows) r c) : Good n (board n rows) := by
  refine ⟨?_,?_,?_⟩
  · intro x y H
    have hh : ¬ (0 < x ∧ x ≤ n ∧ 0 < y ∧ y ≤ n) := by omega
    simp [board,hh]
  · intro x y x0 xn y0 yn H
    obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
    exact (h ⟨x, by omega⟩ ⟨y, by omega⟩).1 H
  · intro x y x0 xn y0 yn
    obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
    exact (h ⟨x, by omega⟩ ⟨y, by omega⟩).2 x0 xn y0 yn

theorem board_seams (n b : ℕ) (rows : List ℕ)
    (h : ∀ i : Fin (n+1),
      (board n rows (b-1) i = board n rows (b+2) i ∧ board n rows b i = board n rows (b+3) i) ∧
      (board n rows i (b-1) = board n rows i (b+2) ∧ board n rows i b = board n rows i (b+3))) :
    Seams b (board n rows) := by
  constructor
  · intro y
    by_cases hy : y ≤ n
    · exact (h ⟨y, by omega⟩).1
    · simp [Seam,board,hy]
  · intro x
    by_cases hx : x ≤ n
    · exact (h ⟨x, by omega⟩).2
    · simp [Seam,board,hx]

def rows7 : List ℕ := [74, 51, 36, 73, 18, 102, 41]
theorem good7 : Good 7 (board 7 rows7) := board_good _ _ (by decide +kernel)

def rows8 : List ℕ := [85, 148, 39, 200, 19, 228, 41, 170]
theorem good8 : Good 8 (board 8 rows8) := board_good _ _ (by decide +kernel)

def rows9 : List ℕ := [202, 307, 292, 201, 146, 294, 73, 409, 166]
theorem good9 : Good 9 (board 9 rows9) := board_good _ _ (by decide +kernel)

def rows10 : List ℕ := [597, 404, 295, 584, 147, 804, 73, 914, 166, 681]
theorem good10 : Good 10 (board 10 rows10) := board_good _ _ (by decide +kernel)

def rows11 : List ℕ := [725, 1172, 295, 1608, 1171, 292, 1609, 147, 1828, 329, 1370]
theorem good11 : Good 11 (board 11 rows11) := board_good _ _ (by decide +kernel)

def rows12 : List ℕ := [1621, 2452, 2343, 1608, 1171, 2340, 585, 3218, 294, 3657, 665, 2726]
theorem good12 : Good 12 (board 12 rows12) := board_good _ _ (by decide +kernel)

def rows13 : List ℕ := [4821, 3220, 2343, 4680, 1171, 6436, 4681, 1171, 6436, 585, 7314, 1318, 5481]
theorem good13 : Good 13 (board 13 rows13) := board_good _ _ (by decide +kernel)
theorem seams13 : Seams 6 (board 13 rows13) := board_seams _ _ _ (by decide +kernel)

def rows14 : List ℕ := [5845, 9364, 2343, 12872, 9363, 2340, 12873, 9363, 2340, 12873, 1171, 14628, 2633, 10970]
theorem good14 : Good 14 (board 14 rows14) := board_good _ _ (by decide +kernel)
theorem seams14 : Seams 6 (board 14 rows14) := board_seams _ _ _ (by decide +kernel)

def rows15 : List ℕ := [13013, 19604, 18727, 12872, 9363, 18724, 4681, 25747, 18724, 4681, 25746, 2342, 29257, 5273, 21926]
theorem good15 : Good 15 (board 15 rows15) := board_good _ _ (by decide +kernel)
theorem seams15 : Seams 7 (board 15 rows15) := board_seams _ _ _ (by decide +kernel)

end A344719Stripes

namespace A344719Stripes
open OMA.S_oeis_a344719 Finset

def selected (n : ℕ) (g : ℕ → ℕ → Bool) : Finset (Cell n) :=
  univ.filter (fun q => g (q.1.val+1) (q.2.val+1))

theorem selected_card (n : ℕ) (g : ℕ → ℕ → Bool) :
    (selected n g).card = ∑ x ∈ range n, ∑ y ∈ range n, (g (x+1) (y+1)).toNat := by
  classical
  have key (a : Bool) : (if a then 1 else 0) = a.toNat := by cases a <;> rfl
  unfold selected
  rw [← Nat.cast_id (univ.filter _).card, ← Finset.sum_boole (R := ℕ), Fintype.sum_prod_type]
  simp only [key, ← Fin.sum_univ_eq_sum_range]

theorem lower_indicator (f : ℕ → Bool) (h : f 0 = false) (i : ℕ) :
    (if 0 < i ∧ f (i-1+1) then 1 else 0) = (f i).toNat := by
  cases i with
  | zero => simp [h]
  | succ i =>
    cases h' : f (i+1) <;> simp [h']

theorem upper_indicator (n : ℕ) (f : ℕ → Bool) (h : ∀ x, n < x → f x = false) (i : ℕ) :
    (if i+1 < n ∧ f (i+1+1) then 1 else 0) = (f (i+1+1)).toNat := by
  by_cases h' : i+1 < n
  · cases f (i+1+1) <;> simp [h']
  · simp [h',h (i+1+1) (by omega)]

theorem selected_fair {n : ℕ} {g : ℕ → ℕ → Bool} (h : Good n g) : Fair (selected n g) := by
  intro q unpainted
  obtain ⟨r,c⟩ := q
  have off : g (r.val+1) (c.val+1) = false := by simpa [selected] using unpainted
  have loc := h.2.1 (r.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega) off
  unfold selected
  rw [FairGrid.neighbor_model (fun i j => g (i+1) (j+1))]
  dsimp only
  rw [lower_indicator (fun j => g (r.val+1) j) (h.1 _ _ (.inr (.inl rfl))) c.val,
    upper_indicator n (fun j => g (r.val+1) j) (fun j hj => h.1 _ _ (.inr (.inr (.inr hj)))) c.val,
    lower_indicator (fun i => g i (c.val+1)) (h.1 _ _ (.inl rfl)) r.val,
    upper_indicator n (fun i => g i (c.val+1)) (fun i hi => h.1 _ _ (.inr (.inr (.inl hi)))) r.val]
  simpa using loc

theorem selected_striped {n : ℕ} {g : ℕ → ℕ → Bool} (h : Good n g) :
    Striped (selected n g) := by
  intro r r0 rn
  refine ⟨⟨r.val%3, Nat.mod_lt _ (by decide)⟩,?_⟩
  intro c c0 cn
  simp only [selected, mem_filter,mem_univ,true_and,h.2.2 (r.val+1) (c.val+1) (by omega)
    (by omega) (by omega) (by omega), decide_eq_true_eq]
  omega

end A344719Stripes

namespace A344719Stripes
open OMA.S_oeis_a344719

def target (n : ℕ) := ((n+2)^2+2)/3-6

theorem target_step (n : ℕ) (hn : 7 ≤ n) : target (n+3) = target n + 2*n+7 := by
  have h : 9*9 ≤ (n+2)^2 := by
    simpa only [sq] using Nat.mul_le_mul (show 9 ≤ n+2 by omega) (show 9 ≤ n+2 by omega)
  have e : (n+3+2)^2 = (n+2)^2 + 3*(2*n+7) := by ring
  simp only [target,e]
  omega

def Ready (n : ℕ) : Prop := ∃ (b : ℕ) (g : ℕ → ℕ → Bool),
  3 ≤ b ∧ b+4 ≤ n ∧ Good n g ∧ Seams b g ∧
  total n g = target n ∧ bands n b g = 2*n+4 ∧ core b g = 3

theorem ready_step {n : ℕ} (h : Ready n) : Ready (n+3) := by
  obtain ⟨b,g,hb,hn,hg,hs,ht,hd,hc⟩ := h
  refine ⟨b,pump b g,hb,by omega,pump_good n b hb hn g hg hs,pump_seams b (by omega) g hs,?_,?_,?_⟩
  · rw [pump_total, ht,hd,hc,target_step n (by omega)] <;> omega
  · rw [pump_bands,hd,hc] <;> omega
  · rw [pump_core,hc]

theorem ready_range (n : ℕ) (hn : 13 ≤ n) : Ready n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hi : n ≤ 15
    · interval_cases n
      · exact ⟨6,board 13 rows13,by decide,by decide,good13,seams13,by decide +kernel,by decide +kernel,by decide +kernel⟩
      · exact ⟨6,board 14 rows14,by decide,by decide,good14,seams14,by decide +kernel,by decide +kernel,by decide +kernel⟩
      · exact ⟨7,board 15 rows15,by decide,by decide,good15,seams15,by decide +kernel,by decide +kernel,by decide +kernel⟩
    · have eq : n-3+3=n := by omega
      rw [← eq]
      exact ready_step (ih (n-3) (by omega) (by omega))

/-- The three checked stripe templates and six small boards attain Oda's upper bound. -/
theorem upper (n : ℕ) (hn : 7 ≤ n) :
    ∃ p : Finset (Cell n), Fair p ∧ Striped p ∧ p.card = ((n+2)^2+2)/3-6 := by
  suffices h : ∃ g, Good n g ∧ total n g = target n by
    obtain ⟨g,hg,ht⟩ := h
    exact ⟨selected n g, selected_fair hg, selected_striped hg, (selected_card n g).trans ht⟩
  by_cases h : 13 ≤ n
  · obtain ⟨_,g,_,_,hg,_,ht,_,_⟩ := ready_range n h
    exact ⟨g,hg,ht⟩
  · have hi : n ≤ 12 := by omega
    interval_cases n
    · exact ⟨_,good7,by decide +kernel⟩
    · exact ⟨_,good8,by decide +kernel⟩
    · exact ⟨_,good9,by decide +kernel⟩
    · exact ⟨_,good10,by decide +kernel⟩
    · exact ⟨_,good11,by decide +kernel⟩
    · exact ⟨_,good12,by decide +kernel⟩

theorem minimum_le (n : ℕ) (hn : 7 ≤ n) : a n ≤ ((n+2)^2+2)/3-6 := by
  obtain ⟨p,hp,_,size⟩ := upper n hn
  exact Nat.sInf_le ⟨p,hp,size.symm⟩

end A344719Stripes

#print axioms A344719Stripes.upper
#print axioms A344719Stripes.minimum_le
