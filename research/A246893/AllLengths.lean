import OMAStatements.S_oeis_a246893
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Basic

/-! # Counting complementary pairs in words of arbitrary length

For a word of length k over 0,...,n, count configurations having a pair in
distinct positions with sum n. A pair may use any two of the k positions.
For k=5 this gives the original OEIS A246893 count from the registered five-position statement. The proof gives the exponential
generating function in k for the avoiding words and an exact finite formula
in Stirling numbers of the second kind. -/

/-!
# Five-letter words with a complementary pair

We prove Colin Barker's formulas for OEIS A246893 from the registered
five-position counting problem formalized by @clementtrecourt. When the
alphabet endpoint grows by two, the new smallest and largest letters are a
complementary pair. In an avoiding word, the old positions support a smaller
avoiding word, while the new positions must all carry the same letter.
Grouping these choices by their number gives a triangular recurrence at
lengths zero through five. The degree-five term cancels on removing the
avoiding words from the full alphabet power. The final coefficient calculation
sums the resulting two parity polynomials.
-/

namespace ComplementaryWords

/-- The number of words of length k on 0,...,n that have no complementary pair. -/
def bad (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin k → Fin (n+1) =>
    ∀ i j, i≠j → (x i).val + (x j).val ≠ n)).card

end ComplementaryWords

/-! Splitting off the two endpoints of a finite alphabet preserves the old complementary pairs. -/
namespace ComplementaryWords

def tag (n : ℕ) (x : Fin (n+2+1)) : Fin (n+1) ⊕ Bool :=
  if _ : x.val=0 then .inr false
  else if _ : x.val=n+2 then .inr true
  else .inl ⟨x.val-1, by omega⟩

def untag (n : ℕ) : Fin (n+1) ⊕ Bool → Fin (n+2+1)
  | .inl x => ⟨x.val+1, by omega⟩
  | .inr false => ⟨0,by omega⟩
  | .inr true => ⟨n+2,by omega⟩

/-- Interior letters are shifted down by one; false and true are the two endpoints. -/
def alphabet (n : ℕ) : Fin (n+2+1) ≃ (Fin (n+1) ⊕ Bool) where
  toFun := tag n
  invFun := untag n
  left_inv := by
    intro x
    unfold tag
    split <;> rename_i h
    · apply Fin.ext
      exact h.symm
    · split <;> rename_i h'
      · apply Fin.ext
        exact h'.symm
      · apply Fin.ext
        change x.val-1+1=x.val
        omega
  right_inv := by
    rintro (x|b)
    · obtain ⟨v,hv⟩ := x
      simp [tag,untag]
      exact dif_neg (by omega)
    · cases b <;> simp [tag,untag]

theorem sum_iff (n : ℕ) (x y : Fin (n+2+1)) :
    x.val+y.val=n+2 ↔
      match alphabet n x, alphabet n y with
      | .inl a,.inl b => a.val+b.val=n
      | .inr a,.inr b => a≠b
      | _,_ => False := by
  obtain ⟨a,rfl⟩ := (alphabet n).symm.surjective x
  obtain ⟨b,rfl⟩ := (alphabet n).symm.surjective y
  simp only [Equiv.apply_symm_apply]
  change (untag n a).val + (untag n b).val = n+2 ↔ _
  rcases a with a|(_|_) <;> rcases b with b|(_|_) <;> simp [untag] <;> omega

end ComplementaryWords

namespace ComplementaryWords

def Avoid {I A : Type} (R : A → A → Prop) (f : I → A) : Prop :=
  ∀ i j, i ≠ j → ¬ R (f i) (f j)

abbrev Words (I : Type) {A : Type} (R : A → A → Prop) := {f : I → A // Avoid R f}

def joined {A : Type} (R : A → A → Prop) : A ⊕ Bool → A ⊕ Bool → Prop
  | .inl a, .inl b => R a b
  | .inr a, .inr b => a ≠ b
  | _, _ => False

abbrev ConstWords (I : Type) := {b : I → Bool // ∀ i j, b i = b j}

section
variable {I A : Type} [Fintype I] [DecidableEq I] (R : A → A → Prop)

abbrev Pieces := Σ S : Finset I, Words S R × ConstWords {i : I // i ∉ S}

def expand (v : Pieces (I:=I) R) : Words I (joined R) := by
  rcases v with ⟨S,f,b⟩
  refine ⟨fun i => if h : i ∈ S then .inl (f.val ⟨i,h⟩) else .inr (b.val ⟨i,h⟩),?_⟩
  intro i j ne
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simpa [hi,hj,joined] using f.property ⟨i,hi⟩ ⟨j,hj⟩ (fun e => ne (congrArg Subtype.val e))
  · simp [hi,hj,joined]
  · simp [hi,hj,joined]
  · simp [hi,hj,joined,b.property ⟨i,hi⟩ ⟨j,hj⟩]

theorem expand_bijective : Function.Bijective (expand (I:=I) R) := by
  classical
  constructor
  · rintro ⟨S,f,b⟩ ⟨T,g,c⟩ eq
    have hi (i : I) := congrFun (congrArg Subtype.val eq) i
    have same : S=T := by
      ext i
      have h := hi i
      by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp [expand,hs,ht] at h ⊢
    subst T
    have fg : f=g := by
      apply Subtype.ext
      funext i
      simpa [expand,i.property] using hi i.val
    have bc : b=c := by
      apply Subtype.ext
      funext i
      simpa [expand,i.property] using hi i.val
    rw [fg,bc]
  · intro w
    let S := Finset.univ.filter (fun i => (w.val i).isLeft)
    have memS (i) : i ∈ S ↔ (w.val i).isLeft := by simp [S]
    have L (i) (hi : i ∈ S) : ∃ a, w.val i = Sum.inl a := by
      have h := (memS i).mp hi
      cases e : w.val i with
      | inl a => exact ⟨a,rfl⟩
      | inr b => simp [e] at h
    have B (i) (hi : i ∉ S) : ∃ b, w.val i = Sum.inr b := by
      rw [memS] at hi
      cases e : w.val i with
      | inl a => simp [e] at hi
      | inr b => exact ⟨b,rfl⟩
    let f (i : S) := (L i.val i.property).choose
    let b (i : {i : I // i ∉ S}) := (B i.val i.property).choose
    have lf (i : S) : w.val i = Sum.inl (f i) := (L i.val i.property).choose_spec
    have rb (i : {i : I // i ∉ S}) : w.val i = Sum.inr (b i) := (B i.val i.property).choose_spec
    have fa : Avoid R f := by
      intro i j ne
      have h := w.property i j (fun same => ne (Subtype.ext same))
      simpa only [lf i,lf j,joined] using h
    have mono (i j : {i : I // i ∉ S}) : b i = b j := by
      by_cases eq : i=j
      · rw [eq]
      · have h := w.property i j (fun same => eq (Subtype.ext same))
        simpa only [rb i,rb j,joined,not_not] using h
    refine ⟨⟨S,⟨f,fa⟩,⟨b,mono⟩⟩,?_⟩
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simpa [expand,hi] using (lf ⟨i,hi⟩).symm
    · simpa [expand,hi] using (rb ⟨i,hi⟩).symm

end
end ComplementaryWords

namespace ComplementaryWords
open scoped Classical

/-- Transport both the positions and the alphabet along bijections respecting the
forbidden relation. -/
def transport {I J A C : Type} (d : I ≃ J) (e : A ≃ C)
    (R : A → A → Prop) (T : C → C → Prop) (rel : ∀ x y, R x y ↔ T (e x) (e y)) :
    Words I R ≃ Words J T where
  toFun f := ⟨fun j => e (f.val (d.symm j)),by
    intro i j ne badPair
    exact f.property _ _ (d.symm.injective.ne ne) ((rel _ _).mpr badPair)⟩
  invFun g := ⟨fun i => e.symm (g.val (d i)),by
    intro i j ne badPair
    have h := (rel _ _).mp badPair
    exact g.property _ _ (d.injective.ne ne) (by simpa using h)⟩
  left_inv f := by ext i; simp
  right_inv g := by ext i; simp

private theorem card_const (I : Type) [Fintype I] [Fintype (ConstWords I)] :
    Fintype.card (ConstWords I) = if Nonempty I then 2 else 1 := by
  classical
  split_ifs with ne
  · let i := Classical.choice ne
    let e : ConstWords I ≃ Bool :=
      { toFun := fun f => f.val i
        invFun := fun b => ⟨fun _ => b,fun _ _ => rfl⟩
        left_inv := by intro f; apply Subtype.ext; funext j; exact f.property i j
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (by decide)
  · let e : ConstWords I ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨fun _ => false,fun _ _ => rfl⟩
        left_inv := by intro f; apply Subtype.ext; funext j; exact (ne ⟨j⟩).elim
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (by decide)

private theorem numeric_card (n k : ℕ) :
    Fintype.card (Words (Fin k) (fun a b : Fin (n+1) => a.val + b.val = n)) = bad n k := by
  classical
  rw [Fintype.card_subtype]
  unfold bad
  congr 1
  ext f
  constructor
  · intro hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hf).2⟩
  · intro hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hf).2⟩

theorem bad_pieces (n k : ℕ) :
    bad (n+2) k = ∑ S : Finset (Fin k), bad n S.card * (if S=Finset.univ then 1 else 2) := by
  classical
  let R := fun a b : Fin (n+1) => a.val+b.val=n
  have rel (x y : Fin (n+2+1)) : x.val+y.val=n+2 ↔ joined R (alphabet n x) (alphabet n y) := by
    have h := sum_iff n x y
    cases hx : alphabet n x <;> cases hy : alphabet n y <;> simpa [hx,hy,joined,R] using h
  rw [← numeric_card]
  let e := transport (Equiv.refl (Fin k)) (alphabet n) _ (joined R) rel
  let split := Equiv.ofBijective (expand (I:=Fin k) R) (expand_bijective R)
  rw [Fintype.card_congr e,← Fintype.card_congr split]
  change Fintype.card (Σ S : Finset (Fin k), Words S R × ConstWords {i : Fin k // i ∉ S}) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  rw [Fintype.card_prod,card_const {i : Fin k // i ∉ S}]
  have N : Nonempty {i : Fin k // i ∉ S} ↔ S ≠ Finset.univ := by
    simp only [nonempty_subtype]
    constructor
    · rintro ⟨i,hi⟩ rfl
      exact hi (Finset.mem_univ i)
    · contrapose!
      exact Finset.eq_univ_of_forall
  rw [N]
  have old := Fintype.card_congr (transport (Fintype.equivFinOfCardEq (Fintype.card_coe S))
    (Equiv.refl (Fin (n+1))) R R (fun _ _ => Iff.rfl))
  rw [old]
  change Fintype.card (Words (Fin S.card) (fun a b : Fin (n+1) => a.val + b.val = n)) * _ = _
  rw [numeric_card]
  by_cases h : S=Finset.univ <;> simp [h]

end ComplementaryWords

namespace PairWindows

/-- Regroup the subsets indexing the old letters by size. Keeping every
position leaves only one choice, while each proper subset leaves two. -/
theorem reindex_sum (k : ℕ) (f : ℕ → ℕ) :
    (∑ S : Finset (Fin k), f S.card * (if S = Finset.univ then 1 else 2)) =
      f k + 2 * ∑ j ∈ Finset.range k, k.choose j * f j := by
  let g (j : ℕ) := f j * (if j = k then 1 else 2)
  have total := Finset.sum_powerset_apply_card g (x := (Finset.univ : Finset (Fin k)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_range_succ] at total
  calc
    _ = ∑ S : Finset (Fin k), g S.card := by
      apply Finset.sum_congr rfl
      intro S _
      have eq : S.card = k ↔ S = Finset.univ := by simpa using S.card_eq_iff_eq_univ
      simp only [g, eq]
    _ = (∑ j ∈ Finset.range k, k.choose j * g j) + k.choose k * g k := total
    _ = (∑ j ∈ Finset.range k, 2 * (k.choose j * f j)) + f k := by
      simp only [g, if_true, mul_one, Nat.choose_self, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_range.mp hj).ne]
      ring
    _ = _ := by rw [← Finset.mul_sum, add_comm]

end PairWindows

namespace ComplementaryWords

/-- Introducing a complementary pair of new letters gives two choices on every
nonempty set of new positions and one choice when all letters are old. -/
theorem bad_add_two (n k : ℕ) :
    bad (n+2) k = bad n k + 2 * ∑ j ∈ Finset.range k, k.choose j * bad n j :=
  (bad_pieces n k).trans (PairWindows.reindex_sum k (bad n))

end ComplementaryWords

namespace ComplementaryWords

open OMA.S_oeis_a246893 Finset

/-- The only length-five window starts at zero. Ordering two distinct
positions gives exactly the pair used by the registered predicate. -/
theorem good_iff {n : ℕ} (x : Fin 5 → Fin (n+1)) :
    good x = true ↔ ¬(∀ i j, i ≠ j → (x i).val + (x j).val ≠ n) := by
  classical
  simp only [good, decide_eq_true_eq]
  constructor
  · intro w no
    obtain ⟨i,hi,j,hj,lt,sum⟩ := w 0 (by decide)
    apply no ⟨i,hi⟩ ⟨j,hj⟩ (fun eq => by have := congrArg Fin.val eq; dsimp at this; omega)
    simpa [OMA.S_oeis_a246893.get,hi,hj] using sum
  · intro pair q hq
    have : q=0 := by omega
    subst q
    push Not at pair
    obtain ⟨i,j,ne,eq⟩ := pair
    rcases lt_or_gt_of_ne ne with lt | lt
    · exact ⟨i.val,i.isLt,j.val,j.isLt,lt,by simpa [OMA.S_oeis_a246893.get] using eq⟩
    · exact ⟨j.val,j.isLt,i.val,i.isLt,lt,by simpa [OMA.S_oeis_a246893.get,add_comm] using eq⟩

theorem actual (n : ℕ) : (a n : ℚ) = ((n+1 : ℕ)^5 : ℚ) - (bad n 5 : ℚ) := by
  classical
  let words := (univ : Finset (Fin 5 → Fin (n+1)))
  let avoids (x : Fin 5 → Fin (n+1)) := ∀ i j, i ≠ j → (x i).val + (x j).val ≠ n
  have other : (words.filter fun x => ¬avoids x) = words.filter (fun x => good x = true) := by
    ext x; simp only [mem_filter,good_iff,avoids]
  have split := card_filter_add_card_filter_not (s := words) avoids
  rw [other] at split
  have all : words.card = (n+1)^5 := by simp [words]
  rw [all] at split
  change ((↑(words.filter (fun x => good x = true)).card : ℤ) : ℚ) = _ 
  change (bad n 5) + (words.filter fun x => good x = true).card = (n+1)^5 at split
  have eq := congrArg (fun k : ℕ => (k : ℚ)) split
  push_cast at eq ⊢
  linarith

theorem base0 : ∀ k ≤ 5, bad 0 k = if k ≤ 1 then 1 else 0 := by
  intro k bound
  interval_cases k <;> decide +kernel

theorem base1 : ∀ k ≤ 5, bad 1 k = if k = 0 then 1 else 2 := by
  intro k bound
  interval_cases k <;> decide +kernel

end ComplementaryWords

namespace PairWindows

/-- The first six length counts form a triangular recurrence. In each column the
polynomial depends only on the parity of the alphabet endpoint. -/
theorem count_formulas (B : ℕ → ℕ → ℕ)
    (hrec : ∀ n k, B (n + 2) k = B n k + 2 * ∑ j ∈ Finset.range k, k.choose j * B n j)
    (base0 : ∀ k ≤ 5, B 0 k = if k ≤ 1 then 1 else 0)
    (base1 : ∀ k ≤ 5, B 1 k = if k = 0 then 1 else 2) :
    (∀ n : ℕ, Even n → ((n + 1 : ℕ) ^ 5 : ℚ) - (B n 5 : ℚ) =
      1 - 5 * (n : ℚ) + 30 * (n : ℚ) ^ 2 - 5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, Odd n → ((n + 1 : ℕ) ^ 5 : ℚ) - (B n 5 : ℚ) =
      -15 + 20 * (n : ℚ) + 20 * (n : ℚ) ^ 2 - 5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) := by
  let P (x e : ℚ) : ℕ → ℚ
    | 0 => 1
    | 1 => x + 1
    | 2 => x ^ 2 + x
    | 3 => x ^ 3 + e
    | 4 => x ^ 4 - 2*x^3 + 3*x^2 - x + e*(4*x - 3)
    | _ => x ^ 5 - 5*x^4 + 15*x^3 - 20*x^2 + 10*x + e*(10*x^2 - 25*x + 16)
  have profile (n : ℕ) : ∀ k ≤ 5, (B n k : ℚ) = P n (n % 2 : ℕ) k := by
    induction n using Nat.twoStepInduction with
    | zero =>
      intro k bound
      rw [base0 k bound]
      interval_cases k <;> norm_num [P]
    | one =>
      intro k bound
      rw [base1 k bound]
      interval_cases k <;> norm_num [P]
    | more n hyp _ =>
      intro k bound
      rw [hrec]
      have parity : (n + 2) % 2 = n % 2 := by omega
      rw [parity]
      interval_cases k <;>
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_add, Nat.cast_mul,
          Nat.cast_zero, Nat.cast_ofNat] <;>
        norm_num [hyp, P, Nat.choose] <;> ring
  constructor
  · intro n even
    rw [profile n 5 (by decide), Nat.even_iff.mp even]
    simp [P]
    ring
  · intro n odd
    rw [profile n 5 (by decide), Nat.odd_iff.mp odd]
    simp [P]
    ring

end PairWindows

namespace FivePairs

open PowerSeries

/-- Clearing the denominator takes eight shifts of the two quartic formulas.
Their coefficients cancel from degree nine onward in each parity class. -/
theorem series (a : ℕ → ℤ)
    (even : ∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = 1-5*(n:ℚ)+30*(n:ℚ)^2-5*(n:ℚ)^3+10*(n:ℚ)^4)
    (odd : ∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = -15+20*(n:ℚ)+20*(n:ℚ)^2-5*(n:ℚ)^3+10*(n:ℚ)^4) :
    mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
      ((1-X)^5 * (1+X)^3 : PowerSeries ℚ) =
      X * (30+171*X+378*X^2+619*X^3+394*X^4+329*X^5-2*X^6+X^7) := by
  let b (n : ℕ) : ℚ := if n < 1 then 0 else (a n : ℚ)
  let f (x : ℚ) := 1-5*x+30*x^2-5*x^3+10*x^4
  let g (x : ℚ) := -15+20*x+20*x^2-5*x^3+10*x^4
  have value (n : ℕ) : b n = if n = 0 then 0 else if n%2=0 then f n else g n := by
    by_cases z : n=0
    · simp [b,z]
    have pos : 1 ≤ n := by omega
    by_cases e : n%2=0
    · simpa [b,z,e,not_lt.mpr pos,f] using even n pos (Nat.even_iff.mpr e)
    · simpa [b,z,e,not_lt.mpr pos,g] using odd n pos (Nat.odd_iff.mpr (by omega))
  let B := mk b
  calc
    _ = B - (2:ℕ) • (X^1*B) - (2:ℕ) • (X^2*B) + (6:ℕ) • (X^3*B) -
        (6:ℕ) • (X^5*B) + (2:ℕ) • (X^6*B) + (2:ℕ) • (X^7*B) - X^8*B := by
          dsimp [B,b]; simp only [nsmul_eq_mul]; ring
    _ = (30:ℕ) • X^1 + (171:ℕ) • X^2 + (378:ℕ) • X^3 + (619:ℕ) • X^4 +
        (394:ℕ) • X^5 + (329:ℕ) • X^6 - (2:ℕ) • X^7 + X^8 := by
      apply PowerSeries.ext
      intro n
      simp only [B, map_sub, map_add, map_nsmul, coeff_X_pow_mul', coeff_X_pow, coeff_mk, value]
      simp only [nsmul_eq_mul]
      by_cases low : n ≤ 8
      · interval_cases n <;> norm_num [f,g]
      · obtain ⟨k,rfl⟩ : ∃ k, n=k+9 := ⟨n-9,by omega⟩
        have parity : k%2 = 0 ∨ k%2 = 1 := by omega
        rcases parity with e | e <;>
          simp +arith [Nat.add_mod, e, Nat.add_sub_assoc, f, g] <;> ring
    _ = _ := by simp only [nsmul_eq_mul]; ring

end FivePairs

/-- The two parity formulas and Colin Barker's rational generating function. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a246893.main := by
  obtain ⟨e,o⟩ := PairWindows.count_formulas ComplementaryWords.bad
    ComplementaryWords.bad_add_two ComplementaryWords.base0 ComplementaryWords.base1
  have even (n : ℕ) (_ : 1 ≤ n) (h : Even n) :=
    (ComplementaryWords.actual n).trans (e n h)
  have odd (n : ℕ) (_ : 1 ≤ n) (h : Odd n) :=
    (ComplementaryWords.actual n).trans (o n h)
  exact ⟨FivePairs.series OMA.S_oeis_a246893.a even odd,even,odd⟩

/-! # Exponential generating functions for adding one complementary pair of symbols -/

namespace PairWindows

open PowerSeries

/-- Exponential generating function of a rational-valued sequence. -/
noncomputable def egf (c : ℕ → ℚ) : PowerSeries ℚ :=
  mk (fun k => c k / (k.factorial : ℚ))

/-- Multiplication by `exp ℚ` takes the binomial transform of the coefficients. -/
theorem coeff_egf_mul_exp (c : ℕ → ℚ) (k : ℕ) :
    coeff k (egf c * exp ℚ) = (∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * c j) / k.factorial := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have choose_fac : (k.choose j : ℚ) * j.factorial * (k-j).factorial = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show j ≤ k by simpa using hj)
  simp only [egf, coeff_mk, coeff_exp, Algebra.algebraMap_self_apply]
  field_simp
  linear_combination (c j) * choose_fac.symm

/-- For each new position outside the old word, one chooses one of the two new
symbols, the same choice at every such position. If no position is new, there
is only the old word. These two cases give the multiplier `2*exp ℚ-1`. -/
theorem egf_add_pair (c d : ℕ → ℚ)
    (step : ∀ k, d k = c k + 2 * ∑ j ∈ Finset.range k, (k.choose j : ℚ)*c j) :
    egf d = (2 * exp ℚ - 1) * egf c := by
  rw [show (2 * exp ℚ-1)*egf c = egf c*exp ℚ + egf c*exp ℚ - egf c by ring]
  apply PowerSeries.ext
  intro k
  rw [map_sub, map_add, coeff_egf_mul_exp, Finset.sum_range_succ]
  simp only [egf, coeff_mk, step k, Nat.choose_self, Nat.cast_one, one_mul]
  ring

/-- The same rule for ordinary natural-number counts. -/
theorem egf_add_pair_nat (c d : ℕ → ℕ)
    (step : ∀ k, d k = c k + 2 * ∑ j ∈ Finset.range k, k.choose j*c j) :
    egf (fun k => (d k:ℚ)) = (2 * exp ℚ - 1) * egf (fun k => (c k:ℚ)) := by
  apply egf_add_pair
  intro k
  exact_mod_cast step k

end PairWindows

namespace ComplementaryWords

/-- On the one-letter alphabet two distinct positions always complement each other. -/
theorem bad_zero (k : ℕ) : bad 0 k = if k ≤ 1 then 1 else 0 := by
  rcases k with _|(_|k)
  · decide
  · decide
  · rw [if_neg (by omega)]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    let i : Fin (k+2) := ⟨0,by omega⟩
    let j : Fin (k+2) := ⟨1,by omega⟩
    have ne : i ≠ j := fun e => by
      have h : (0 : ℕ) = 1 := congrArg Fin.val e
      omega
    have forbidden := (Finset.mem_filter.mp hw).2 i j ne
    have hi := (w i).isLt
    have hj := (w j).isLt
    omega

/-- On a two-letter alphabet every nonempty avoiding word is constant. -/
theorem bad_one (k : ℕ) : bad 1 k = if k = 0 then 1 else 2 := by
  cases k with
  | zero => decide
  | succ t =>
    let constant (a : Fin 2) := fun _ : Fin (t+1) => a
    have inj : Function.Injective constant := fun _ _ e => congrFun e 0
    have words : (Finset.univ.filter (fun w : Fin (t+1) → Fin 2 =>
        ∀ i j, i ≠ j → (w i).val + (w j).val ≠ 1)) =
        Finset.univ.image constant := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro good
        refine ⟨w 0,?_⟩
        funext i
        change w 0 = w i
        by_cases h : i = 0
        · rw [h]
        · have forb := good i 0 h
          apply Fin.ext
          have hi := (w i).isLt
          have hz := (w 0).isLt
          omega
      · rintro ⟨a, rfl⟩ i j _
        change a.val + a.val ≠ 1
        omega
    simp [bad,words,Finset.card_image_of_injective _ inj]

end ComplementaryWords

/-! # Exponential generating functions for words without complementary pairs

The letters range from `0` through `n` inclusive. A self-complementary
middle letter is therefore present precisely when `n` is even.
-/

namespace ComplementaryWords

open PowerSeries PairWindows

/-- With just the self-complementary letter, only lengths zero and one occur. -/
theorem egf_bad_zero : egf (fun k => (bad 0 k : ℚ)) = 1 + X := by
  apply PowerSeries.ext
  intro k
  simp only [egf, coeff_mk, bad_zero, map_add, coeff_one, coeff_X]
  rcases k with _ | _ | k <;> simp

/-- With one complementary pair, each nonempty word is constant. -/
theorem egf_bad_one : egf (fun k => (bad 1 k : ℚ)) = 2 * exp ℚ - 1 := by
  rw [two_mul]
  apply PowerSeries.ext
  intro k
  simp only [egf, coeff_mk, bad_one, map_sub, map_add, coeff_exp,
    Algebra.algebraMap_self_apply, coeff_one]
  cases k <;> simp
  ring

/-- Appending two letters to the alphabet multiplies the length EGF by `2 exp(X) - 1`. -/
theorem egf_bad_add_two (n : ℕ) :
    egf (fun k => (bad (n+2) k : ℚ)) = (2 * exp ℚ - 1) * egf (fun k => (bad n k : ℚ)) :=
  egf_add_pair_nat (bad n) (bad (n+2)) (bad_add_two n)

/-- On the alphabet `0,…,2m`, each pair contributes `2 exp(X) - 1`, and the
middle letter can occur at most once. -/
theorem egf_bad_even (m : ℕ) :
    egf (fun k => (bad (2*m) k : ℚ)) = (2 * exp ℚ - 1)^m * (1 + X) := by
  induction m with
  | zero => simpa using egf_bad_zero
  | succ m ih => rw [Nat.mul_succ, egf_bad_add_two, ih, pow_succ]; ring

/-- On the alphabet `0,…,2m+1`, every letter belongs to a complementary pair. -/
theorem egf_bad_odd (m : ℕ) :
    egf (fun k => (bad (2*m+1) k : ℚ)) = (2 * exp ℚ - 1)^(m+1) := by
  induction m with
  | zero => simpa using egf_bad_one
  | succ m ih =>
    rw [show 2*(m+1)+1=(2*m+1)+2 by omega, egf_bad_add_two, ih, pow_succ _ (m+1)]
    ring

end ComplementaryWords

namespace PairWordMoments
open PowerSeries Finset

noncomputable def moment (k : ℕ) (f : PowerSeries ℚ) : ℚ := k.factorial * coeff k f

theorem moment_succ (k : ℕ) (f : PowerSeries ℚ) :
    moment (k+1) f = moment k (derivative ℚ f) := by
  simp [moment, Nat.factorial_succ, coeff_derivative]
  ring

private noncomputable abbrev U := exp ℚ - 1

private theorem deriv_succ (r : ℕ) :
    derivative ℚ (U^(r+1)) = (r+1) • (U^r + U^(r+1)) := by
  rw [derivative_pow]
  simp only [Nat.add_sub_cancel, map_sub, derivative_exp, derivative_one, sub_zero]
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  change ((r:PowerSeries ℚ)+1) * U^r * exp ℚ = _
  dsimp only [U]
  ring

/-- The normalized coefficients of (exp(X)-1)^r count onto functions. -/
theorem stirling_moment (k r : ℕ) :
    moment k ((exp ℚ - 1)^r) = (r.factorial : ℚ) * (Nat.stirlingSecond k r : ℚ) := by
  induction k generalizing r with
  | zero =>
    cases r with
    | zero => simp [moment, Nat.stirlingSecond]
    | succ r => simp [moment, coeff_zero_eq_constantCoeff_apply, Nat.stirlingSecond]
  | succ k ih =>
    cases r with
    | zero => simp [moment, Nat.stirlingSecond]
    | succ r =>
      rw [moment_succ, deriv_succ]
      change (k.factorial:ℚ) * coeff k ((r+1) • (U^r + U^(r+1))) = _
      rw [map_nsmul, map_add, nsmul_eq_mul]
      have a := ih r
      have b := ih (r+1)
      dsimp only [moment] at a b
      rw [Nat.stirlingSecond_succ_succ,Nat.factorial_succ]
      push_cast
      change (k.factorial:ℚ)*(((r:ℚ)+1)*(coeff k (U^r)+coeff k (U^(r+1)))) = _
      dsimp only [U]
      rw [Nat.factorial_succ] at b
      push_cast at b
      linear_combination ((r:ℚ)+1) * a + ((r:ℚ)+1) * b

/-- Words on m complement pairs, written in the falling-factorial basis. -/
def pairCount (m k : ℕ) : ℕ :=
  ∑ r ∈ range (m+1), m.descFactorial r * 2^r * Nat.stirlingSecond k r

theorem paired_moment (m k : ℕ) :
    moment k ((2 * exp ℚ - 1)^m) = (pairCount m k : ℚ) := by
  have pol : (2 * exp ℚ - 1)^m =
      ∑ r ∈ range (m+1), (2^r * m.choose r) • ((exp ℚ-1)^r) := by
    rw [show 2 * exp ℚ - 1 = 2*(exp ℚ-1)+1 by ring, add_pow]
    apply sum_congr rfl
    intro r _
    simp [mul_pow, nsmul_eq_mul]
    ring
  have scalar (z : ℕ) (f : PowerSeries ℚ) : coeff k (z • f) = (z:ℚ)*coeff k f := by
    rw [map_nsmul, nsmul_eq_mul]
  rw [pol]
  simp only [moment, map_sum, scalar, Finset.mul_sum, pairCount,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply sum_congr rfl
  intro r _
  have eq := stirling_moment k r
  dsimp only [moment] at eq
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  linear_combination (2:ℚ)^r * (m.choose r:ℚ) * eq

theorem with_center (m k : ℕ) :
    moment k ((2 * exp ℚ - 1)^m * (1+X)) =
      ((pairCount m k + k * pairCount m (k-1) : ℕ) : ℚ) := by
  cases k with
  | zero => simpa [moment, mul_add] using paired_moment m 0
  | succ k =>
    rw [mul_add, mul_one]
    simp only [moment, map_add, coeff_succ_mul_X, mul_add, Nat.add_one_sub_one,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have a := paired_moment m (k+1)
    have b := paired_moment m k
    dsimp only [moment] at a b
    rw [a, Nat.factorial_succ]
    push_cast
    linear_combination ((k:ℚ)+1) * b

end PairWordMoments

namespace PairWordMoments
open PowerSeries ComplementaryWords Finset

private theorem reconstruct (k : ℕ) (a : ℕ → ℕ) :
    moment k (PairWindows.egf (fun j => (a j:ℚ))) = (a k:ℚ) := by
  simp [moment, PairWindows.egf, mul_div_cancel₀, Nat.factorial_ne_zero]

/-- Exact counts on the alphabet 0,...,2m+1 from all set partitions of the positions. -/
theorem bad_odd (m k : ℕ) : bad (2*m+1) k = pairCount (m+1) k := by
  have h := reconstruct k (bad (2*m+1))
  rw [egf_bad_odd, paired_moment] at h
  exact_mod_cast h.symm

/-- When the alphabet has a middle letter, choose its single position if it occurs. -/
theorem bad_even (m k : ℕ) :
    bad (2*m) k = pairCount m k + k * pairCount m (k-1) := by
  have h := reconstruct k (bad (2*m))
  rw [egf_bad_even, with_center] at h
  exact_mod_cast h.symm

/-- Count words containing some complementary pair of letters in distinct positions. -/
def containingPair (n k : ℕ) : ℕ :=
  (univ.filter fun x : Fin k → Fin (n+1) =>
     ∃ i j : Fin k, i≠j ∧ (x i).val+(x j).val=n).card

private theorem partition (n k : ℕ) : containingPair n k + bad n k = (n+1)^k := by
  classical
  let U := (univ : Finset (Fin k → Fin (n+1)))
  let P := fun x : Fin k → Fin (n+1) => ∃ i j : Fin k, i≠j ∧ (x i).val+(x j).val=n
  have eq : (U.filter fun x => ¬ P x) =
      (U.filter fun x => ∀ i j, i≠j → (x i).val+(x j).val≠n) := by
    ext x
    simp [P]
  have h := card_filter_add_card_filter_not (s:=U) P
  rw [eq] at h
  simpa only [containingPair,bad,U,P,card_univ,Fintype.card_fun,Fintype.card_fin] using h

/-- Length-k words on either alphabet that contain a pair summing to the bound. -/
theorem counts (m k : ℕ) :
    containingPair (2*m+1) k = (2*m+2)^k - pairCount (m+1) k ∧
    containingPair (2*m) k = (2*m+1)^k - (pairCount m k + k*pairCount m (k-1)) := by
  have odd := partition (2*m+1) k
  have even := partition (2*m) k
  rw [bad_odd] at odd
  rw [show 2*m+1+1=2*m+2 by omega] at odd
  rw [bad_even] at even
  omega

end PairWordMoments

namespace PairWordMoments
open OMA.S_oeis_a246893

/-- Specialization at length five is exactly the registered OEIS count. -/
theorem registered_five (n : ℕ) : (a n : ℚ) = (containingPair n 5 : ℚ) := by
  rw [ComplementaryWords.actual]
  have h := congrArg (fun j : ℕ => (j:ℚ)) (partition n 5)
  push_cast at h ⊢
  linarith

end PairWordMoments
