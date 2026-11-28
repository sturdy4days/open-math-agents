import OMAStatements.S_mo_88547
import Mathlib.Tactic

/-!
# Matching counts in finite bipartite graphs

We prove the finite classification formalized by @LDJAI for MathOverflow
question 88547. Hall's theorem gives a cover of the same size as a maximum
matching. Outside that cover, the graph is determined by how often each
nonempty neighborhood occurs. A multiplicity never exceeds the number of edges.
-/

namespace BipartiteCensus
open Finset

/-- Finite bipartite matching and vertex-cover duality, in terms of edge sets
and their projections. Hall's theorem is applied after adjoining dummy vertices
of cardinality equal to the maximum Hall deficiency. -/
theorem konig {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) :
    ∃ C : Finset A, ∃ D : Finset B, (∀ p ∈ E, p.1 ∈ C ∨ p.2 ∈ D) ∧
      ∃ M ⊆ E, M.card = C.card+D.card ∧
        (M.image Prod.fst).card=M.card ∧ (M.image Prod.snd).card=M.card := by
  classical
  let nbr (a : A) := (univ : Finset B).filter fun b => (a,b) ∈ E
  let N (s : Finset A) := s.biUnion nbr
  let cost (s : Finset A) := (univ \ s).card + (N s).card
  obtain ⟨X, _, best⟩ := exists_min_image (univ : Finset (Finset A)) cost univ_nonempty
  have price (s : Finset A) : cost s = Fintype.card A - s.card + (N s).card := by
    simp [cost,card_sdiff_of_subset]
  have fits : cost X ≤ Fintype.card A := by simpa [cost,N] using best ∅ (mem_univ _)
  let d := Fintype.card A - cost X
  let t (a : A) := (nbr a).disjSum (univ : Finset (Fin d))
  have hall (s : Finset A) : s.card ≤ (s.biUnion t).card := by
    obtain hs | hs := s.eq_empty_or_nonempty
    · simp [hs]
    have union : s.biUnion t = (N s).disjSum univ := by
      ext y
      cases y with
      | inl b => simp [N,t]
      | inr j => simpa [t,Finset.Nonempty] using hs
    rw [union,card_disjSum,card_univ,Fintype.card_fin]
    have opt := best s (mem_univ _)
    rw [price s] at opt
    have cap := card_le_univ s
    dsimp [d]
    omega
  obtain ⟨f,inj,allowed⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  let W := (univ : Finset A).image f
  let realEdges := E.filter fun p => f p.1 = Sum.inl p.2
  have real_subset : W.toLeft ⊆ realEdges.image Prod.snd := by
    intro b hb
    obtain ⟨a,_,e⟩ := mem_image.mp (mem_toLeft.mp hb)
    have h := allowed a
    rw [e] at h
    have edge : (a,b) ∈ E := by simpa [t,nbr] using h
    exact mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨edge,e⟩,rfl⟩
  have enough : cost X ≤ realEdges.card := by
    have plus := card_toLeft_add_card_toRight (u:=W)
    have tot : W.card = Fintype.card A := by
      rw [show W = univ.image f from rfl, card_image_of_injective _ inj, card_univ]
    have dummy : W.toRight.card ≤ d := by simpa using card_le_univ W.toRight
    have left := (card_le_card real_subset).trans card_image_le
    dsimp [d] at dummy
    omega
  obtain ⟨M, hm, sz⟩ := exists_subset_card_eq enough
  have consistent (p : A × B) (hp : p ∈ M) : f p.1 = Sum.inl p.2 := (mem_filter.mp (hm hp)).2
  refine ⟨univ \ X, N X, ?_, M, hm.trans (filter_subset _ _), sz, ?_, ?_⟩
  · rintro ⟨a,b⟩ he
    by_cases h : a ∈ X
    · exact Or.inr (mem_biUnion.mpr ⟨a,h,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨mem_univ _,h⟩)
  · apply card_image_of_injOn
    intro p hp q hq eq
    exact Prod.ext eq (Sum.inl.inj ((consistent p hp).symm.trans
      ((congrArg f eq).trans (consistent q hq))))
  · apply card_image_of_injOn
    intro p hp q hq eq
    exact Prod.ext (inj ((consistent p hp).trans ((congrArg Sum.inl eq).trans
      (consistent q hq).symm))) eq

end BipartiteCensus

namespace BipartiteCensus
open OMA.S_mo_88547 Finset
variable {A B : Type} [DecidableEq A] [DecidableEq B]

/-- A size-one matching is just an edge. -/
theorem matchingCount_one (E : Finset (A × B)) : matchingCount E 1 = E.card := by
  unfold matchingCount
  have self : ∀ M ∈ E.powersetCard 1,
      (M.image Prod.fst).card = 1 ∧ (M.image Prod.snd).card = 1 := by
    intro M hm
    obtain ⟨x,rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hm).2
    simp
  rw [filter_true_of_mem self, card_powersetCard, Nat.choose_one_right]

private lemma positive_iff (E : Finset (A × B)) (i : ℕ) :
    0 < matchingCount E i ↔ ∃ M ⊆ E, M.card = i ∧
      (M.image Prod.fst).card = M.card ∧ (M.image Prod.snd).card = M.card := by
  unfold matchingCount
  rw [card_pos]
  simp only [Finset.Nonempty,mem_filter,mem_powersetCard]
  constructor
  · rintro ⟨M,⟨sub,sz⟩,h₁,h₂⟩
    exact ⟨M,sub,sz,h₁.trans sz.symm,h₂.trans sz.symm⟩
  · rintro ⟨M,sub,sz,h₁,h₂⟩
    exact ⟨M,⟨sub,sz⟩,h₁.trans sz,h₂.trans sz⟩

private lemma covered_matching (E M : Finset (A × B)) (sub : M ⊆ E)
    (one : (M.image Prod.fst).card=M.card) (two : (M.image Prod.snd).card=M.card)
    (C : Finset A) (D : Finset B) (cover : ∀ p ∈ E, p.1 ∈ C ∨ p.2 ∈ D) :
    M.card ≤ C.card + D.card := by
  let left := M.filter fun p => p.1 ∈ C
  let right := M.filter fun p => p.1 ∉ C
  have fl : left.card ≤ C.card := card_le_card_of_injOn Prod.fst
    (fun _ h => (mem_filter.mp h).2) ((card_image_iff.mp one).mono (filter_subset _ _))
  have fr : right.card ≤ D.card := card_le_card_of_injOn Prod.snd
    (fun p h => (cover p (sub (mem_filter.mp h).1)).resolve_left (mem_filter.mp h).2)
    ((card_image_iff.mp two).mono (filter_subset _ _))
  have eq : left.card + right.card = M.card := card_filter_add_card_filter_not (s:=M) (fun p => p.1 ∈ C)
  omega

/-- The highest positive matching count and the first zero count determine the minimum cover
size. This is the property needed to enumerate the core in the census. -/
theorem cover_of_realizes [Fintype A] [Fintype B] {k : ℕ} {E : Finset (A × B)}
    (m : Fin (k+1) → ℕ) (hm : ∀ i, 0 < m i) (h : realizes E m) :
    ∃ C : Finset A, ∃ D : Finset B, (∀ p ∈ E, p.1 ∈ C ∨ p.2 ∈ D) ∧ C.card+D.card=k+1 := by
  obtain ⟨C,D,cover,M,sub,sz,one,two⟩ := konig E
  obtain ⟨L,ls,lc,l₁,l₂⟩ := (positive_iff E (k+1)).mp
    ((hm (Fin.last k)).trans_le (h.1 (Fin.last k)).ge)
  have low := covered_matching E L ls l₁ l₂ C D cover
  refine ⟨C,D,cover,le_antisymm ?_ (lc ▸ low)⟩
  by_contra! too
  have enough : k+2 ≤ M.card := by omega
  obtain ⟨T,ts,tc⟩ := exists_subset_card_eq enough
  have first : (T.image Prod.fst).card=T.card := card_image_iff.mpr ((card_image_iff.mp one).mono ts)
  have second : (T.image Prod.snd).card=T.card := card_image_iff.mpr ((card_image_iff.mp two).mono ts)
  have pos := (positive_iff E (k+2)).mpr ⟨T,ts.trans sub,tc,first,second⟩
  rw [h.2] at pos
  omega

end BipartiteCensus

namespace OMA.S_mo_88547

/-- Independent injections on the two parts preserve every matching count.
The target parts may contain arbitrary additional isolated vertices. -/
theorem matchingCount_map {A B C D : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D] (fa : A ↪ C) (fb : B ↪ D)
    (E : Finset (A × B)) (i : ℕ) :
    matchingCount (E.map (fa.prodMap fb)) i = matchingCount E i := by
  have first (M : Finset (A × B)) :
      ((M.map (fa.prodMap fb)).image Prod.fst).card = (M.image Prod.fst).card := by
    have h : (M.map (fa.prodMap fb)).image Prod.fst = (M.image Prod.fst).map fa := by
      simp only [Finset.map_eq_image, Finset.image_image]
      rfl
    rw [h, Finset.card_map]
  have second (M : Finset (A × B)) :
      ((M.map (fa.prodMap fb)).image Prod.snd).card = (M.image Prod.snd).card := by
    have h : (M.map (fa.prodMap fb)).image Prod.snd = (M.image Prod.snd).map fb := by
      simp only [Finset.map_eq_image, Finset.image_image]
      rfl
    rw [h, Finset.card_map]
  unfold matchingCount
  rw [Finset.powersetCard_map, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro M _
  change (((M.map (fa.prodMap fb)).image Prod.fst).card = i ∧
    ((M.map (fa.prodMap fb)).image Prod.snd).card = i) ↔ _
  rw [first, second]

theorem realizes_map_iff {A B C D : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D] (fa : A ↪ C) (fb : B ↪ D)
    (E : Finset (A × B)) {k : ℕ} (m : Fin k → ℕ) :
    realizes (E.map (fa.prodMap fb)) m ↔ realizes E m := by
  simp only [realizes, matchingCount_map]

/-- A graph on finite parts has a realization on the standard parts of the
same sizes, with its edge set transported by the two enumerations. -/
theorem realizes_iff_standard {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (E : Finset (A × B)) {k : ℕ} (m : Fin k → ℕ) :
    realizes E m ↔ ∃ F : Finset (Fin (Fintype.card A) × Fin (Fintype.card B)),
      F = E.map ((Fintype.equivFin A).toEmbedding.prodMap (Fintype.equivFin B).toEmbedding) ∧
      realizes F m := by
  constructor
  · intro h
    exact ⟨_, rfl, (realizes_map_iff _ _ E m).mpr h⟩
  · rintro ⟨_, rfl, h⟩
    exact (realizes_map_iff _ _ E m).mp h

theorem exists_standard {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (E : Finset (A × B)) {k : ℕ} (m : Fin k → ℕ)
    (h : realizes E m) : ∃ (a b : ℕ) (F : Finset (Fin a × Fin b)), realizes F m := by
  obtain ⟨F, _, hF⟩ := (realizes_iff_standard E m).mp h
  exact ⟨_, _, F, hF⟩

end OMA.S_mo_88547

namespace BipartiteCensus
open Finset

variable {A V : Type}

/-- Number the vertices of a finite set. -/
noncomputable def core (C : Finset A) (i : Fin C.card) : A := (C.equivFin.symm i).val

theorem core_mem (C : Finset A) (i : Fin C.card) : core C i ∈ C := (C.equivFin.symm i).property

theorem core_inj (C : Finset A) : Function.Injective (core C) := fun _ _ h =>
  C.equivFin.symm.injective (Subtype.ext h)

theorem core_surj {C : Finset A} {x : A} (hx : x ∈ C) : ∃ i, core C i=x :=
  ⟨C.equivFin ⟨x,hx⟩, congrArg Subtype.val (C.equivFin.symm_apply_apply _)⟩

variable [Fintype A] [DecidableEq A] [DecidableEq V]

/-- Outside the cover, group nonisolated vertices by the full neighborhood. -/
def twins (C : Finset A) (N : A → Finset V) (S : Finset V) : Finset A :=
  univ.filter fun x => x ∉ C ∧ N x=S ∧ S.Nonempty

@[simp] theorem twins_zero (C : Finset A) (N : A → Finset V) :
    (twins C N ∅).card = 0 := by simp [twins]

noncomputable def clone (C : Finset A) (N : A → Finset V) (S : Finset V)
    (i : Fin (twins C N S).card) : A := core (twins C N S) i

theorem clone_props (C : Finset A) (N : A → Finset V) (S : Finset V)
    (i : Fin (twins C N S).card) :
    clone C N S i ∉ C ∧ N (clone C N S i)=S ∧ S.Nonempty := by
  exact (mem_filter.mp (core_mem (twins C N S) i)).2

noncomputable def place (C : Finset A) (N : A → Finset V) :
    (Fin C.card ⊕ (Σ S : Finset V, Fin (twins C N S).card)) ↪ A where
  toFun := Sum.elim (core C) fun p => clone C N p.1 p.2
  inj' := by
    rintro (i | ⟨S,i⟩) (j | ⟨T,j⟩) h
    · exact congrArg Sum.inl (core_inj C h)
    · change core C i = clone C N T j at h
      exact False.elim ((clone_props C N T j).1 (h ▸ core_mem C i))
    · change clone C N S i = core C j at h
      exact False.elim ((clone_props C N S i).1 (h.symm ▸ core_mem C j))
    · change clone C N S i=clone C N T j at h
      have st : S=T := (clone_props C N S i).2.1.symm.trans
        ((congrArg N h).trans (clone_props C N T j).2.1)
      subst T
      obtain rfl := core_inj (twins C N S) h
      rfl

theorem place_surj (C : Finset A) (N : A → Finset V) (x : A)
    (hx : x∈C ∨ (N x).Nonempty) : ∃ i, place C N i=x := by
  by_cases h : x ∈ C
  · obtain ⟨i,hi⟩ := core_surj h
    exact ⟨.inl i,hi⟩
  · have mem : x ∈ twins C N (N x) := mem_filter.mpr ⟨mem_univ _,h,rfl,hx.resolve_left h⟩
    obtain ⟨i,hi⟩ := core_surj mem
    exact ⟨.inr ⟨N x,i⟩,hi⟩

end BipartiteCensus

namespace BipartiteCensus
open Finset OMA.S_mo_88547

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def leftNeighbors (E : Finset (A×B)) (D : Finset B) (x : A) : Finset (Fin D.card) :=
  univ.filter fun j => (x,core D j)∈E

noncomputable def rightNeighbors (E : Finset (A×B)) (C : Finset A) (y : B) : Finset (Fin C.card) :=
  univ.filter fun i => (core C i,y)∈E

noncomputable def coreEdges (E : Finset (A×B)) (C : Finset A) (D : Finset B) :
    Finset (Fin C.card × Fin D.card) := univ.filter fun p => (core C p.1,core D p.2) ∈ E

end BipartiteCensus

namespace BipartiteCensus
open Finset
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem left_bound (E : Finset (A×B)) (C : Finset A) (D : Finset B)
    (S : Finset (Fin D.card)) : (twins C (leftNeighbors E D) S).card ≤ E.card := by
  apply le_trans (b := (E.image Prod.fst).card) _ card_image_le
  apply card_le_card
  intro x hx
  obtain ⟨_, hS, ⟨j,hj⟩⟩ := (mem_filter.mp hx).2
  have he : (x,core D j) ∈ E := (mem_filter.mp (hS.symm ▸ hj : j ∈ leftNeighbors E D x)).2
  exact mem_image.mpr ⟨_,he,rfl⟩

omit [Fintype A] in
theorem right_bound (E : Finset (A×B)) (C : Finset A) (D : Finset B)
    (S : Finset (Fin C.card)) : (twins D (rightNeighbors E C) S).card ≤ E.card := by
  apply le_trans (b := (E.image Prod.snd).card) _ card_image_le
  apply card_le_card
  intro y hy
  obtain ⟨_, hS, ⟨i,hi⟩⟩ := (mem_filter.mp hy).2
  have he : (core C i,y) ∈ E := (mem_filter.mp (hS.symm ▸ hi : i ∈ rightNeighbors E C y)).2
  exact mem_image.mpr ⟨_,he,rfl⟩

end BipartiteCensus

namespace BipartiteCensus
open Finset OMA.S_mo_88547

/-- The pattern formed by a cover and the two neighborhood partitions has
exactly the original edges after restoring the original vertex labels. -/
theorem edges_eq_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (E : Finset (A × B)) (C : Finset A) (D : Finset B)
    (covers : ∀ p ∈ E, p.1 ∈ C ∨ p.2 ∈ D) :
    (coverEdges (coreEdges E C D) (fun S => (twins D (rightNeighbors E C) S).card)
      (fun S => (twins C (leftNeighbors E D) S).card)).map
      ((place C (leftNeighbors E D)).prodMap (place D (rightNeighbors E C))) = E := by
  classical
  let L := leftNeighbors E D
  let R := rightNeighbors E C
  let P := coverEdges (coreEdges E C D) (fun S => (twins D R S).card) (fun S => (twins C L S).card)
  have decode (i j) : (i,j) ∈ P ↔ (place C L i, place D R j) ∈ E := by
    rcases i with i | ⟨S,i⟩ <;> rcases j with j | ⟨T,j⟩
    · change _ ↔ (core C i,core D j) ∈ E
      simp [P,coverEdges,coreEdges]
    · change _ ↔ (core C i,clone D R T j) ∈ E
      have h := (clone_props D R T j).2.1
      simp only [P,coverEdges,mem_filter,mem_univ,true_and,decide_eq_true_eq]
      conv_lhs => rw [← h]
      simp [R,rightNeighbors]
    · change _ ↔ (clone C L S i,core D j) ∈ E
      have h := (clone_props C L S i).2.1
      simp only [P,coverEdges,mem_filter,mem_univ,true_and,decide_eq_true_eq]
      conv_lhs => rw [← h]
      simp [L,leftNeighbors]
    · change _ ↔ (clone C L S i,clone D R T j) ∈ E
      simp only [P,coverEdges,mem_filter,mem_univ,true_and,Bool.false_eq_true,false_iff]
      intro he
      exact (covers _ he).elim (clone_props C L S i).1 (clone_props D R T j).1
  change P.map ((place C L).prodMap (place D R)) = E
  ext ⟨x,y⟩
  constructor
  · rintro h
    obtain ⟨⟨i,j⟩,inside,eq⟩ := mem_map.mp h
    exact eq ▸ (decode i j).mp inside
  · intro he
    have cv := covers (x,y) he
    have lx : x∈C ∨ (L x).Nonempty := by
      rcases cv with hx | hy
      · exact Or.inl hx
      · obtain ⟨j,rfl⟩ := core_surj hy
        exact Or.inr ⟨j,mem_filter.mpr ⟨mem_univ _,he⟩⟩
    have ry : y∈D ∨ (R y).Nonempty := by
      rcases cv with hx | hy
      · obtain ⟨i,rfl⟩ := core_surj hx
        exact Or.inr ⟨i,mem_filter.mpr ⟨mem_univ _,he⟩⟩
      · exact Or.inl hy
    obtain ⟨i,hi⟩ := place_surj C L x lx
    obtain ⟨j,hj⟩ := place_surj D R y ry
    exact mem_map.mpr ⟨(i,j),(decode i j).mpr (by rwa [hi,hj]),Prod.ext hi hj⟩

end BipartiteCensus

open BipartiteCensus OMA.S_mo_88547

theorem OMA.solution : type_of% @OMA.S_mo_88547.main := by
  intro k m hm
  constructor
  · rintro ⟨a,b,E,realized⟩
    obtain ⟨C,D,cover,size⟩ := cover_of_realizes m hm realized
    have single := realized.1 (0 : Fin (k+1))
    have count : E.card=m 0 := by simpa [matchingCount_one] using single
    refine ⟨C.card,D.card,coreEdges E C D,_,_,size,twins_zero _ _,twins_zero _ _,
      (fun S => (right_bound E C D S).trans count.le),
      (fun S => (left_bound E C D S).trans count.le),?_⟩
    apply (realizes_map_iff (place C (leftNeighbors E D)) (place D (rightNeighbors E C)) _ m).mp
    rwa [edges_eq_map E C D cover]
  · rintro ⟨a,b,H,p,q,_,_,_,_,_,realized⟩
    exact exists_standard (coverEdges H p q) m realized
