/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation

@[expose] public section

/-! # Hennessy-Milner Logic (HML)

Hennessy-Milner Logic (HML) is a logic for reasoning about the behaviour of nondeterministic and
concurrent systems.

## References

* [M. Hennessy, R. Milner, *Algebraic Laws for Nondeterminism and Concurrency*][Hennessy1985]
* [L. Aceto, A. Ingólfsdóttir, *Testing Hennessy-Milner Logic with Recursion*][Aceto1999]

-/

namespace Cslib.Logic.HML

/-- Propositions. -/
inductive Proposition (Label : Type u) : Type u where
  | true
  | false
  | neg (a : Proposition Label)
  | and (a : Proposition Label) (b : Proposition Label)
  | or (a : Proposition Label) (b : Proposition Label)
  | diamond (μ : Label) (a : Proposition Label)
  | box (μ : Label) (a : Proposition Label)

/-- Finite conjunction of propositions. -/
def Proposition.finiteAnd : List (Proposition Label) → Proposition Label
  | [] => .true
  | [a] => a
  | a :: as => .and a (finiteAnd as)

/-- Finite disjunction of propositions. -/
def Proposition.finiteOr : List (Proposition Label) → Proposition Label
  | [] => .false
  | [a] => a
  | a :: as => .or a (finiteOr as)

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (a : Proposition Label) (lts : LTS State Label)
  : Set State :=
  match a with
  | .true => Set.univ
  | .false => ∅
  | .neg a => (a.denotation lts)ᶜ
  | .and a b => a.denotation lts ∩ b.denotation lts
  | .or a b => a.denotation lts ∪ b.denotation lts
  | .diamond μ a => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ a.denotation lts}
  | .box μ a => {s | ∀ s', lts.Tr s μ s' → s' ∈ a.denotation lts}

/-- Satisfaction relation defined via denotation. -/
@[scoped grind =]
def Satisfies (lts : LTS State Label) (s : State) (a : Proposition Label) : Prop :=
  s ∈ a.denotation lts

/-- The theory of a state is the set of all propositions that it satifies. -/
abbrev theory (s : State) (lts : LTS State Label) : Set (Proposition Label) :=
  {a | Satisfies lts s a}

abbrev TheoryEq (lts : LTS State Label) (s1 s2 : State) :=
  theory s1 lts = theory s2 lts

open Proposition LTS Bisimulation Simulation

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind _=_]
theorem satisfies_mem_denotation {lts : LTS State Label} :
    Satisfies lts s a ↔ s ∈ a.denotation lts := Iff.rfl

/-- Satisfies true is always true. -/
theorem Satisfies.true {lts : LTS State Label} {s : State}
  : Satisfies lts s .true := by
  simp [Satisfies]

/-- Satisfies neg iff not satisfies. -/
theorem Satisfies.neg_iff {lts : LTS State Label} {s : State}
  {a : Proposition Label}
  : Satisfies lts s (.neg a) ↔ ¬Satisfies lts s a := by
  simp [Satisfies]

/-- Satisfies and iff satisfies both. -/
theorem Satisfies.and_iff {lts : LTS State Label} {s : State}
  {a b : Proposition Label}
  : Satisfies lts s (.and a b) ↔ Satisfies lts s a ∧ Satisfies lts s b := by
  simp [Satisfies]

/-- Satisfies or iff satisfies one. -/
theorem Satisfies.or_iff {lts : LTS State Label} {s : State}
  {a b : Proposition Label} :
    Satisfies lts s (.or a b) ↔ Satisfies lts s a ∨ Satisfies lts s b := by
  simp [Satisfies]

/-- Satisfies diamond iff exists successor satisfying. -/
theorem Satisfies.diamond_iff {lts : LTS State Label} {s : State} {μ : Label}
  {a : Proposition Label} :
    Satisfies lts s (.diamond μ a) ↔ ∃ s', lts.Tr s μ s' ∧ Satisfies lts s' a := by
  simp [Satisfies]

/-- Satisfies box iff all successors satisfy. -/
theorem Satisfies.box_iff {lts : LTS State Label} {s : State} {μ : Label}
  {a : Proposition Label} :
    Satisfies lts s (.box μ a) ↔ ∀ s', lts.Tr s μ s' → Satisfies lts s' a := by
  simp [Satisfies]

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
theorem satisfies_finiteAnd {lts : LTS State Label} {s : State}
  {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteAnd as) ↔ ∀ a ∈ as, Satisfies lts s a := by
  induction as with
  | nil => simp [Proposition.finiteAnd, Satisfies, Proposition.denotation]
  | cons a as ih =>
    cases as with
    | nil => simp [Proposition.finiteAnd]
    | cons b bs =>
      simp only [Proposition.finiteAnd, List.mem_cons, Satisfies, Proposition.denotation,
                 Set.mem_inter_iff]
      constructor
      · intro ⟨ha, hrest⟩ x hx
        cases hx with
        | inl heq => exact heq ▸ ha
        | inr hmem => exact ih.mp hrest x (List.mem_cons.mpr hmem)
      · intro h
        constructor
        · exact h a (Or.inl rfl)
        · apply ih.mpr
          intro x hx
          exact h x (Or.inr (List.mem_cons.mp hx))

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
theorem satisfies_finiteOr {lts : LTS State Label} {s : State}
  {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteOr as) ↔ ∃ a ∈ as, Satisfies lts s a := by
  induction as with
  | nil =>
    simp only [Proposition.finiteOr, List.not_mem_nil, false_and, exists_false,
               Satisfies, Proposition.denotation, Set.mem_empty_iff_false]
  | cons a as ih =>
    cases as with
    | nil => simp [Proposition.finiteOr]
    | cons b bs =>
      simp only [Proposition.finiteOr, Satisfies, Proposition.denotation, Set.mem_union]
      constructor
      · intro h
        cases h with
        | inl ha => exact ⟨a, List.mem_cons.mpr (Or.inl rfl), ha⟩
        | inr hrest =>
          obtain ⟨x, hx_mem, hx_sat⟩ := ih.mp hrest
          exact ⟨x, List.mem_cons.mpr (Or.inr hx_mem), hx_sat⟩
      · intro ⟨x, hx_mem, hx_sat⟩
        rcases List.mem_cons.mp hx_mem with rfl | hmem
        · left; exact hx_sat
        · right; exact ih.mpr ⟨x, hmem, hx_sat⟩

-- TODO Make this grind-friendly
theorem theoryEq_denotation_eq {lts : LTS State Label} :
    TheoryEq lts s1 s2 ↔
    (∀ a : Proposition Label, s1 ∈ a.denotation lts ↔ s2 ∈ a.denotation lts) := by
  apply Iff.intro <;> intro h
  · intro a
    apply Iff.intro <;> intro hmem
    · have : a ∈ theory s1 lts := by grind
      grind
    · have : a ∈ theory s1 lts := by grind
      grind
  · grind

/-- Helper: transfer satisfaction via theory equality. -/
theorem theoryEq_satisfies {lts : LTS State Label} (h : TheoryEq lts s1 s2)
    (hs : Satisfies lts s1 a) : Satisfies lts s2 a := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h a).mp hs

/-- With negation in HML: For any two non-theory-equivalent states, we can always find a formula
    that one satisfies and the other doesn't, by using negation if needed. -/
private lemma exists_distinguishing_formula_satisfies
    {lts : LTS State Label} {s1 s2 : State} (h : ¬TheoryEq lts s1 s2)
    : ∃ a, Satisfies lts s1 a ∧ ¬Satisfies lts s2 a := by
  have h₁ : ∃ a, (Satisfies lts s1 a ∧ ¬Satisfies lts s2 a)
            ∨ (¬Satisfies lts s1 a ∧ Satisfies lts s2 a) := by grind
  obtain ⟨a, ha⟩ := h₁
  cases ha with
  | inl hcase => exact ⟨a, hcase⟩
  | inr hcase =>
    -- s1' ⊭ a ∧ s2' ⊨ a, use negation
    obtain ⟨h1, h2⟩ := hcase
    exists .neg a
    simp only [Satisfies, Proposition.denotation, Set.mem_compl_iff]
    constructor <;> grind

@[scoped grind ⇒]
lemma theoryEq_isBisimulation (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    lts.IsBisimulation (TheoryEq lts) := by
  intro s1 s2 h μ
  constructor
  case left =>
    intro s1' htr
    by_contra hnex
    simp only [not_exists, not_and] at hnex
    -- hnex : ∀ s2', lts.Tr s2 μ s2' → ¬TheoryEq lts s1' s2'
    have hfin : Finite (lts.image s2 μ) := image_finite s2 μ
    -- For each s2' reachable from s2, find a formula that s1' satisfies but s2' doesn't
    have hdist : ∀ s2' : lts.image s2 μ,
        ∃ a, Satisfies lts s1' a ∧ ¬Satisfies lts s2'.val a := by
      intro ⟨s2', hs2'⟩
      exact exists_distinguishing_formula_satisfies (hnex s2' hs2')
    -- Build finite conjunction of distinguishing formulas
    let ft := Fintype.ofFinite (lts.image s2 μ)
    choose dist_formula hdist_spec using hdist
    let formulas := ft.elems.toList.map (fun s2' => dist_formula s2')
    let conjunction := Proposition.finiteAnd formulas
    -- s1 ⊨ ◇μ(⋀_i a_i) via s1'
    have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) := by
      simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq]
      exists s1'
      constructor
      · exact htr
      · rw [← satisfies_mem_denotation, satisfies_finiteAnd]
        intro a ha_mem
        obtain ⟨s2'_sub, _, ha_eq⟩ := List.mem_map.mp ha_mem
        rw [← ha_eq]
        exact (hdist_spec s2'_sub).1
    -- s2 ⊨ ◇μ(⋀_i a_i) by TheoryEq
    have hs2_diamond : Satisfies lts s2 (.diamond μ conjunction) :=
      theoryEq_satisfies h hs1_diamond
    -- But every s2' fails its own distinguishing formula
    simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq] at hs2_diamond
    obtain ⟨s2'', htr2, hsat⟩ := hs2_diamond
    let s2''_sub : lts.image s2 μ := ⟨s2'', htr2⟩
    rw [← satisfies_mem_denotation, satisfies_finiteAnd] at hsat
    have hmem : dist_formula s2''_sub ∈ formulas := by
      apply List.mem_map.mpr
      exists s2''_sub
      exact ⟨Finset.mem_toList.mpr (Fintype.complete s2''_sub), rfl⟩
    have := hsat (dist_formula s2''_sub) hmem
    exact (hdist_spec s2''_sub).2 this
  case right =>
    -- Symmetric to left case
    intro s2' htr
    by_contra hnex
    simp only [not_exists, not_and] at hnex
    have hfin : Finite (lts.image s1 μ) := image_finite s1 μ
    have hdist : ∀ s1' : lts.image s1 μ,
        ∃ a, Satisfies lts s2' a ∧ ¬Satisfies lts s1'.val a := by
      intro ⟨s1', hs1'⟩
      have hne := hnex s1' hs1'
      have hne' : ¬TheoryEq lts s2' s1' := fun h' => hne h'.symm
      exact exists_distinguishing_formula_satisfies hne'
    let ft := Fintype.ofFinite (lts.image s1 μ)
    choose dist_formula hdist_spec using hdist
    let formulas := ft.elems.toList.map (fun s1' => dist_formula s1')
    let conjunction := Proposition.finiteAnd formulas
    have hs2_diamond : Satisfies lts s2 (.diamond μ conjunction) := by
      simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq]
      exists s2'
      constructor
      · exact htr
      · rw [← satisfies_mem_denotation, satisfies_finiteAnd]
        intro a ha_mem
        obtain ⟨s1'_sub, _, ha_eq⟩ := List.mem_map.mp ha_mem
        rw [← ha_eq]
        exact (hdist_spec s1'_sub).1
    have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) :=
      theoryEq_satisfies h.symm hs2_diamond
    simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq] at hs1_diamond
    obtain ⟨s1'', htr1, hsat⟩ := hs1_diamond
    let s1''_sub : lts.image s1 μ := ⟨s1'', htr1⟩
    rw [← satisfies_mem_denotation, satisfies_finiteAnd] at hsat
    have hmem : dist_formula s1''_sub ∈ formulas := by
      apply List.mem_map.mpr
      exists s1''_sub
      exact ⟨Finset.mem_toList.mpr (Fintype.complete s1''_sub), rfl⟩
    have := hsat (dist_formula s1''_sub) hmem
    exact (hdist_spec s1''_sub).2 this

/-- Bisimulation preserves satisfaction in both directions. -/
lemma bisimulation_satisfies_iff {lts : LTS State Label}
  {hrb : lts.IsBisimulation r} (hr : r s1 s2) (a : Proposition Label) :
    Satisfies lts s1 a ↔ Satisfies lts s2 a := by
  induction a generalizing s1 s2
  case true => simp [Satisfies]
  case false => simp [Satisfies]
  case neg a ih =>
    simp only [Satisfies, Proposition.denotation, Set.mem_compl_iff]
    exact not_iff_not.mpr (ih hr)
  case and a b iha ihb =>
    simp only [Satisfies, Proposition.denotation, Set.mem_inter_iff]
    exact and_congr (iha hr) (ihb hr)
  case or a b iha ihb =>
    simp only [Satisfies, Proposition.denotation, Set.mem_union]
    exact or_congr (iha hr) (ihb hr)
  case diamond μ a ih =>
    simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq]
    constructor
    · intro ⟨s1', htr, hsat⟩
      obtain ⟨s2', htr', hr'⟩ := hrb.follow_fst hr htr
      exact ⟨s2', htr', (ih hr').mp hsat⟩
    · intro ⟨s2', htr, hsat⟩
      obtain ⟨s1', htr', hr'⟩ := hrb.follow_snd hr htr
      exact ⟨s1', htr', (ih hr').mpr hsat⟩
  case box μ a ih =>
    simp only [Satisfies, Proposition.denotation, Set.mem_setOf_eq]
    constructor
    · intro hs1 s2' htr
      obtain ⟨s1', htr', hr'⟩ := hrb.follow_snd hr htr
      exact (ih hr').mp (hs1 s1' htr')
    · intro hs2 s1' htr
      obtain ⟨s2', htr', hr'⟩ := hrb.follow_fst hr htr
      exact (ih hr').mpr (hs2 s2' htr')

@[scoped grind ⇒]
lemma bisimulation_satisfies {lts : LTS State Label}
   {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) (a : Proposition Label) (hs : Satisfies lts s1 a) :
    Satisfies lts s2 a :=
  (bisimulation_satisfies_iff (hrb := hrb) hr a).mp hs

lemma bisimulation_TheoryEq {lts : LTS State Label}
  {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) :
    TheoryEq lts s1 s2 := by
  unfold TheoryEq theory
  ext a
  apply Iff.intro <;> intro h
  case mp =>
    grind
  case mpr =>
    have hbs : s2 ~[lts] s1 := by grind [Bisimilarity.symm]
    obtain ⟨r', hr', hr'b⟩ := hbs
    grind

theorem theoryEq_eq_bisimilarity (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = Bisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exists TheoryEq lts
    grind
  · obtain ⟨r, hr, hrb⟩ := h
    apply bisimulation_TheoryEq hr
    exact hrb


end Cslib.Logic.HML
