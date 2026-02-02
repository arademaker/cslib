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
  | and (a : Proposition Label) (b : Proposition Label)
  | or (a : Proposition Label) (b : Proposition Label)
  | diamond (μ : Label) (a : Proposition Label)
  | box (μ : Label) (a : Proposition Label)

/-- Negation of a proposition. -/
@[simp, scoped grind =]
def Proposition.neg (a : Proposition Label) : Proposition Label :=
  match a with
  | .true => .false
  | .false => .true
  | and a b => or a.neg b.neg
  | or a b => and a.neg b.neg
  | diamond μ a => box μ a.neg
  | box μ a => diamond μ a.neg

/-- Finite conjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteAnd (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .and .true as

/-- Finite disjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteOr (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .or .false as

/-- Satisfaction relation. -/
@[scoped grind]
inductive Satisfies (lts : LTS State Label) : State → Proposition Label → Prop where
  | true {s : State} : Satisfies lts s .true
  | and {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s b →
    Satisfies lts s (.and a b)
  | or₁ {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s (.or a b)
  | or₂ {s : State} {a b : Proposition Label} :
    Satisfies lts s b → Satisfies lts s (.or a b)
  | diamond {s s' : State} {μ : Label} {a : Proposition Label}
    (htr : lts.Tr s μ s') (hs : Satisfies lts s' a) : Satisfies lts s (.diamond μ a)
  | box {s : State} {μ : Label} {a : Proposition Label}
    (h : ∀ s', lts.Tr s μ s' → Satisfies lts s' a) :
    Satisfies lts s (.box μ a)

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (a : Proposition Label) (lts : LTS State Label)
    : Set State :=
  match a with
  | .true => Set.univ
  | .false => ∅
  | .and a b => a.denotation lts ∩ b.denotation lts
  | .or a b => a.denotation lts ∪ b.denotation lts
  | .diamond μ a => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ a.denotation lts}
  | .box μ a => {s | ∀ s', lts.Tr s μ s' → s' ∈ a.denotation lts}

/-- The theory of a state is the set of all propositions that it satifies. -/
abbrev theory (s : State) (lts : LTS State Label) : Set (Proposition Label) :=
  {a | Satisfies lts s a}

abbrev TheoryEq (lts : LTS State Label) (s1 s2 : State) :=
  theory s1 lts = theory s2 lts

open Proposition LTS Bisimulation Simulation

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {lts : LTS State Label} :
    Satisfies lts s a ↔ s ∈ a.denotation lts := by
  induction a generalizing s <;> grind

-- @[scoped grind =]
theorem neg_satisfies {lts : LTS State Label} : Satisfies lts s a ↔ ¬Satisfies lts s a.neg := by
  induction a generalizing s <;> grind

@[scoped grind =]
theorem neg_denotation {lts : LTS State Label} (a : Proposition Label) :
    s ∈ a.denotation lts ↔ s ∉ a.neg.denotation lts := by
  grind [_=_ satisfies_mem_denotation, neg_satisfies]

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem satisfies_finiteAnd {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteAnd as) ↔ ∀ a ∈ as, Satisfies lts s a := by
  induction as <;> grind

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
@[scoped grind =]
theorem satisfies_finiteOr {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteOr as) ↔ ∃ a ∈ as, Satisfies lts s a := by
  induction as <;> grind

-- TODO Make this grind-friendly
-- @[scoped grind ⇒]
-- theorem theoryEq_denotation_eq {lts : LTS State Label}
--     (h : TheoryEq lts s1 s2) (a : Proposition Label) :
--     s1 ∈ a.denotation lts ↔ s2 ∈ a.denotation lts := by sorry

-- theorem
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

/-- If two states are not theory equivalent, there exists a distinguishing formula. -/
lemma not_theoryEq_satisfies (h : ¬(TheoryEq lts) s1 s2) :
    ∃ a, (Satisfies lts s1 a ∧ ¬Satisfies lts s2 a) := by
  grind [neg_satisfies]

/-- Helper: transfer satisfaction via theory equality. -/
theorem theoryEq_satisfies {lts : LTS State Label} (h : TheoryEq lts s1 s2)
    (hs : Satisfies lts s1 a) : Satisfies lts s2 a := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h a).mp hs

/-- Theory equivalence is a bisimulation. -/
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
      exact not_theoryEq_satisfies (hnex s2' hs2')
    -- Build finite conjunction of distinguishing formulas
    let ft := Fintype.ofFinite (lts.image s2 μ)
    choose dist_formula hdist_spec using hdist
    let formulas := ft.elems.toList.map (fun s2' => dist_formula s2')
    let conjunction := Proposition.finiteAnd formulas
    -- s1 ⊨ ◇μ(⋀_i a_i) via s1'
    have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) := by
      apply Satisfies.diamond htr
      rw [satisfies_finiteAnd]
      intro a ha_mem
      obtain ⟨s2'_sub, _, ha_eq⟩ := List.mem_map.mp ha_mem
      rw [← ha_eq]
      exact (hdist_spec s2'_sub).1
    -- s2 ⊨ ◇μ(⋀_i a_i) by TheoryEq
    have hs2_diamond : Satisfies lts s2 (.diamond μ conjunction) :=
      theoryEq_satisfies h hs1_diamond
    -- But every s2' fails its own distinguishing formula
    cases hs2_diamond
    rename_i s2'' htr2 hsat
    let s2''_sub : lts.image s2 μ := ⟨s2'', htr2⟩
    rw [satisfies_finiteAnd] at hsat
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
      exact not_theoryEq_satisfies hne'
    let ft := Fintype.ofFinite (lts.image s1 μ)
    choose dist_formula hdist_spec using hdist
    let formulas := ft.elems.toList.map (fun s1' => dist_formula s1')
    let conjunction := Proposition.finiteAnd formulas
    have hs2_diamond : Satisfies lts s2 (.diamond μ conjunction) := by
      apply Satisfies.diamond htr
      rw [satisfies_finiteAnd]
      intro a ha_mem
      obtain ⟨s1'_sub, _, ha_eq⟩ := List.mem_map.mp ha_mem
      rw [← ha_eq]
      exact (hdist_spec s1'_sub).1
    have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) :=
      theoryEq_satisfies h.symm hs2_diamond
    cases hs1_diamond
    rename_i s1'' htr1 hsat
    let s1''_sub : lts.image s1 μ := ⟨s1'', htr1⟩
    rw [satisfies_finiteAnd] at hsat
    have hmem : dist_formula s1''_sub ∈ formulas := by
      apply List.mem_map.mpr
      exists s1''_sub
      exact ⟨Finset.mem_toList.mpr (Fintype.complete s1''_sub), rfl⟩
    have := hsat (dist_formula s1''_sub) hmem
    exact (hdist_spec s1''_sub).2 this

@[scoped grind ⇒]
lemma bisimulation_satisfies {lts : LTS State Label}
    {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) (a : Proposition Label) (hs : Satisfies lts s1 a) :
    Satisfies lts s2 a := by
  induction a generalizing s1 s2
  case true => grind
  case false => grind
  case and a b => grind
  case or a b => grind
  case diamond μ a ih =>
    cases hs
    rename_i s1' htr hs
    have := hrb.follow_fst hr htr
    grind
  case box μ a ih =>
    apply Satisfies.box
    cases hs
    rename_i hs
    grind

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
