/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.Simulation

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

/-- Satisfaction relation. -/
@[scoped grind]
inductive Satisfies (lts : LTS State Label) : State → Proposition Label → Prop where
  | true {s : State} : Satisfies lts s .true
  | and {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s b →
    Satisfies lts s (.and a b)
  | orLeft {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s (.or a b)
  | orRight {s : State} {a b : Proposition Label} :
    Satisfies lts s b → Satisfies lts s (.or a b)
  | diamond {s s' : State} {μ : Label} {a : Proposition Label}
    (htr : lts.Tr s μ s') (hs : Satisfies lts s' a) : Satisfies lts s (.diamond μ a)
  | box {s : State} {μ : Label} {a : Proposition Label}
    (h : ∀ s', lts.Tr s μ s' → Satisfies lts s' a) :
    Satisfies lts s (.box μ a)

/-- The theory of a state is the set of all propositions that it satifies. -/
abbrev theory (s : State) (lts : LTS State Label) : Set (Proposition Label) :=
  {a | Satisfies lts s a}

abbrev theoryEq (lts : LTS State Label) (s1 s2 : State) := theory s1 lts = theory s2 lts

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (a : Proposition Label) (lts : LTS State Label) : Set State :=
  match a with
  | .true => Set.univ
  | .false => ∅
  | .and a b => a.denotation lts ∩ b.denotation lts
  | .or a b => a.denotation lts ∪ b.denotation lts
  | .diamond μ a => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ a.denotation lts}
  | .box μ a => {s | ∀ s', lts.Tr s μ s' → s' ∈ a.denotation lts}

open Proposition Satisfies LTS Bisimulation Simulation

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind _=_]
theorem satisfies_mem_denotation {lts : LTS State Label} :
    Satisfies lts s a ↔ s ∈ a.denotation lts := by
  induction a generalizing s <;> grind

lemma not_theoryEq_satisfies (h : ¬(theoryEq lts) s1 s2) :
    ∃ a, Satisfies lts s1 a ∧ ¬Satisfies lts s2 a :=
  sorry

@[scoped grind ⇒]
lemma theoryEq_isBisimulation (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    lts.IsBisimulation (theoryEq lts) := by
  intro s1 s2 h μ
  constructor
  case left =>
    intro s1' htr
    by_contra hnex
    simp [not_exists] at hnex
    -- Gotta build a bound n and a map of distinguishable propositions/witnesses:
    -- f i -> s2_i, a_i such that s2 -μ-> s2_i x s2_i ⊨ a_i x s1' doesn't
    -- now build d = [μ] V_i a_i
    -- prove s2 ⊨ d
    -- prove s1 doesn't
    -- Contradiction with h
    have htr2 : ∃ s2', lts.Tr s2 μ s2' := by
      let a := Proposition.diamond μ .true
      have hs1 : Satisfies lts s1 a := by grind
      have hs2 : Satisfies lts s2 a := by
        apply Set.ext_iff.1 at h
        specialize h a
        grind
      grind
    obtain ⟨s2', htr2⟩ := htr2
    exists s2'
    constructor
    · exact htr2
    · apply Set.ext_iff.2
      intro a
      apply Iff.intro <;> intro hmem
      case mp =>

        sorry
      case mpr => sorry
  case right =>
    sorry

@[scoped grind ⇒]
lemma bisimulation_satisfies {lts : LTS State Label} {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) (a : Proposition Label) (hs : Satisfies lts s1 a) :
    Satisfies lts s2 a := by
  induction a generalizing s1 s2
  case true => grind
  case false => grind
  case and a b => grind
  case or a b => grind
  case diamond μ a ih =>
    cases hs
    grind
  case box μ a ih => grind

-- @[scoped grind ]
lemma bisimulation_theoryEq {lts : LTS State Label} {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) :
    theoryEq lts s1 s2 := by
  unfold theoryEq theory
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
    theoryEq lts = Bisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exists theoryEq lts
    grind
  · obtain ⟨r, hr, hrb⟩ := h
    apply bisimulation_theoryEq hr
    exact hrb

end Cslib.Logic.HML
