/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Optlib.Lindahl.Basic
import Optlib.Optimality.ConvexKKTFinite

/-!
# Capped Shmyrev program

This file contains the Shmyrev objective, KKT data, subgradient calculations,
and KKT-to-Lindahl-equilibrium lemmas for the formal proof of
`thm:lindahl shmyrev capped` from `lindahl.tex`.

The basic capped Lindahl model and the definition of Lindahl equilibrium live
in `Optlib.Lindahl.Basic`.
-/

open BigOperators
open scoped Topology

namespace Optlib
namespace Lindahl
namespace ShmyrevCapped

noncomputable section

set_option linter.unusedSectionVars false

variable {nAgents nProjects : ℕ}

def contributionNonnegative (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : Prop :=
  ∀ e, 0 <= b e

def shmyrevFeasible (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : Prop :=
  contributionNonnegative I b ∧
    (∀ i, agentSpend I b i <= I.budget i) ∧
    (∀ j, projectTotal I b j <= I.cap j)

/-- The affine constraints of the capped Shmyrev program, excluding
nonnegativity. Nonnegativity is the domain of the objective. -/
inductive ShmyrevConstraint (nAgents nProjects : ℕ) where
  | budget : Agent nAgents -> ShmyrevConstraint nAgents nProjects
  | cap : Project nProjects -> ShmyrevConstraint nAgents nProjects
deriving DecidableEq

instance : Fintype (ShmyrevConstraint nAgents nProjects) :=
  Fintype.ofEquiv (Agent nAgents ⊕ Project nProjects)
    { toFun := fun k =>
        match k with
        | Sum.inl i => ShmyrevConstraint.budget i
        | Sum.inr j => ShmyrevConstraint.cap j
      invFun := fun k =>
        match k with
        | ShmyrevConstraint.budget i => Sum.inl i
        | ShmyrevConstraint.cap j => Sum.inr j
      left_inv := by
        intro k
        cases k <;> rfl
      right_inv := by
        intro k
        cases k <;> rfl }

def shmyrevConstraintRhs (I : CappedInstance nAgents nProjects) :
    ShmyrevConstraint nAgents nProjects -> ℝ
  | ShmyrevConstraint.budget i => I.budget i
  | ShmyrevConstraint.cap j => I.cap j

def shmyrevConstraintFunctional (I : CappedInstance nAgents nProjects) :
    ShmyrevConstraint nAgents nProjects -> Contribution I -> ℝ
  | ShmyrevConstraint.budget i, b => agentSpend I b i
  | ShmyrevConstraint.cap j, b => projectTotal I b j

theorem shmyrevConstraintFunctional_linear
    (I : CappedInstance nAgents nProjects)
    (k : ShmyrevConstraint nAgents nProjects) :
    Optlib.DomainSubgradient.IsLinearFunctional (shmyrevConstraintFunctional I k) := by
  constructor
  · intro b c
    cases k with
    | budget i =>
        exact agentSpend_add I b c i
    | cap j =>
        exact projectTotal_add I b c j
  · intro r b
    cases k with
    | budget i =>
        exact agentSpend_smul I r b i
    | cap j =>
        exact projectTotal_smul I r b j

theorem shmyrevFeasible_iff_domainAffineFeasible
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    shmyrevFeasible I b ↔
      b ∈ Optlib.KKT.DomainAffineFeasible
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevConstraintFunctional I) (shmyrevConstraintRhs I) := by
  constructor
  · intro hb
    refine ⟨hb.1, ?_⟩
    intro k
    cases k with
    | budget i =>
        exact hb.2.1 i
    | cap j =>
        exact hb.2.2 j
  · intro hb
    refine ⟨hb.1, ?_, ?_⟩
    · intro i
      exact hb.2 (ShmyrevConstraint.budget i)
    · intro j
      exact hb.2 (ShmyrevConstraint.cap j)

/-- The full affine KKT constraints used in the paper, including the redundant
nonnegativity inequalities `-b_e <= 0` so that the KKT multipliers include the
`eta_e` family. -/
inductive ShmyrevKKTConstraint (I : CappedInstance nAgents nProjects) where
  | budget : Agent nAgents -> ShmyrevKKTConstraint I
  | cap : Project nProjects -> ShmyrevKKTConstraint I
  | nonneg : I.PositiveEdge -> ShmyrevKKTConstraint I
deriving DecidableEq

def shmyrevKKTConstraintEquiv (I : CappedInstance nAgents nProjects) :
    ((Agent nAgents ⊕ Project nProjects) ⊕ I.PositiveEdge) ≃
      ShmyrevKKTConstraint I where
  toFun := fun k =>
        match k with
        | Sum.inl (Sum.inl i) => ShmyrevKKTConstraint.budget i
        | Sum.inl (Sum.inr j) => ShmyrevKKTConstraint.cap j
        | Sum.inr e => ShmyrevKKTConstraint.nonneg e
  invFun := fun k =>
        match k with
        | ShmyrevKKTConstraint.budget i => Sum.inl (Sum.inl i)
        | ShmyrevKKTConstraint.cap j => Sum.inl (Sum.inr j)
        | ShmyrevKKTConstraint.nonneg e => Sum.inr e
  left_inv := by
        intro k
        cases k with
        | inl k =>
            cases k <;> rfl
        | inr e =>
            rfl
  right_inv := by
        intro k
        cases k <;> rfl

instance (I : CappedInstance nAgents nProjects) :
    Fintype (ShmyrevKKTConstraint I) :=
  Fintype.ofEquiv ((Agent nAgents ⊕ Project nProjects) ⊕ I.PositiveEdge)
    (shmyrevKKTConstraintEquiv I)

def shmyrevKKTConstraintRhs (I : CappedInstance nAgents nProjects) :
    ShmyrevKKTConstraint I -> ℝ
  | ShmyrevKKTConstraint.budget i => I.budget i
  | ShmyrevKKTConstraint.cap j => I.cap j
  | ShmyrevKKTConstraint.nonneg _e => 0

def shmyrevKKTConstraintFunctional (I : CappedInstance nAgents nProjects) :
    ShmyrevKKTConstraint I -> Contribution I -> ℝ
  | ShmyrevKKTConstraint.budget i, b => agentSpend I b i
  | ShmyrevKKTConstraint.cap j, b => projectTotal I b j
  | ShmyrevKKTConstraint.nonneg e, b => -b e

theorem shmyrevKKTConstraintFunctional_linear
    (I : CappedInstance nAgents nProjects) (k : ShmyrevKKTConstraint I) :
    Optlib.DomainSubgradient.IsLinearFunctional (shmyrevKKTConstraintFunctional I k) := by
  constructor
  · intro b c
    cases k with
    | budget i =>
        exact agentSpend_add I b c i
    | cap j =>
        exact projectTotal_add I b c j
    | nonneg e =>
        simp [shmyrevKKTConstraintFunctional, add_comm]
  · intro r b
    cases k with
    | budget i =>
        exact agentSpend_smul I r b i
    | cap j =>
        exact projectTotal_smul I r b j
    | nonneg e =>
        simp [shmyrevKKTConstraintFunctional, Pi.smul_apply, smul_eq_mul, mul_neg]

theorem shmyrevFeasible_iff_domainKKTFeasible
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    shmyrevFeasible I b ↔
      b ∈ Optlib.KKT.DomainAffineFeasible
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevKKTConstraintFunctional I) (shmyrevKKTConstraintRhs I) := by
  constructor
  · intro hb
    refine ⟨hb.1, ?_⟩
    intro k
    cases k with
    | budget i =>
        exact hb.2.1 i
    | cap j =>
        exact hb.2.2 j
    | nonneg e =>
        simpa [shmyrevKKTConstraintFunctional, shmyrevKKTConstraintRhs] using
          neg_nonpos.mpr (hb.1 e)
  · intro hb
    refine ⟨?_, ?_, ?_⟩
    · intro e
      have h := hb.2 (ShmyrevKKTConstraint.nonneg e)
      simpa [shmyrevKKTConstraintFunctional, shmyrevKKTConstraintRhs] using
        neg_nonpos.mp h
    · intro i
      exact hb.2 (ShmyrevKKTConstraint.budget i)
    · intro j
      exact hb.2 (ShmyrevKKTConstraint.cap j)

def contributionFunctional (I : CappedInstance nAgents nProjects)
    (g : Contribution I) : Contribution I -> ℝ :=
  fun z => ∑ e : I.PositiveEdge, g e * z e

theorem contributionFunctional_linear
    (I : CappedInstance nAgents nProjects) (g : Contribution I) :
    Optlib.DomainSubgradient.IsLinearFunctional (contributionFunctional I g) := by
  constructor
  · intro z w
    unfold contributionFunctional
    simp_rw [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  · intro r z
    unfold contributionFunctional
    simp_rw [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    ring

def basisContribution (I : CappedInstance nAgents nProjects)
    (e : I.PositiveEdge) : Contribution I :=
  fun e' => if e' = e then 1 else 0

@[simp] theorem basisContribution_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    basisContribution I e e = 1 := by
  simp [basisContribution]

theorem basisContribution_ne
    (I : CappedInstance nAgents nProjects) {e e' : I.PositiveEdge}
    (hne : e' ≠ e) :
    basisContribution I e e' = 0 := by
  simp [basisContribution, hne]

theorem contributionFunctional_basis
    (I : CappedInstance nAgents nProjects) (g : Contribution I)
    (e : I.PositiveEdge) :
    contributionFunctional I g (basisContribution I e) = g e := by
  unfold contributionFunctional basisContribution
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _he' hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ e))

theorem contributionAt_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    contributionAt I (basisContribution I e) (edgeAgent e.1) (edgeProject e.1) = 1 := by
  unfold contributionAt
  have hmem : (edgeAgent e.1, edgeProject e.1) ∈ I.positiveEdges := by
    simp [edgeAgent, edgeProject, e.2]
  have heq : (⟨(edgeAgent e.1, edgeProject e.1), hmem⟩ : I.PositiveEdge) = e := by
    ext <;> simp [edgeAgent, edgeProject]
  simp [hmem, heq]

theorem agentSpend_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    agentSpend I (basisContribution I e) (edgeAgent e.1) = 1 := by
  unfold agentSpend
  rw [Finset.sum_eq_single (edgeProject e.1)]
  · exact contributionAt_basis_self I e
  · intro j _hj hne
    unfold contributionAt
    by_cases hmem : (edgeAgent e.1, j) ∈ I.positiveEdges
    · have hsub_ne : (⟨(edgeAgent e.1, j), hmem⟩ : I.PositiveEdge) ≠ e := by
        intro heq
        apply hne
        exact congrArg (fun e' : I.PositiveEdge => edgeProject e'.1) heq
      simp [hmem, basisContribution_ne I hsub_ne]
    · simp [hmem]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (edgeProject e.1)))

theorem projectTotal_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    projectTotal I (basisContribution I e) (edgeProject e.1) = 1 := by
  unfold projectTotal
  rw [Finset.sum_eq_single (edgeAgent e.1)]
  · exact contributionAt_basis_self I e
  · intro i _hi hne
    unfold contributionAt
    by_cases hmem : (i, edgeProject e.1) ∈ I.positiveEdges
    · have hsub_ne : (⟨(i, edgeProject e.1), hmem⟩ : I.PositiveEdge) ≠ e := by
        intro heq
        apply hne
        exact congrArg (fun e' : I.PositiveEdge => edgeAgent e'.1) heq
      simp [hmem, basisContribution_ne I hsub_ne]
    · simp [hmem]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (edgeAgent e.1)))

theorem agentSpend_basis_ne
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge)
    {i : Agent nAgents} (hne : i ≠ edgeAgent e.1) :
    agentSpend I (basisContribution I e) i = 0 := by
  unfold agentSpend
  apply Finset.sum_eq_zero
  intro j _hj
  unfold contributionAt
  by_cases hmem : (i, j) ∈ I.positiveEdges
  · have hsub_ne : (⟨(i, j), hmem⟩ : I.PositiveEdge) ≠ e := by
      intro heq
      apply hne
      exact congrArg (fun e' : I.PositiveEdge => edgeAgent e'.1) heq
    simp [hmem, basisContribution_ne I hsub_ne]
  · simp [hmem]

theorem projectTotal_basis_ne
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge)
    {j : Project nProjects} (hne : j ≠ edgeProject e.1) :
    projectTotal I (basisContribution I e) j = 0 := by
  unfold projectTotal
  apply Finset.sum_eq_zero
  intro i _hi
  unfold contributionAt
  by_cases hmem : (i, j) ∈ I.positiveEdges
  · have hsub_ne : (⟨(i, j), hmem⟩ : I.PositiveEdge) ≠ e := by
      intro heq
      apply hne
      exact congrArg (fun e' : I.PositiveEdge => edgeProject e'.1) heq
    simp [hmem, basisContribution_ne I hsub_ne]
  · simp [hmem]

@[simp] theorem lineContribution_apply_self
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) (t : ℝ) :
    (b + t • basisContribution I e) e = b e + t := by
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem lineContribution_apply_ne
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    {e e' : I.PositiveEdge} (hne : e' ≠ e) (t : ℝ) :
    (b + t • basisContribution I e) e' = b e' := by
  rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I hne]
  simp

@[simp] theorem projectTotal_line_self
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) (t : ℝ) :
    projectTotal I (b + t • basisContribution I e) (edgeProject e.1) =
      projectTotal I b (edgeProject e.1) + t := by
  rw [projectTotal_add, projectTotal_smul, projectTotal_basis_self]
  ring

theorem projectTotal_line_ne
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) {j : Project nProjects}
    (hne : j ≠ edgeProject e.1) (t : ℝ) :
    projectTotal I (b + t • basisContribution I e) j =
      projectTotal I b j := by
  rw [projectTotal_add, projectTotal_smul, projectTotal_basis_ne I e hne]
  ring

theorem valuationSum_line
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) (t : ℝ) :
    (∑ e' : I.PositiveEdge,
        (b + t • basisContribution I e) e' * Real.log (I.edgeValuation e')) =
      (∑ e' : I.PositiveEdge, b e' * Real.log (I.edgeValuation e')) +
        t * Real.log (I.edgeValuation e) := by
  calc
    (∑ e' : I.PositiveEdge,
        (b + t • basisContribution I e) e' * Real.log (I.edgeValuation e'))
        =
        ∑ e' : I.PositiveEdge,
          (b e' * Real.log (I.edgeValuation e') +
            if e' = e then t * Real.log (I.edgeValuation e) else 0) := by
        apply Finset.sum_congr rfl
        intro e' _he'
        by_cases heq : e' = e
        · subst e'
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        · rw [lineContribution_apply_ne I b heq t]
          simp [heq]
    _ =
      (∑ e' : I.PositiveEdge, b e' * Real.log (I.edgeValuation e')) +
        ∑ e' : I.PositiveEdge,
          (if e' = e then t * Real.log (I.edgeValuation e) else 0) := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ e' : I.PositiveEdge, b e' * Real.log (I.edgeValuation e')) +
        t * Real.log (I.edgeValuation e) := by
        congr 1
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _he' hne
          simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ e))

theorem shmyrevKKTConstraintFunctional_budget_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    shmyrevKKTConstraintFunctional I
      (ShmyrevKKTConstraint.budget (edgeAgent e.1)) (basisContribution I e) = 1 :=
  agentSpend_basis_self I e

theorem shmyrevKKTConstraintFunctional_cap_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    shmyrevKKTConstraintFunctional I
      (ShmyrevKKTConstraint.cap (edgeProject e.1)) (basisContribution I e) = 1 :=
  projectTotal_basis_self I e

theorem shmyrevKKTConstraintFunctional_nonneg_basis_self
    (I : CappedInstance nAgents nProjects) (e : I.PositiveEdge) :
    shmyrevKKTConstraintFunctional I
      (ShmyrevKKTConstraint.nonneg e) (basisContribution I e) = -1 := by
  simp [shmyrevKKTConstraintFunctional]

theorem multiplierFunctional_shmyrevKKTConstraint
    (I : CappedInstance nAgents nProjects)
    (Lambda : ShmyrevKKTConstraint I -> ℝ) (z : Contribution I) :
    Optlib.KKT.multiplierFunctional (shmyrevKKTConstraintFunctional I) Lambda z =
      (∑ i : Agent nAgents,
        Lambda (ShmyrevKKTConstraint.budget i) * agentSpend I z i) +
        (∑ j : Project nProjects,
          Lambda (ShmyrevKKTConstraint.cap j) * projectTotal I z j) +
          (∑ e : I.PositiveEdge,
            Lambda (ShmyrevKKTConstraint.nonneg e) * (-(z e))) := by
  unfold Optlib.KKT.multiplierFunctional
  rw [← (shmyrevKKTConstraintEquiv I).sum_comp
    (fun k : ShmyrevKKTConstraint I =>
      Lambda k * shmyrevKKTConstraintFunctional I k z)]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [shmyrevKKTConstraintEquiv, shmyrevKKTConstraintFunctional,
    Finset.sum_neg_distrib, mul_neg, add_assoc]

theorem separated_stationarity_coordinate
    (I : CappedInstance nAgents nProjects) {g : Contribution I}
    {lambda : Agent nAgents -> ℝ} {mu : Project nProjects -> ℝ}
    {eta : I.PositiveEdge -> ℝ}
    (hstat : ∀ z : Contribution I,
      contributionFunctional I g z +
        (∑ i : Agent nAgents, lambda i * agentSpend I z i) +
          (∑ j : Project nProjects, mu j * projectTotal I z j) +
            (∑ e' : I.PositiveEdge, eta e' * (-(z e'))) = 0) :
    ∀ e : I.PositiveEdge,
      g e + lambda (edgeAgent e.1) + mu (edgeProject e.1) - eta e = 0 := by
  intro e
  have h := hstat (basisContribution I e)
  have hbudget :
      (∑ i : Agent nAgents,
        lambda i * agentSpend I (basisContribution I e) i) =
        lambda (edgeAgent e.1) := by
    rw [Finset.sum_eq_single (edgeAgent e.1)]
    · rw [agentSpend_basis_self]
      ring
    · intro i _hi hne
      rw [agentSpend_basis_ne I e hne]
      ring
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ (edgeAgent e.1)))
  have hcap :
      (∑ j : Project nProjects,
        mu j * projectTotal I (basisContribution I e) j) =
        mu (edgeProject e.1) := by
    rw [Finset.sum_eq_single (edgeProject e.1)]
    · rw [projectTotal_basis_self]
      ring
    · intro j _hj hne
      rw [projectTotal_basis_ne I e hne]
      ring
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ (edgeProject e.1)))
  have heta :
      (∑ e' : I.PositiveEdge, eta e' * (-(basisContribution I e e'))) =
        - eta e := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro e' _he' hne
      rw [basisContribution_ne I hne]
      ring
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ e))
  rw [contributionFunctional_basis, hbudget, hcap, heta] at h
  linarith

theorem contributionNonnegative_convexDomain
    (I : CappedInstance nAgents nProjects) :
    Optlib.DomainSubgradient.ConvexDomain
      {b : Contribution I | contributionNonnegative I b} := by
  intro b hb c hc a d ha hd _had
  intro e
  simp only [Set.mem_setOf_eq, contributionNonnegative] at hb hc ⊢
  exact add_nonneg (smul_nonneg ha (hb e)) (smul_nonneg hd (hc e))

theorem projectTotal_nonneg
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) (j : Project nProjects) :
    0 <= projectTotal I b j := by
  unfold projectTotal
  apply Finset.sum_nonneg
  intro i _hi
  unfold contributionAt
  by_cases h : (i, j) ∈ I.positiveEdges
  · simp [h, hb ⟨(i, j), h⟩]
  · simp [h]

theorem contributionAt_le_projectTotal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) (i : Agent nAgents) (j : Project nProjects) :
    contributionAt I b i j <= projectTotal I b j := by
  unfold projectTotal
  have hnonneg :
      ∀ k ∈ (Finset.univ : Finset (Agent nAgents)), 0 <= contributionAt I b k j := by
    intro k _hk
    unfold contributionAt
    by_cases h : (k, j) ∈ I.positiveEdges
    · simp [h, hb ⟨(k, j), h⟩]
    · simp [h]
  simpa using
    (Finset.single_le_sum (s := (Finset.univ : Finset (Agent nAgents)))
      (f := fun k => contributionAt I b k j) hnonneg (Finset.mem_univ i))

theorem contribution_eq_zero_of_projectTotal_eq_zero
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) {e : I.PositiveEdge}
    (he : edgeProject e.1 = j) :
    b e = 0 := by
  have hzero : contributionAt I b (edgeAgent e.1) j = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i : Agent nAgents => contributionAt I b i j) ?_).mp
        hj (edgeAgent e.1) (Finset.mem_univ (edgeAgent e.1))
    · exact hs
    · intro i _hi
      unfold contributionAt
      by_cases h : (i, j) ∈ I.positiveEdges
      · simp [h, hb ⟨(i, j), h⟩]
      · simp [h]
  unfold contributionAt at hzero
  have hp : (edgeAgent e.1, j) = e.1 := by
    ext
    · rfl
    · simpa [edgeProject] using congrArg Fin.val he.symm
  have hmem : (edgeAgent e.1, j) ∈ I.positiveEdges := by
    simp [hp, e.2]
  have heq : (⟨(edgeAgent e.1, j), hmem⟩ : I.PositiveEdge) = e := by
    exact Subtype.ext hp
  simpa [hmem, heq] using hzero

theorem sum_projectTotal_eq_sum_agentSpend
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    (∑ j : Project nProjects, projectTotal I b j) =
      ∑ i : Agent nAgents, agentSpend I b i := by
  unfold projectTotal
  unfold agentSpend
  rw [Finset.sum_comm]

/-- The entropy term `h(b_j) = sum_i b_ij log (b_ij / x_j(b))`.
It is real-valued here; the surrounding domain predicates carry the intended
nonnegativity side conditions. -/
def projectEntropyTerm (I : CappedInstance nAgents nProjects)
    (b : Contribution I) (j : Project nProjects) : ℝ :=
  if projectTotal I b j = 0 then 0
  else
    ∑ e : I.PositiveEdge,
      if edgeProject e.1 = j then
        b e * Real.log (b e / projectTotal I b j)
      else 0

theorem projectEntropyTerm_eq_zero_of_projectTotal_eq_zero
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    {j : Project nProjects} (hj : projectTotal I b j = 0) :
    projectEntropyTerm I b j = 0 := by
  unfold projectEntropyTerm
  simp [hj]

theorem projectTotal_congr_project
    (I : CappedInstance nAgents nProjects) {b c : Contribution I}
    {j : Project nProjects}
    (h : ∀ e : I.PositiveEdge, edgeProject e.1 = j -> b e = c e) :
    projectTotal I b j = projectTotal I c j := by
  unfold projectTotal contributionAt
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hmem : (i, j) ∈ I.positiveEdges
  · have heq := h ⟨(i, j), hmem⟩ rfl
    simp [hmem, heq]
  · simp [hmem]

theorem projectEntropyTerm_congr_project
    (I : CappedInstance nAgents nProjects) {b c : Contribution I}
    {j : Project nProjects}
    (h : ∀ e : I.PositiveEdge, edgeProject e.1 = j -> b e = c e) :
    projectEntropyTerm I b j = projectEntropyTerm I c j := by
  have htotal := projectTotal_congr_project I h
  unfold projectEntropyTerm
  rw [htotal]
  by_cases hc : projectTotal I c j = 0
  · simp [hc]
  · simp [hc]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases heq : edgeProject e.1 = j
    · rw [if_pos heq, if_pos heq, h e heq]
    · simp [heq]

/-- Algebraically equivalent form of `projectEntropyTerm` on the nonnegative
orthant. This version is continuous by mathlib's continuity of `x * log x`. -/
def projectEntropyContinuousTerm (I : CappedInstance nAgents nProjects)
    (b : Contribution I) (j : Project nProjects) : ℝ :=
  (∑ e : I.PositiveEdge,
    if edgeProject e.1 = j then b e * Real.log (b e) else 0) -
      projectTotal I b j * Real.log (projectTotal I b j)

theorem projectEntropyContinuousTerm_continuous
    (I : CappedInstance nAgents nProjects) (j : Project nProjects) :
    Continuous (fun b : Contribution I => projectEntropyContinuousTerm I b j) := by
  unfold projectEntropyContinuousTerm
  apply Continuous.sub
  · apply continuous_finset_sum
    intro e _he
    by_cases h : edgeProject e.1 = j
    · simp [h]
      fun_prop
    · simp [h]
      exact continuous_const
  · have hpt : Continuous (fun b : Contribution I => projectTotal I b j) := by
      unfold projectTotal contributionAt
      apply continuous_finset_sum
      intro i _hi
      by_cases h : (i, j) ∈ I.positiveEdges
      · simp [h]
        fun_prop
      · simp [h]
        exact continuous_const
    exact Real.Continuous.mul_log hpt

/-- Continuous expression corresponding to the negative capped Shmyrev
objective on the nonnegative orthant. -/
def shmyrevContinuousObjective (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : ℝ :=
  - (∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
    ∑ j : Project nProjects, projectEntropyContinuousTerm I b j

theorem shmyrevContinuousObjective_continuous
    (I : CappedInstance nAgents nProjects) :
    Continuous (shmyrevContinuousObjective I) := by
  unfold shmyrevContinuousObjective
  apply Continuous.add
  · apply Continuous.neg
    apply continuous_finset_sum
    intro e _he
    fun_prop
  · apply continuous_finset_sum
    intro j _hj
    exact projectEntropyContinuousTerm_continuous I j

theorem projectEntropyContinuousTerm_eq_zero_of_projectTotal_eq_zero
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) :
    projectEntropyContinuousTerm I b j = 0 := by
  unfold projectEntropyContinuousTerm
  have hsum :
      (∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then b e * Real.log (b e) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _he
    by_cases heq : edgeProject e.1 = j
    · have hbzero := contribution_eq_zero_of_projectTotal_eq_zero I hb hj (e := e) heq
      simp [heq, hbzero]
    · simp [heq]
  rw [hsum, hj]
  simp

theorem projectEntropyTerm_eq_continuousTerm_of_projectTotal_eq_zero
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) :
    projectEntropyTerm I b j = projectEntropyContinuousTerm I b j := by
  rw [projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hj,
    projectEntropyContinuousTerm_eq_zero_of_projectTotal_eq_zero I hb hj]

theorem sum_positiveEdges_project_eq_projectTotal
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (j : Project nProjects) :
    (∑ e : I.PositiveEdge, if edgeProject e.1 = j then b e else 0) =
      projectTotal I b j := by
  classical
  let sE : Finset I.PositiveEdge :=
    Finset.univ.filter fun e : I.PositiveEdge => edgeProject e.1 = j
  let sA : Finset (Agent nAgents) :=
    Finset.univ.filter fun i : Agent nAgents => (i, j) ∈ I.positiveEdges
  have hleft :
      (∑ e : I.PositiveEdge, if edgeProject e.1 = j then b e else 0) =
        ∑ e ∈ sE, b e := by
    unfold sE
    rw [Finset.sum_filter]
  have hright :
      projectTotal I b j =
        ∑ i ∈ sA,
          if h : (i, j) ∈ I.positiveEdges then b ⟨(i, j), h⟩ else 0 := by
    unfold projectTotal contributionAt sA
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hmem : (i, j) ∈ I.positiveEdges
    · simp [hmem]
    · simp [hmem]
  rw [hleft, hright]
  refine Finset.sum_bij
    (fun e _he => edgeAgent e.1)
    ?_ ?_ ?_ ?_
  · intro e he
    dsimp [sE, sA] at he ⊢
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hproj := he.2
    have hp : (edgeAgent e.1, j) = e.1 := by
      ext
      · rfl
      · exact congrArg Fin.val hproj.symm
    simp [hp, e.2]
  · intro e₁ he₁ e₂ he₂ hagent
    apply Subtype.ext
    dsimp [sE] at he₁ he₂
    have hproj₁ := (Finset.mem_filter.mp he₁).2
    have hproj₂ := (Finset.mem_filter.mp he₂).2
    change edgeAgent e₁.1 = edgeAgent e₂.1 at hagent
    ext
    · exact congrArg Fin.val (by simpa [edgeAgent] using hagent)
    · exact congrArg Fin.val (by simpa [edgeProject] using hproj₁.trans hproj₂.symm)
  · intro i hi
    dsimp [sA] at hi
    have hmem : (i, j) ∈ I.positiveEdges := (Finset.mem_filter.mp hi).2
    refine ⟨⟨(i, j), hmem⟩, ?_, ?_⟩
    · dsimp [sE]
      simp [edgeProject]
    · rfl
  · intro e he
    dsimp [sE] at he
    have hproj := (Finset.mem_filter.mp he).2
    have hmem : (edgeAgent e.1, j) ∈ I.positiveEdges := by
      have hp : (edgeAgent e.1, j) = e.1 := by
        ext
        · rfl
        · exact congrArg Fin.val hproj.symm
      simp [hp, e.2]
    have heq : (⟨(edgeAgent e.1, j), hmem⟩ : I.PositiveEdge) = e := by
      apply Subtype.ext
      ext
      · rfl
      · exact congrArg Fin.val (by simpa [edgeProject] using hproj.symm)
    simp [hmem, heq]

theorem mul_log_div_eq_mul_log_sub
    {x t : ℝ} (hx : 0 <= x) (ht : 0 < t) :
    x * Real.log (x / t) = x * Real.log x - x * Real.log t := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt ht), mul_sub]

theorem binary_log_sum_inequality
    {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 <= x₁) (hx₂ : 0 <= x₂)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    (x₁ + x₂) * Real.log ((x₁ + x₂) / (y₁ + y₂)) <=
      x₁ * Real.log (x₁ / y₁) + x₂ * Real.log (x₂ / y₂) := by
  let Y := y₁ + y₂
  have hYpos : 0 < Y := add_pos hy₁ hy₂
  have hYne : Y ≠ 0 := ne_of_gt hYpos
  have hy₁ne : y₁ ≠ 0 := ne_of_gt hy₁
  have hy₂ne : y₂ ≠ 0 := ne_of_gt hy₂
  have hw₁ : 0 <= y₁ / Y := div_nonneg hy₁.le hYpos.le
  have hw₂ : 0 <= y₂ / Y := div_nonneg hy₂.le hYpos.le
  have hwsum : y₁ / Y + y₂ / Y = 1 := by
    field_simp [Y, hYne]
  have hx₁ratio : x₁ / y₁ ∈ Set.Ici (0 : ℝ) := by
    exact div_nonneg hx₁ hy₁.le
  have hx₂ratio : x₂ / y₂ ∈ Set.Ici (0 : ℝ) := by
    exact div_nonneg hx₂ hy₂.le
  have hconv := Real.convexOn_mul_log.2
    hx₁ratio hx₂ratio hw₁ hw₂ hwsum
  have harg :
      y₁ / Y * (x₁ / y₁) + y₂ / Y * (x₂ / y₂) =
        (x₁ + x₂) / Y := by
    field_simp [Y, hy₁ne, hy₂ne, hYne]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hconv hYpos.le
  have hleft :
      Y * ((y₁ / Y * (x₁ / y₁) + y₂ / Y * (x₂ / y₂)) *
          Real.log (y₁ / Y * (x₁ / y₁) + y₂ / Y * (x₂ / y₂))) =
        (x₁ + x₂) * Real.log ((x₁ + x₂) / Y) := by
    rw [harg]
    field_simp [hYne]
  have hright :
      Y * (y₁ / Y * ((x₁ / y₁) * Real.log (x₁ / y₁)) +
          y₂ / Y * ((x₂ / y₂) * Real.log (x₂ / y₂))) =
        x₁ * Real.log (x₁ / y₁) + x₂ * Real.log (x₂ / y₂) := by
    field_simp [Y, hy₁ne, hy₂ne, hYne]
    ring
  simpa [hleft, hright, Y, smul_eq_mul, mul_assoc] using hscaled

theorem le_one_of_mul_log_nonpos {x : ℝ}
    (hlog : x * Real.log x <= 0) :
    x <= 1 := by
  by_contra hnot
  have hxgt : 1 < x := lt_of_not_ge hnot
  have hxpos : 0 < x := lt_trans zero_lt_one hxgt
  have hlogpos : 0 < Real.log x := Real.log_pos hxgt
  have hprodpos : 0 < x * Real.log x := mul_pos hxpos hlogpos
  linarith

theorem hasDerivAt_add_mul_log_line {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => (x + t) * Real.log (x + t))
      (Real.log x + 1) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x + t) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).const_add x
  have hmul : HasDerivAt (fun y : ℝ => y * Real.log y)
      (Real.log (x + 0) + 1) (x + 0) := by
    simpa using Real.hasDerivAt_mul_log (by simpa using hx : x + 0 ≠ 0)
  simpa using hmul.comp 0 hlin

theorem hasDerivAt_const_add_mul (C L : ℝ) :
    HasDerivAt (fun t : ℝ => C + t * L) L 0 := by
  have h : HasDerivAt (fun t : ℝ => t * L) (1 * L) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).mul_const L
  simpa using h.const_add C

theorem hasDerivAt_neg_const_add_mul (C L : ℝ) :
    HasDerivAt (fun t : ℝ => -(C + t * L)) (-L) 0 := by
  simpa using (hasDerivAt_const_add_mul C L).neg

theorem scaled_mul_log_div_scaled
    {a x t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (a * x) * Real.log ((a * x) / (a * t)) =
      a * (x * Real.log (x / t)) := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  have hratio : (a * x) / (a * t) = x / t := by
    field_simp [ne_of_gt ha, ne_of_gt ht]
    ring
  rw [hratio]
  ring

theorem projectEntropyTerm_eq_continuousTerm_on_domain
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) (j : Project nProjects) :
    projectEntropyTerm I b j = projectEntropyContinuousTerm I b j := by
  by_cases hj : projectTotal I b j = 0
  · exact projectEntropyTerm_eq_continuousTerm_of_projectTotal_eq_zero I hb hj
  · have htotal_nonneg := projectTotal_nonneg I hb j
    have htotal_pos : 0 < projectTotal I b j :=
      lt_of_le_of_ne htotal_nonneg (Ne.symm hj)
    unfold projectEntropyTerm projectEntropyContinuousTerm
    simp [hj]
    calc
      (∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            b e * Real.log (b e / projectTotal I b j)
          else 0)
          = ∑ e : I.PositiveEdge,
              ((if edgeProject e.1 = j then b e * Real.log (b e) else 0) -
                (if edgeProject e.1 = j then b e else 0) *
                  Real.log (projectTotal I b j)) := by
            apply Finset.sum_congr rfl
            intro e _he
            by_cases heq : edgeProject e.1 = j
            · simp [heq, mul_log_div_eq_mul_log_sub (hb e) htotal_pos]
            · simp [heq]
      _ = (∑ e : I.PositiveEdge,
              if edgeProject e.1 = j then b e * Real.log (b e) else 0) -
            (∑ e : I.PositiveEdge,
              if edgeProject e.1 = j then b e else 0) *
                Real.log (projectTotal I b j) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.sum_mul]
      _ = (∑ e : I.PositiveEdge,
              if edgeProject e.1 = j then b e * Real.log (b e) else 0) -
            projectTotal I b j * Real.log (projectTotal I b j) := by
            rw [sum_positiveEdges_project_eq_projectTotal I b j]

theorem projectEntropyTerm_smul_of_nonneg
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {r : ℝ} (hr : 0 <= r)
    (j : Project nProjects) :
    projectEntropyTerm I (r • b) j = r * projectEntropyTerm I b j := by
  by_cases hrzero : r = 0
  · simp [hrzero, projectEntropyTerm_eq_zero_of_projectTotal_eq_zero,
      projectTotal_smul]
    have hzero : projectTotal I (0 : Contribution I) j = 0 := by
      unfold projectTotal contributionAt
      simp
    exact projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hzero
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
  by_cases hj : projectTotal I b j = 0
  · have hscaled : projectTotal I (r • b) j = 0 := by
      rw [projectTotal_smul, hj, mul_zero]
    rw [projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hscaled,
      projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hj, mul_zero]
  · have htotal_nonneg := projectTotal_nonneg I hb j
    have htotal_pos : 0 < projectTotal I b j :=
      lt_of_le_of_ne htotal_nonneg (Ne.symm hj)
    have hscaled_ne : projectTotal I (r • b) j ≠ 0 := by
      rw [projectTotal_smul]
      exact mul_ne_zero (ne_of_gt hrpos) (ne_of_gt htotal_pos)
    have hratio :
        ∀ e : I.PositiveEdge,
          edgeProject e.1 = j ->
            (r * b e) / (r * projectTotal I b j) =
              b e / projectTotal I b j := by
      intro e _he
      field_simp [ne_of_gt hrpos, ne_of_gt htotal_pos]
      ring
    unfold projectEntropyTerm
    simp [hscaled_ne, hj, projectTotal_smul, Pi.smul_apply, smul_eq_mul, hrzero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases heq : edgeProject e.1 = j
    · rw [if_pos heq, if_pos heq, hratio e heq]
      ring
    · simp [heq]

theorem projectEntropyTerm_convex_positive_totals
    (I : CappedInstance nAgents nProjects) (j : Project nProjects)
    {b c : Contribution I}
    (hb : contributionNonnegative I b) (hc : contributionNonnegative I c)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hbtotal : 0 < projectTotal I b j)
    (hctotal : 0 < projectTotal I c j) :
    projectEntropyTerm I (a • b + d • c) j <=
      a * projectEntropyTerm I b j + d * projectEntropyTerm I c j := by
  have hcombo_total :
      projectTotal I (a • b + d • c) j =
        a * projectTotal I b j + d * projectTotal I c j := by
    rw [projectTotal_add, projectTotal_smul, projectTotal_smul]
  have hcombo_pos :
      0 < projectTotal I (a • b + d • c) j := by
    rw [hcombo_total]
    exact add_pos (mul_pos ha hbtotal) (mul_pos hd hctotal)
  have hcombo_rhs_ne :
      a * projectTotal I b j + d * projectTotal I c j ≠ 0 :=
    ne_of_gt (add_pos (mul_pos ha hbtotal) (mul_pos hd hctotal))
  have hcombo_ne : projectTotal I (a • b + d • c) j ≠ 0 :=
    ne_of_gt hcombo_pos
  have hbne : projectTotal I b j ≠ 0 := ne_of_gt hbtotal
  have hcne : projectTotal I c j ≠ 0 := ne_of_gt hctotal
  unfold projectEntropyTerm
  simp [hcombo_ne, hbne, hcne, hcombo_total, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hcombo_rhs_ne]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _he
  by_cases heq : edgeProject e.1 = j
  · rw [if_pos heq, if_pos heq, if_pos heq]
    have hbe : 0 <= b e := hb e
    have hce : 0 <= c e := hc e
    have hx₁ : 0 <= a * b e := mul_nonneg ha.le hbe
    have hx₂ : 0 <= d * c e := mul_nonneg hd.le hce
    have hy₁ : 0 < a * projectTotal I b j := mul_pos ha hbtotal
    have hy₂ : 0 < d * projectTotal I c j := mul_pos hd hctotal
    have hlogsum := binary_log_sum_inequality
      (x₁ := a * b e) (x₂ := d * c e)
      (y₁ := a * projectTotal I b j)
      (y₂ := d * projectTotal I c j)
      hx₁ hx₂ hy₁ hy₂
    have hscale_b := scaled_mul_log_div_scaled
      (a := a) (x := b e) (t := projectTotal I b j)
      ha hbtotal
    have hscale_c := scaled_mul_log_div_scaled
      (a := d) (x := c e) (t := projectTotal I c j)
      hd hctotal
    simpa [hscale_b, hscale_c, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_left_comm, mul_comm] using hlogsum
  · simp [heq]

/-- Negative of the capped Shmyrev objective, stated as a minimization
objective for KKT. -/
def shmyrevObjective (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : ℝ :=
  - (∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
    ∑ j : Project nProjects, projectEntropyTerm I b j

def shmyrevOptimal (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : Prop :=
  shmyrevFeasible I b ∧
    ∀ b', shmyrevFeasible I b' -> shmyrevObjective I b <= shmyrevObjective I b'

theorem shmyrevObjective_eq_continuousObjective_on_domain
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) :
    shmyrevObjective I b = shmyrevContinuousObjective I b := by
  unfold shmyrevObjective shmyrevContinuousObjective
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  exact projectEntropyTerm_eq_continuousTerm_on_domain I hb j

theorem projectEntropyTerm_convex_on_domain
    (I : CappedInstance nAgents nProjects) (j : Project nProjects) :
    ∀ b, contributionNonnegative I b ->
      ∀ c, contributionNonnegative I c ->
        ∀ a d : ℝ, 0 <= a -> 0 <= d -> a + d = 1 ->
          projectEntropyTerm I (a • b + d • c) j <=
            a * projectEntropyTerm I b j + d * projectEntropyTerm I c j := by
  intro b hb c hc a d ha hd had
  by_cases ha0 : a = 0
  · have hd1 : d = 1 := by linarith
    simp [ha0, hd1]
  by_cases hd0 : d = 0
  · have ha1 : a = 1 := by linarith
    simp [hd0, ha1]
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  by_cases hbzero : projectTotal I b j = 0
  · have hcongr :
        projectEntropyTerm I (a • b + d • c) j =
          projectEntropyTerm I (d • c) j := by
      apply projectEntropyTerm_congr_project I
      intro e he
      have hb_e := contribution_eq_zero_of_projectTotal_eq_zero
        I hb hbzero (e := e) he
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb_e]
    rw [hcongr, projectEntropyTerm_smul_of_nonneg I hc hd j,
      projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hbzero]
    nlinarith
  by_cases hczero : projectTotal I c j = 0
  · have hcongr :
        projectEntropyTerm I (a • b + d • c) j =
          projectEntropyTerm I (a • b) j := by
      apply projectEntropyTerm_congr_project I
      intro e he
      have hc_e := contribution_eq_zero_of_projectTotal_eq_zero
        I hc hczero (e := e) he
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc_e]
    rw [hcongr, projectEntropyTerm_smul_of_nonneg I hb ha j,
      projectEntropyTerm_eq_zero_of_projectTotal_eq_zero I hczero]
    nlinarith
  have hbtotal : 0 < projectTotal I b j :=
    lt_of_le_of_ne (projectTotal_nonneg I hb j) (Ne.symm hbzero)
  have hctotal : 0 < projectTotal I c j :=
    lt_of_le_of_ne (projectTotal_nonneg I hc j) (Ne.symm hczero)
  exact projectEntropyTerm_convex_positive_totals I j hb hc hapos hdpos
    hbtotal hctotal

def noPartiallyZeroFundedProject (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : Prop :=
  ∀ e : I.PositiveEdge, 0 < projectTotal I b (edgeProject e.1) -> 0 < b e

/-- The paper's subgradient characterization for the negative Shmyrev
objective. -/
def shmyrevSubgradientAt (I : CappedInstance nAgents nProjects)
    (b g : Contribution I) : Prop :=
  noPartiallyZeroFundedProject I b ∧
    (∀ e : I.PositiveEdge,
      0 < projectTotal I b (edgeProject e.1) ->
        g e =
          - Real.log (I.edgeValuation e) +
            Real.log (b e / projectTotal I b (edgeProject e.1))) ∧
    (∀ j : Project nProjects,
      projectTotal I b j = 0 ->
        (∑ i : Agent nAgents,
          if h : (i, j) ∈ I.positiveEdges then
            Real.exp (g ⟨(i, j), h⟩ + Real.log (I.edgeValuation ⟨(i, j), h⟩))
          else 0) <= 1)

def zeroProjectSubgradientTest (I : CappedInstance nAgents nProjects)
    (b g : Contribution I) (j : Project nProjects) : Contribution I :=
  fun e =>
    if edgeProject e.1 = j then
      Real.exp (g e + Real.log (I.edgeValuation e))
    else b e

theorem zeroProjectSubgradientTest_nonnegative
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b) (j : Project nProjects) :
    contributionNonnegative I (zeroProjectSubgradientTest I b g j) := by
  intro e
  unfold zeroProjectSubgradientTest
  by_cases heq : edgeProject e.1 = j
  · simp [heq, (Real.exp_pos _).le]
  · simp [heq, hb e]

theorem zeroProjectSubgradientTest_apply_of_project
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    {j : Project nProjects} {e : I.PositiveEdge}
    (he : edgeProject e.1 = j) :
    zeroProjectSubgradientTest I b g j e =
      Real.exp (g e + Real.log (I.edgeValuation e)) := by
  simp [zeroProjectSubgradientTest, he]

theorem zeroProjectSubgradientTest_apply_of_not_project
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    {j : Project nProjects} {e : I.PositiveEdge}
    (he : edgeProject e.1 ≠ j) :
    zeroProjectSubgradientTest I b g j e = b e := by
  simp [zeroProjectSubgradientTest, he]

theorem projectTotal_zeroProjectSubgradientTest
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    (j : Project nProjects) :
    projectTotal I (zeroProjectSubgradientTest I b g j) j =
      ∑ i : Agent nAgents,
        if h : (i, j) ∈ I.positiveEdges then
          Real.exp (g ⟨(i, j), h⟩ + Real.log (I.edgeValuation ⟨(i, j), h⟩))
        else 0 := by
  unfold projectTotal contributionAt zeroProjectSubgradientTest
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hmem : (i, j) ∈ I.positiveEdges
  · simp [hmem, edgeProject]
  · simp [hmem]

theorem contributionFunctional_zeroProjectSubgradientTest_sub
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) :
    contributionFunctional I g (zeroProjectSubgradientTest I b g j - b) =
      ∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then
          g e * Real.exp (g e + Real.log (I.edgeValuation e))
        else 0 := by
  unfold contributionFunctional
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heq : edgeProject e.1 = j
  · have hbzero := contribution_eq_zero_of_projectTotal_eq_zero
      I hb hj (e := e) heq
    simp [zeroProjectSubgradientTest, heq, hbzero, sub_eq_add_neg]
  · simp [zeroProjectSubgradientTest, heq]

theorem zeroProjectSubgradientTest_projectTotal_nonneg
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    (j : Project nProjects) :
    0 <= projectTotal I (zeroProjectSubgradientTest I b g j) j := by
  rw [projectTotal_zeroProjectSubgradientTest]
  apply Finset.sum_nonneg
  intro i _hi
  by_cases hmem : (i, j) ∈ I.positiveEdges
  · simp [hmem, (Real.exp_pos _).le]
  · simp [hmem]

theorem zeroProjectSubgradientTest_projectTotal_eq_sum_weights
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    (j : Project nProjects) :
    projectTotal I (zeroProjectSubgradientTest I b g j) j =
      ∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then
          Real.exp (g e + Real.log (I.edgeValuation e))
        else 0 := by
  calc
    projectTotal I (zeroProjectSubgradientTest I b g j) j
        =
        ∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            zeroProjectSubgradientTest I b g j e
          else 0 := by
          exact (sum_positiveEdges_project_eq_projectTotal I
            (zeroProjectSubgradientTest I b g j) j).symm
    _ =
      (∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then
          Real.exp (g e + Real.log (I.edgeValuation e))
        else 0) := by
          apply Finset.sum_congr rfl
          intro e _he
          by_cases heq : edgeProject e.1 = j
          · simp [zeroProjectSubgradientTest, heq]
          · simp [heq]

theorem valuationSum_zeroProjectSubgradientTest
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) :
    (∑ e : I.PositiveEdge,
        zeroProjectSubgradientTest I b g j e * Real.log (I.edgeValuation e)) =
      (∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
        ∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            Real.exp (g e + Real.log (I.edgeValuation e)) *
              Real.log (I.edgeValuation e)
          else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heq : edgeProject e.1 = j
  · have hbzero := contribution_eq_zero_of_projectTotal_eq_zero
      I hb hj (e := e) heq
    simp [zeroProjectSubgradientTest, heq, hbzero]
  · simp [zeroProjectSubgradientTest, heq]

theorem projectEntropyContinuousTerm_zeroProjectSubgradientTest_self
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    (j : Project nProjects) :
    projectEntropyContinuousTerm I (zeroProjectSubgradientTest I b g j) j =
      (∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then
          Real.exp (g e + Real.log (I.edgeValuation e)) *
            (g e + Real.log (I.edgeValuation e))
        else 0) -
      projectTotal I (zeroProjectSubgradientTest I b g j) j *
        Real.log (projectTotal I (zeroProjectSubgradientTest I b g j) j) := by
  unfold projectEntropyContinuousTerm
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heq : edgeProject e.1 = j
  · simp [zeroProjectSubgradientTest, heq, Real.log_exp]
  · simp [zeroProjectSubgradientTest, heq]

theorem projectEntropyContinuousTerm_zeroProjectSubgradientTest_ne
    (I : CappedInstance nAgents nProjects) (b g : Contribution I)
    {j k : Project nProjects} (hjk : k ≠ j) :
    projectEntropyContinuousTerm I (zeroProjectSubgradientTest I b g j) k =
      projectEntropyContinuousTerm I b k := by
  unfold projectEntropyContinuousTerm
  have htotal :
      projectTotal I (zeroProjectSubgradientTest I b g j) k =
        projectTotal I b k := by
    apply projectTotal_congr_project I
    intro e he
    have hne : edgeProject e.1 ≠ j := by
      intro h
      exact hjk (he.symm.trans h)
    simp [zeroProjectSubgradientTest, hne]
  rw [htotal]
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hek : edgeProject e.1 = k
  · have hne : edgeProject e.1 ≠ j := by
      intro h
      exact hjk (hek.symm.trans h)
    simp [zeroProjectSubgradientTest, hek, hne, hjk]
  · simp [hek]

theorem projectEntropyContinuousTerm_line_self_eq
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) (t : ℝ) :
    projectEntropyContinuousTerm I (b + t • basisContribution I e) (edgeProject e.1) =
      projectEntropyContinuousTerm I b (edgeProject e.1) +
        ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
        ((projectTotal I b (edgeProject e.1) + t) *
            Real.log (projectTotal I b (edgeProject e.1) + t) -
          projectTotal I b (edgeProject e.1) *
            Real.log (projectTotal I b (edgeProject e.1))) := by
  unfold projectEntropyContinuousTerm
  have hsum :
      (∑ e' : I.PositiveEdge,
        if edgeProject e'.1 = edgeProject e.1 then
          (b + t • basisContribution I e) e' *
            Real.log ((b + t • basisContribution I e) e')
        else 0) =
      (∑ e' : I.PositiveEdge,
        if edgeProject e'.1 = edgeProject e.1 then
          b e' * Real.log (b e')
        else 0) +
        ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) := by
    calc
      (∑ e' : I.PositiveEdge,
        if edgeProject e'.1 = edgeProject e.1 then
          (b + t • basisContribution I e) e' *
            Real.log ((b + t • basisContribution I e) e')
        else 0)
          =
          ∑ e' : I.PositiveEdge,
            ((if edgeProject e'.1 = edgeProject e.1 then
              b e' * Real.log (b e')
            else 0) +
            if e' = e then
              ((b e + t) * Real.log (b e + t) - b e * Real.log (b e))
            else 0) := by
            apply Finset.sum_congr rfl
            intro e' _he'
            by_cases heq : e' = e
            · subst e'
              simp
            · have hline := lineContribution_apply_ne I b heq t
              by_cases hproj : edgeProject e'.1 = edgeProject e.1
              · simp [hproj, heq, hline]
              · simp [hproj, heq]
      _ =
          (∑ e' : I.PositiveEdge,
            if edgeProject e'.1 = edgeProject e.1 then
              b e' * Real.log (b e')
            else 0) +
          ∑ e' : I.PositiveEdge,
            (if e' = e then
              ((b e + t) * Real.log (b e + t) - b e * Real.log (b e))
            else 0) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ e' : I.PositiveEdge,
            if edgeProject e'.1 = edgeProject e.1 then
              b e' * Real.log (b e')
            else 0) +
          ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) := by
            congr 1
            rw [Finset.sum_eq_single e]
            · simp
            · intro e' _he' hne
              simp [hne]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ e))
  rw [hsum, projectTotal_line_self]
  ring

theorem projectEntropyContinuousTerm_line_ne
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) {j : Project nProjects}
    (hne : j ≠ edgeProject e.1) (t : ℝ) :
    projectEntropyContinuousTerm I (b + t • basisContribution I e) j =
      projectEntropyContinuousTerm I b j := by
  unfold projectEntropyContinuousTerm
  rw [projectTotal_line_ne I b e hne t]
  congr 1
  apply Finset.sum_congr rfl
  intro e' _he'
  by_cases hproj : edgeProject e'.1 = j
  · have hne_edge : e' ≠ e := by
      intro heq
      apply hne
      rw [← hproj]
      exact congrArg (fun z : I.PositiveEdge => edgeProject z.1) heq
    rw [lineContribution_apply_ne I b hne_edge t]
  · simp [hproj]

theorem shmyrevContinuousObjective_line_eq
    (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (e : I.PositiveEdge) (t : ℝ) :
    shmyrevContinuousObjective I (b + t • basisContribution I e) =
      shmyrevContinuousObjective I b -
        t * Real.log (I.edgeValuation e) +
        ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
        ((projectTotal I b (edgeProject e.1) + t) *
            Real.log (projectTotal I b (edgeProject e.1) + t) -
          projectTotal I b (edgeProject e.1) *
            Real.log (projectTotal I b (edgeProject e.1))) := by
  unfold shmyrevContinuousObjective
  have hentropy :
      (∑ j : Project nProjects,
        projectEntropyContinuousTerm I (b + t • basisContribution I e) j) =
      (∑ j : Project nProjects, projectEntropyContinuousTerm I b j) +
        (((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
        ((projectTotal I b (edgeProject e.1) + t) *
            Real.log (projectTotal I b (edgeProject e.1) + t) -
          projectTotal I b (edgeProject e.1) *
            Real.log (projectTotal I b (edgeProject e.1)))) := by
    calc
      (∑ j : Project nProjects,
        projectEntropyContinuousTerm I (b + t • basisContribution I e) j)
          =
          ∑ j : Project nProjects,
            (projectEntropyContinuousTerm I b j +
              if j = edgeProject e.1 then
                (((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
                ((projectTotal I b (edgeProject e.1) + t) *
                    Real.log (projectTotal I b (edgeProject e.1) + t) -
                  projectTotal I b (edgeProject e.1) *
                    Real.log (projectTotal I b (edgeProject e.1))))
              else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hj : j = edgeProject e.1
            · subst j
              rw [projectEntropyContinuousTerm_line_self_eq]
              simp only [if_true]
              ring_nf
            · rw [projectEntropyContinuousTerm_line_ne I b e hj t]
              simp [hj]
      _ =
          (∑ j : Project nProjects, projectEntropyContinuousTerm I b j) +
            ∑ j : Project nProjects,
              (if j = edgeProject e.1 then
                (((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
                ((projectTotal I b (edgeProject e.1) + t) *
                    Real.log (projectTotal I b (edgeProject e.1) + t) -
                  projectTotal I b (edgeProject e.1) *
                    Real.log (projectTotal I b (edgeProject e.1))))
              else 0) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ j : Project nProjects, projectEntropyContinuousTerm I b j) +
        (((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
        ((projectTotal I b (edgeProject e.1) + t) *
            Real.log (projectTotal I b (edgeProject e.1) + t) -
          projectTotal I b (edgeProject e.1) *
            Real.log (projectTotal I b (edgeProject e.1)))) := by
            congr 1
            rw [Finset.sum_eq_single (edgeProject e.1)]
            · simp
            · intro j _hj hne
              simp [hne]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ (edgeProject e.1)))
  rw [valuationSum_line, hentropy]
  ring

theorem shmyrevObjective_zeroProjectSubgradientTest_eq
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b) {j : Project nProjects}
    (hj : projectTotal I b j = 0) :
    shmyrevObjective I (zeroProjectSubgradientTest I b g j) =
      shmyrevObjective I b +
        (∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            g e * Real.exp (g e + Real.log (I.edgeValuation e))
          else 0) -
        projectTotal I (zeroProjectSubgradientTest I b g j) j *
          Real.log (projectTotal I (zeroProjectSubgradientTest I b g j) j) := by
  let y : Contribution I := zeroProjectSubgradientTest I b g j
  have hy : contributionNonnegative I y :=
    zeroProjectSubgradientTest_nonnegative I hb j
  have hval :
      (∑ e : I.PositiveEdge, y e * Real.log (I.edgeValuation e)) =
        (∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
          ∑ e : I.PositiveEdge,
            if edgeProject e.1 = j then
              Real.exp (g e + Real.log (I.edgeValuation e)) *
                Real.log (I.edgeValuation e)
            else 0 := by
    simpa [y] using valuationSum_zeroProjectSubgradientTest I hb (g := g) hj
  have hdiff :
      (∑ k : Project nProjects,
        (projectEntropyContinuousTerm I y k -
          projectEntropyContinuousTerm I b k)) =
        (∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            Real.exp (g e + Real.log (I.edgeValuation e)) *
              (g e + Real.log (I.edgeValuation e))
          else 0) -
        projectTotal I y j * Real.log (projectTotal I y j) := by
    rw [Finset.sum_eq_single j]
    · rw [projectEntropyContinuousTerm_zeroProjectSubgradientTest_self]
      rw [projectEntropyContinuousTerm_eq_zero_of_projectTotal_eq_zero I hb hj]
      ring
    · intro k _hk hkj
      rw [projectEntropyContinuousTerm_zeroProjectSubgradientTest_ne I b g hkj,
        sub_self]
    · intro hjnot
      exact False.elim (hjnot (Finset.mem_univ j))
  have hentropy :
      (∑ k : Project nProjects, projectEntropyContinuousTerm I y k) =
        (∑ k : Project nProjects, projectEntropyContinuousTerm I b k) +
          ((∑ e : I.PositiveEdge,
            if edgeProject e.1 = j then
              Real.exp (g e + Real.log (I.edgeValuation e)) *
                (g e + Real.log (I.edgeValuation e))
            else 0) -
          projectTotal I y j * Real.log (projectTotal I y j)) := by
    calc
      (∑ k : Project nProjects, projectEntropyContinuousTerm I y k)
          =
          ∑ k : Project nProjects,
            (projectEntropyContinuousTerm I b k +
              (projectEntropyContinuousTerm I y k -
                projectEntropyContinuousTerm I b k)) := by
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ =
          (∑ k : Project nProjects, projectEntropyContinuousTerm I b k) +
            ∑ k : Project nProjects,
              (projectEntropyContinuousTerm I y k -
                projectEntropyContinuousTerm I b k) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ k : Project nProjects, projectEntropyContinuousTerm I b k) +
          ((∑ e : I.PositiveEdge,
            if edgeProject e.1 = j then
              Real.exp (g e + Real.log (I.edgeValuation e)) *
                (g e + Real.log (I.edgeValuation e))
            else 0) -
          projectTotal I y j * Real.log (projectTotal I y j)) := by
            rw [hdiff]
  have hsplit :
      (∑ e : I.PositiveEdge,
        if edgeProject e.1 = j then
          Real.exp (g e + Real.log (I.edgeValuation e)) *
            (g e + Real.log (I.edgeValuation e))
        else 0) =
        (∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            g e * Real.exp (g e + Real.log (I.edgeValuation e))
          else 0) +
        (∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            Real.exp (g e + Real.log (I.edgeValuation e)) *
              Real.log (I.edgeValuation e)
          else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases heq : edgeProject e.1 = j
    · simp [heq]
      ring
    · simp [heq]
  rw [shmyrevObjective_eq_continuousObjective_on_domain I hy,
    shmyrevObjective_eq_continuousObjective_on_domain I hb]
  unfold shmyrevContinuousObjective
  rw [hval, hentropy, hsplit]
  ring

theorem shmyrevObjective_hasDerivAt_positiveEdge_line
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {e : I.PositiveEdge}
    (hepos : 0 < b e)
    (htotal : 0 < projectTotal I b (edgeProject e.1)) :
    HasDerivAt
      (fun t : ℝ => shmyrevObjective I (b + t • basisContribution I e))
      (- Real.log (I.edgeValuation e) +
        Real.log (b e / projectTotal I b (edgeProject e.1))) 0 := by
  let T := projectTotal I b (edgeProject e.1)
  let L := Real.log (I.edgeValuation e)
  let C := shmyrevContinuousObjective I b
  have hbase :
      HasDerivAt (fun t : ℝ => C - t * L) (-L) 0 := by
    simpa [sub_eq_add_neg] using hasDerivAt_const_add_mul C (-L)
  have hedge :
      HasDerivAt
        (fun t : ℝ => (b e + t) * Real.log (b e + t) -
          b e * Real.log (b e))
        (Real.log (b e) + 1) 0 := by
    exact (hasDerivAt_add_mul_log_line (ne_of_gt hepos)).sub_const _
  have htotal_deriv :
      HasDerivAt
        (fun t : ℝ => (T + t) * Real.log (T + t) -
          T * Real.log T)
        (Real.log T + 1) 0 := by
    exact (hasDerivAt_add_mul_log_line (ne_of_gt (by simpa [T] using htotal))).sub_const _
  have hcombined :
      HasDerivAt
        (fun t : ℝ =>
          (C - t * L) +
            ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
            ((T + t) * Real.log (T + t) - T * Real.log T))
        (-L + (Real.log (b e) + 1) - (Real.log T + 1)) 0 :=
    (hbase.add hedge).sub htotal_deriv
  have hcont :
      HasDerivAt
        (fun t : ℝ => shmyrevContinuousObjective I (b + t • basisContribution I e))
        (-L + (Real.log (b e) + 1) - (Real.log T + 1)) 0 := by
    apply hcombined.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t => by
      change shmyrevContinuousObjective I (b + t • basisContribution I e) =
        C - t * L + ((b e + t) * Real.log (b e + t) - b e * Real.log (b e)) -
          ((T + t) * Real.log (T + t) - T * Real.log T)
      rw [shmyrevContinuousObjective_line_eq]
  have h_event : ∀ᶠ t in 𝓝 (0 : ℝ), -b e < t := by
    exact lt_mem_nhds (by linarith)
  have hobj_eq :
      (fun t : ℝ => shmyrevObjective I (b + t • basisContribution I e)) =ᶠ[𝓝 0]
        (fun t : ℝ => shmyrevContinuousObjective I (b + t • basisContribution I e)) := by
    filter_upwards [h_event] with t ht
    apply shmyrevObjective_eq_continuousObjective_on_domain
    intro e'
    by_cases heq : e' = e
    · subst e'
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I heq]
      simp [hb e']
  have hderiv_obj := hcont.congr_of_eventuallyEq hobj_eq
  have htarget :
      -L + (Real.log (b e) + 1) - (Real.log T + 1) =
        - Real.log (I.edgeValuation e) +
          Real.log (b e / projectTotal I b (edgeProject e.1)) := by
    have hlogdiv :
      Real.log (b e / T) = Real.log (b e) - Real.log T := by
      rw [Real.log_div (ne_of_gt hepos) (ne_of_gt (by simpa [T] using htotal))]
    rw [hlogdiv]
    simp [L, T]
    ring
  exact hderiv_obj.congr_deriv htarget

theorem shmyrevObjective_line_slope_tendsto_atBot_of_zeroEdge
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : contributionNonnegative I b) {e : I.PositiveEdge}
    (hezero : b e = 0)
    (htotal : 0 < projectTotal I b (edgeProject e.1)) :
    Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ * (shmyrevObjective I (b + t • basisContribution I e) -
          shmyrevObjective I b))
      (𝓝[>] (0 : ℝ)) Filter.atBot := by
  let T := projectTotal I b (edgeProject e.1)
  let L := Real.log (I.edgeValuation e)
  have htotal_deriv :
      HasDerivAt
        (fun t : ℝ => (T + t) * Real.log (T + t))
        (Real.log T + 1) 0 := by
    simpa using hasDerivAt_add_mul_log_line (by exact ne_of_gt (by simpa [T] using htotal))
  have htotal_slope :
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ * (((T + t) * Real.log (T + t)) - T * Real.log T))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.log T + 1)) := by
    simpa using htotal_deriv.tendsto_slope_zero_right
  have hfinite :
      Filter.Tendsto
        (fun t : ℝ =>
          -L -
            t⁻¹ * (((T + t) * Real.log (T + t)) - T * Real.log T))
        (𝓝[>] (0 : ℝ)) (𝓝 (-L - (Real.log T + 1))) := by
    exact (tendsto_const_nhds.sub htotal_slope)
  have hlog : Filter.Tendsto Real.log (𝓝[>] (0 : ℝ)) Filter.atBot :=
    Real.tendsto_log_nhdsWithin_zero_right
  have hmodel :
      Filter.Tendsto
        (fun t : ℝ =>
          (-L -
            t⁻¹ * (((T + t) * Real.log (T + t)) - T * Real.log T)) +
            Real.log t)
        (𝓝[>] (0 : ℝ)) Filter.atBot :=
    Filter.Tendsto.add_atBot hfinite hlog
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t htpos_mem
  have htpos : 0 < t := htpos_mem
  have hline_nonneg : contributionNonnegative I (b + t • basisContribution I e) := by
    intro e'
    by_cases heq : e' = e
    · subst e'
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hezero]
      exact le_of_lt htpos
    · rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I heq]
      simp [hb e']
  have hobj_line :=
    shmyrevObjective_eq_continuousObjective_on_domain I hline_nonneg
  have hobj_b := shmyrevObjective_eq_continuousObjective_on_domain I hb
  have hcont_line := shmyrevContinuousObjective_line_eq I b e t
  have htne : t ≠ 0 := ne_of_gt htpos
  rw [hobj_line, hobj_b, hcont_line]
  simp [T, L, hezero, htne, Real.log_mul, Real.log_div]
  field_simp [htne]
  ring

/-- KKT data after applying the finite-dimensional Slater theorem to the
capped Shmyrev program. -/
structure KKTConditions (I : CappedInstance nAgents nProjects)
    (b : Contribution I) where
  g : Contribution I
  lambda : Agent nAgents -> ℝ
  mu : Project nProjects -> ℝ
  eta : I.PositiveEdge -> ℝ
  feasible : shmyrevFeasible I b
  subgradient : shmyrevSubgradientAt I b g
  lambda_nonneg : ∀ i, 0 <= lambda i
  mu_nonneg : ∀ j, 0 <= mu j
  eta_nonneg : ∀ e, 0 <= eta e
  budget_complementary :
    ∀ i, lambda i * (agentSpend I b i - I.budget i) = 0
  cap_complementary :
    ∀ j, mu j * (projectTotal I b j - I.cap j) = 0
  nonneg_complementary :
    ∀ e, eta e * b e = 0
  stationarity :
    ∀ e : I.PositiveEdge,
      g e + lambda (edgeAgent e.1) + mu (edgeProject e.1) - eta e = 0

def kktConditions_of_separated
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    {lambda : Agent nAgents -> ℝ} {mu : Project nProjects -> ℝ}
    {eta : I.PositiveEdge -> ℝ}
    (hfeas : shmyrevFeasible I b)
    (hsub : shmyrevSubgradientAt I b g)
    (hlambda_nonneg : ∀ i, 0 <= lambda i)
    (hmu_nonneg : ∀ j, 0 <= mu j)
    (heta_nonneg : ∀ e, 0 <= eta e)
    (hbudget_comp :
      ∀ i, lambda i * (agentSpend I b i - I.budget i) = 0)
    (hcap_comp :
      ∀ j, mu j * (projectTotal I b j - I.cap j) = 0)
    (hnonneg_comp : ∀ e, eta e * b e = 0)
    (hstat : ∀ z : Contribution I,
      contributionFunctional I g z +
        (∑ i : Agent nAgents, lambda i * agentSpend I z i) +
          (∑ j : Project nProjects, mu j * projectTotal I z j) +
            (∑ e : I.PositiveEdge, eta e * (-(z e))) = 0) :
    KKTConditions I b where
  g := g
  lambda := lambda
  mu := mu
  eta := eta
  feasible := hfeas
  subgradient := hsub
  lambda_nonneg := hlambda_nonneg
  mu_nonneg := hmu_nonneg
  eta_nonneg := heta_nonneg
  budget_complementary := hbudget_comp
  cap_complementary := hcap_comp
  nonneg_complementary := hnonneg_comp
  stationarity := separated_stationarity_coordinate I hstat

def kktConditions_of_abstract
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    {Lambda : ShmyrevKKTConstraint I -> ℝ}
    (hfeas : shmyrevFeasible I b)
    (hsub : shmyrevSubgradientAt I b g)
    (hmult : Optlib.KKT.AffineKKTMultipliers
      (shmyrevKKTConstraintFunctional I) (shmyrevKKTConstraintRhs I) b Lambda)
    (hstat : Optlib.KKT.AffineKKTStationarity
      (shmyrevKKTConstraintFunctional I) (contributionFunctional I g) Lambda) :
    KKTConditions I b :=
  kktConditions_of_separated I
    (b := b) (g := g)
    (lambda := fun i => Lambda (ShmyrevKKTConstraint.budget i))
    (mu := fun j => Lambda (ShmyrevKKTConstraint.cap j))
    (eta := fun e => Lambda (ShmyrevKKTConstraint.nonneg e))
    hfeas hsub
    (fun i => hmult.1 (ShmyrevKKTConstraint.budget i))
    (fun j => hmult.1 (ShmyrevKKTConstraint.cap j))
    (fun e => hmult.1 (ShmyrevKKTConstraint.nonneg e))
    (fun i => by
      simpa [Optlib.KKT.AffineIneqSlack, shmyrevKKTConstraintFunctional,
        shmyrevKKTConstraintRhs] using hmult.2 (ShmyrevKKTConstraint.budget i))
    (fun j => by
      simpa [Optlib.KKT.AffineIneqSlack, shmyrevKKTConstraintFunctional,
        shmyrevKKTConstraintRhs] using hmult.2 (ShmyrevKKTConstraint.cap j))
    (fun e => by
      have h := hmult.2 (ShmyrevKKTConstraint.nonneg e)
      simp [Optlib.KKT.AffineIneqSlack, shmyrevKKTConstraintFunctional,
        shmyrevKKTConstraintRhs] at h
      exact mul_eq_zero.mpr h)
    (fun z => by
      have h := hstat z
      rw [Optlib.KKT.AffineKKTStationarity] at hstat
      rw [multiplierFunctional_shmyrevKKTConstraint I Lambda z] at h
      simpa [add_assoc] using h)

def edgeWeightAtUnfunded (I : CappedInstance nAgents nProjects)
    {b : Contribution I} (K : KKTConditions I b) (e : I.PositiveEdge) : ℝ :=
  Real.exp (K.g e + Real.log (I.edgeValuation e))

def priceOfKKT (I : CappedInstance nAgents nProjects)
    {b : Contribution I} (K : KKTConditions I b) : Prices I :=
  fun i j =>
    if h : (i, j) ∈ I.positiveEdges then
      let e : I.PositiveEdge := ⟨(i, j), h⟩
      if projectTotal I b j = 0 then
        edgeWeightAtUnfunded I K e
      else
        b e / projectTotal I b j
    else 0

theorem allocationOf_feasible_of_shmyrevFeasible
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevFeasible I b) :
    allocationFeasible I (allocationOf I b) := by
  rcases hb with ⟨hb_nonneg, hb_budget, hb_cap⟩
  constructor
  · intro j
    exact ⟨projectTotal_nonneg I hb_nonneg j, hb_cap j⟩
  · calc
      (∑ j : Project nProjects, allocationOf I b j)
          = ∑ j : Project nProjects, projectTotal I b j := rfl
      _ = ∑ i : Agent nAgents, agentSpend I b i :=
          sum_projectTotal_eq_sum_agentSpend I b
      _ <= ∑ i : Agent nAgents, I.budget i := by
          exact Finset.sum_le_sum (fun i _hi => hb_budget i)

theorem shmyrev_objective_convex
    (I : CappedInstance nAgents nProjects) :
    Optlib.DomainSubgradient.ConvexOnDomain
      {b : Contribution I | contributionNonnegative I b}
      (shmyrevObjective I) := by
  refine ⟨contributionNonnegative_convexDomain I, ?_⟩
  intro b hb c hc a d ha hd had
  simp only [Set.mem_setOf_eq] at hb hc
  have hlinear :
      - (∑ e : I.PositiveEdge,
          (a • b + d • c) e * Real.log (I.edgeValuation e)) =
        a * (-(∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e))) +
          d * (-(∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e))) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      - (∑ e : I.PositiveEdge,
          (a * b e + d * c e) * Real.log (I.edgeValuation e))
          =
          - (∑ e : I.PositiveEdge,
            (a * (b e * Real.log (I.edgeValuation e)) +
              d * (c e * Real.log (I.edgeValuation e)))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro e _he
            ring
      _ = - (a * (∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
            d * (∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * (-(∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e))) +
            d * (-(∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e))) := by
            ring
  have hentropy :
      (∑ j : Project nProjects, projectEntropyTerm I (a • b + d • c) j) <=
        ∑ j : Project nProjects,
          (a * projectEntropyTerm I b j + d * projectEntropyTerm I c j) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact projectEntropyTerm_convex_on_domain I j b hb c hc a d ha hd had
  unfold shmyrevObjective
  rw [hlinear]
  calc
    a * (-(∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e))) +
          d * (-(∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e))) +
        ∑ j : Project nProjects, projectEntropyTerm I (a • b + d • c) j
        <=
        a * (-(∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e))) +
          d * (-(∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e))) +
        ∑ j : Project nProjects,
          (a * projectEntropyTerm I b j + d * projectEntropyTerm I c j) := by
          exact add_le_add_left hentropy _
    _ = a *
          (-(∑ e : I.PositiveEdge, b e * Real.log (I.edgeValuation e)) +
            ∑ j : Project nProjects, projectEntropyTerm I b j) +
        d *
          (-(∑ e : I.PositiveEdge, c e * Real.log (I.edgeValuation e)) +
            ∑ j : Project nProjects, projectEntropyTerm I c j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring

theorem shmyrev_objective_continuousOn_domain
    (I : CappedInstance nAgents nProjects) :
    ContinuousOn (shmyrevObjective I)
      {b : Contribution I | contributionNonnegative I b} := by
  refine (shmyrevContinuousObjective_continuous I).continuousOn.congr ?_
  intro b hb
  exact shmyrevObjective_eq_continuousObjective_on_domain I hb

/-- Concrete Slater witness property for the capped Shmyrev program:
strictly positive contributions on every positive-valuation edge, strict
agent-budget slack, and strict project-cap slack. -/
def shmyrev_slater_regular
    (I : CappedInstance nAgents nProjects) :
    Prop :=
  ∃ b : Contribution I,
    (∀ e, 0 < b e) ∧
      (∀ i, agentSpend I b i < I.budget i) ∧
      (∀ j, projectTotal I b j < I.cap j)

private theorem exists_pos_lt_all_of_fintype
    {α : Type*} [Fintype α] (f : α -> ℝ) (hf : ∀ a, 0 < f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, ε < f a := by
  classical
  let P (s : Finset α) : Prop :=
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ s, ε < f a
  have hP_univ : P (Finset.univ : Finset α) := by
    refine Finset.induction_on (Finset.univ : Finset α) ?_ ?_
    · exact ⟨1, by norm_num, by simp⟩
    · intro a s _has ih
      rcases ih with ⟨εs, hεs_pos, hεs⟩
      refine ⟨min (εs / 2) (f a / 2), ?_, ?_⟩
      · exact lt_min (half_pos hεs_pos) (half_pos (hf a))
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hx | hxs
        · rw [hx]
          exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hf a))
        · exact lt_of_le_of_lt (min_le_left _ _)
            (lt_of_lt_of_le (half_lt_self hεs_pos) (hεs x hxs).le)
  rcases hP_univ with ⟨ε, hεpos, hε⟩
  exact ⟨ε, hεpos, fun a => hε a (Finset.mem_univ a)⟩

theorem exists_shmyrev_slater_regular
    (I : CappedInstance nAgents nProjects) :
    shmyrev_slater_regular I := by
  classical
  let denomAgent : ℝ := (Fintype.card (Project nProjects) : ℝ) + 1
  let denomProject : ℝ := (Fintype.card (Agent nAgents) : ℝ) + 1
  have hdenomAgent_pos : 0 < denomAgent := by
    dsimp [denomAgent]
    positivity
  have hdenomProject_pos : 0 < denomProject := by
    dsimp [denomProject]
    positivity
  let bound : Agent nAgents ⊕ Project nProjects -> ℝ
    | Sum.inl i => I.budget i / denomAgent
    | Sum.inr j => I.cap j / denomProject
  have hbound_pos : ∀ k, 0 < bound k := by
    intro k
    cases k with
    | inl i =>
        exact div_pos (I.budget_pos i) hdenomAgent_pos
    | inr j =>
        exact div_pos (I.cap_pos j) hdenomProject_pos
  rcases exists_pos_lt_all_of_fintype bound hbound_pos with ⟨ε, hεpos, hεbound⟩
  refine ⟨fun _e => ε, ?_, ?_, ?_⟩
  · intro _e
    exact hεpos
  · intro i
    have hterm_le : ∀ j : Project nProjects, contributionAt I (fun _e => ε) i j <= ε := by
      intro j
      unfold contributionAt
      by_cases hmem : (i, j) ∈ I.positiveEdges
      · simp [hmem]
      · simp [hmem, le_of_lt hεpos]
    have hsum_le :
        agentSpend I (fun _e => ε) i <=
          (Fintype.card (Project nProjects) : ℝ) * ε := by
      unfold agentSpend
      calc
        (∑ j : Project nProjects, contributionAt I (fun _e => ε) i j)
            <= ∑ _j : Project nProjects, ε := by
              exact Finset.sum_le_sum (fun j _hj => hterm_le j)
        _ = (Fintype.card (Project nProjects) : ℝ) * ε := by
              simp
    have hεi : ε < I.budget i / denomAgent := hεbound (Sum.inl i)
    have hmul_lt : (Fintype.card (Project nProjects) : ℝ) * ε < I.budget i := by
      dsimp [denomAgent] at hεi ⊢
      have hden : 0 < (Fintype.card (Project nProjects) : ℝ) + 1 := by positivity
      rw [lt_div_iff₀ hden] at hεi
      nlinarith [hεpos, hεi]
    exact lt_of_le_of_lt hsum_le hmul_lt
  · intro j
    have hterm_le : ∀ i : Agent nAgents, contributionAt I (fun _e => ε) i j <= ε := by
      intro i
      unfold contributionAt
      by_cases hmem : (i, j) ∈ I.positiveEdges
      · simp [hmem]
      · simp [hmem, le_of_lt hεpos]
    have hsum_le :
        projectTotal I (fun _e => ε) j <=
          (Fintype.card (Agent nAgents) : ℝ) * ε := by
      unfold projectTotal
      calc
        (∑ i : Agent nAgents, contributionAt I (fun _e => ε) i j)
            <= ∑ _i : Agent nAgents, ε := by
              exact Finset.sum_le_sum (fun i _hi => hterm_le i)
        _ = (Fintype.card (Agent nAgents) : ℝ) * ε := by
              simp
    have hεj : ε < I.cap j / denomProject := hεbound (Sum.inr j)
    have hmul_lt : (Fintype.card (Agent nAgents) : ℝ) * ε < I.cap j := by
      dsimp [denomProject] at hεj ⊢
      have hden : 0 < (Fintype.card (Agent nAgents) : ℝ) + 1 := by positivity
      rw [lt_div_iff₀ hden] at hεj
      nlinarith [hεpos, hεj]
    exact lt_of_le_of_lt hsum_le hmul_lt

theorem kkt_positive_project_conclusion
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) {e : I.PositiveEdge}
    (hpos : 0 < projectTotal I b (edgeProject e.1)) :
    I.edgeValuation e
      = Real.exp (K.lambda (edgeAgent e.1) + K.mu (edgeProject e.1)) *
          (b e / projectTotal I b (edgeProject e.1)) := by
  have hbpos : 0 < b e := K.subgradient.1 e hpos
  have hratio_pos : 0 < b e / projectTotal I b (edgeProject e.1) :=
    div_pos hbpos hpos
  have heta_zero : K.eta e = 0 := by
    have hc := K.nonneg_complementary e
    rcases mul_eq_zero.mp hc with heta | hbzero
    · exact heta
    · linarith
  have hg := K.subgradient.2.1 e hpos
  have hs := K.stationarity e
  rw [hg, heta_zero] at hs
  have hlog : Real.log (I.edgeValuation e) =
      Real.log (b e / projectTotal I b (edgeProject e.1)) +
        (K.lambda (edgeAgent e.1) + K.mu (edgeProject e.1)) := by
    linarith
  calc
    I.edgeValuation e = Real.exp (Real.log (I.edgeValuation e)) := by
      rw [Real.exp_log (I.edgeValuation_pos e)]
    _ = Real.exp (Real.log (b e / projectTotal I b (edgeProject e.1)) +
        (K.lambda (edgeAgent e.1) + K.mu (edgeProject e.1))) := by
      rw [hlog]
    _ = Real.exp (K.lambda (edgeAgent e.1) + K.mu (edgeProject e.1)) *
          (b e / projectTotal I b (edgeProject e.1)) := by
      rw [Real.exp_add, Real.exp_log hratio_pos]
      ring

theorem kkt_capped_project_bang_per_buck
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) {e : I.PositiveEdge}
    (_hcap : projectTotal I b (edgeProject e.1) = I.cap (edgeProject e.1))
    (hpos : 0 < projectTotal I b (edgeProject e.1)) :
    Real.exp (K.lambda (edgeAgent e.1)) <=
      I.edgeValuation e / (b e / projectTotal I b (edgeProject e.1)) := by
  have hbpos : 0 < b e := K.subgradient.1 e hpos
  have hratio_pos : 0 < b e / projectTotal I b (edgeProject e.1) :=
    div_pos hbpos hpos
  have hratio_ne : b e / projectTotal I b (edgeProject e.1) ≠ 0 :=
    ne_of_gt hratio_pos
  have hconc := kkt_positive_project_conclusion I K hpos
  have hdiv : I.edgeValuation e / (b e / projectTotal I b (edgeProject e.1)) =
      Real.exp (K.lambda (edgeAgent e.1) + K.mu (edgeProject e.1)) := by
    rw [div_eq_iff hratio_ne]
    exact hconc
  rw [hdiv, Real.exp_le_exp]
  exact le_add_of_nonneg_right (K.mu_nonneg (edgeProject e.1))

theorem kkt_interior_project_bang_per_buck
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) {e : I.PositiveEdge}
    (hpos : 0 < projectTotal I b (edgeProject e.1))
    (hcap : projectTotal I b (edgeProject e.1) < I.cap (edgeProject e.1)) :
    I.edgeValuation e / (b e / projectTotal I b (edgeProject e.1))
      = Real.exp (K.lambda (edgeAgent e.1)) := by
  have hbpos : 0 < b e := K.subgradient.1 e hpos
  have hratio_ne : b e / projectTotal I b (edgeProject e.1) ≠ 0 := by
    exact div_ne_zero (ne_of_gt hbpos) (ne_of_gt hpos)
  have hmu_zero : K.mu (edgeProject e.1) = 0 := by
    have hc := K.cap_complementary (edgeProject e.1)
    rcases mul_eq_zero.mp hc with hmu | hdiff
    · exact hmu
    · linarith
  have hconc := kkt_positive_project_conclusion I K hpos
  rw [hmu_zero, add_zero] at hconc
  rw [div_eq_iff hratio_ne]
  exact hconc

theorem kkt_unfunded_project_bang_per_buck
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) {e : I.PositiveEdge}
    (hunfunded : projectTotal I b (edgeProject e.1) = 0) :
    I.edgeValuation e / edgeWeightAtUnfunded I K e
      <= Real.exp (K.lambda (edgeAgent e.1)) := by
  have hmu_zero : K.mu (edgeProject e.1) = 0 := by
    have hc := K.cap_complementary (edgeProject e.1)
    rcases mul_eq_zero.mp hc with hmu | hdiff
    · exact hmu
    · have hcap_pos := I.cap_pos (edgeProject e.1)
      rw [hunfunded] at hdiff
      linarith
  have hs := K.stationarity e
  rw [hmu_zero] at hs
  have hnonneg : 0 <= K.g e + K.lambda (edgeAgent e.1) := by
    have heta := K.eta_nonneg e
    linarith
  have hle_exp : Real.exp (-K.g e) <= Real.exp (K.lambda (edgeAgent e.1)) := by
    rw [Real.exp_le_exp]
    linarith
  calc
    I.edgeValuation e / edgeWeightAtUnfunded I K e = Real.exp (-K.g e) := by
      unfold edgeWeightAtUnfunded
      rw [Real.exp_add, Real.exp_log (I.edgeValuation_pos e), Real.exp_neg]
      field_simp [Real.exp_ne_zero (K.g e), ne_of_gt (I.edgeValuation_pos e)]
      ring
    _ <= Real.exp (K.lambda (edgeAgent e.1)) := hle_exp

theorem price_zeroRespecting
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) :
    zeroRespecting I (allocationOf I b) (priceOfKKT I K) := by
  intro i j hv0 _hx
  unfold priceOfKKT
  by_cases h : (i, j) ∈ I.positiveEdges
  · have hpos : 0 < I.valuation i j :=
      (I.positiveEdges_iff i j).mp h
    linarith
  · simp [h]

theorem price_nonnegative
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) :
    pricesNonnegative I (priceOfKKT I K) := by
  intro i j
  unfold priceOfKKT
  by_cases h : (i, j) ∈ I.positiveEdges
  · simp [h]
    by_cases htot : projectTotal I b j = 0
    · simp [htot]
      exact (Real.exp_pos _).le
    · simp [htot]
      have hb_nonneg : 0 <= b ⟨(i, j), h⟩ := K.feasible.1 ⟨(i, j), h⟩
      have htotal_nonneg : 0 <= projectTotal I b j :=
        projectTotal_nonneg I K.feasible.1 j
      have htotal_pos : 0 < projectTotal I b j :=
        lt_of_le_of_ne htotal_nonneg (Ne.symm htot)
      exact div_nonneg hb_nonneg (le_of_lt htotal_pos)
  · simp [h]

theorem price_times_allocation_eq_contribution
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) (e : I.PositiveEdge) :
    priceOfKKT I K (edgeAgent e.1) (edgeProject e.1) *
        allocationOf I b (edgeProject e.1) = b e := by
  unfold priceOfKKT allocationOf
  have hmem : (edgeAgent e.1, edgeProject e.1) ∈ I.positiveEdges := by
    simp [edgeAgent, edgeProject, e.2]
  simp [hmem]
  by_cases htot : projectTotal I b (edgeProject e.1) = 0
  · simp [htot]
    exact (contribution_eq_zero_of_projectTotal_eq_zero I K.feasible.1
      htot (e := e) rfl).symm
  · simp [htot]
    have heq : (⟨(edgeAgent e.1, edgeProject e.1), hmem⟩ : I.PositiveEdge) = e := by
      ext <;> simp [edgeAgent, edgeProject]
    rw [heq]

theorem price_times_allocation_eq_contributionAt
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) (i : Agent nAgents) (j : Project nProjects) :
    priceOfKKT I K i j * allocationOf I b j = contributionAt I b i j := by
  unfold contributionAt
  by_cases h : (i, j) ∈ I.positiveEdges
  · simp [h]
    simpa [edgeAgent, edgeProject] using
      price_times_allocation_eq_contribution I K ⟨(i, j), h⟩
  · simp [priceOfKKT, h]

theorem price_profitMaximizing
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) :
    profitMaximizing I (allocationOf I b) (priceOfKKT I K) := by
  intro j
  by_cases htot : projectTotal I b j = 0
  · constructor
    · calc
        (∑ i : Agent nAgents, priceOfKKT I K i j)
            = ∑ i : Agent nAgents,
                if h : (i, j) ∈ I.positiveEdges then
                  Real.exp (K.g ⟨(i, j), h⟩ +
                    Real.log (I.edgeValuation ⟨(i, j), h⟩))
                else 0 := by
              apply Finset.sum_congr rfl
              intro i _hi
              unfold priceOfKKT
              by_cases h : (i, j) ∈ I.positiveEdges
              · simp [h, htot, edgeWeightAtUnfunded]
              · simp [h]
        _ <= 1 := K.subgradient.2.2 j htot
    · intro hxpos
      exfalso
      exact (ne_of_gt hxpos) htot
  · have hsum_eq_one :
        (∑ i : Agent nAgents, priceOfKKT I K i j) = 1 := by
      calc
        (∑ i : Agent nAgents, priceOfKKT I K i j)
            = ∑ i : Agent nAgents, contributionAt I b i j / projectTotal I b j := by
              apply Finset.sum_congr rfl
              intro i _hi
              unfold priceOfKKT contributionAt
              by_cases h : (i, j) ∈ I.positiveEdges
              · simp [h, htot]
              · simp [h]
        _ = (∑ i : Agent nAgents, contributionAt I b i j) / projectTotal I b j := by
              rw [Finset.sum_div]
        _ = 1 := by
              unfold projectTotal
              exact div_self htot
    exact ⟨le_of_eq hsum_eq_one, fun _hxpos => hsum_eq_one⟩

theorem price_affordable
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevFeasible I b) (K : KKTConditions I b) :
    affordable I (allocationOf I b) (priceOfKKT I K) := by
  intro i
  calc
    priceCost I (priceOfKKT I K) i (allocationOf I b)
        = ∑ j : Project nProjects, contributionAt I b i j := by
          unfold priceCost
          apply Finset.sum_congr rfl
          intro j _hj
          exact price_times_allocation_eq_contributionAt I K i j
    _ = agentSpend I b i := rfl
    _ <= I.budget i := hb.2.1 i

theorem priceCost_allocationOf_eq_agentSpend
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) (i : Agent nAgents) :
    priceCost I (priceOfKKT I K) i (allocationOf I b) = agentSpend I b i := by
  calc
    priceCost I (priceOfKKT I K) i (allocationOf I b)
        = ∑ j : Project nProjects, contributionAt I b i j := by
          unfold priceCost
          apply Finset.sum_congr rfl
          intro j _hj
          exact price_times_allocation_eq_contributionAt I K i j
    _ = agentSpend I b i := rfl

theorem underspending_agent_liked_projects_capped
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) {i : Agent nAgents}
    (hunder : agentSpend I b i < I.budget i) :
    ∀ e : I.PositiveEdge, edgeAgent e.1 = i ->
      projectTotal I b (edgeProject e.1) = I.cap (edgeProject e.1) := by
  intro e hei
  by_contra hnotcap
  have hlambda_zero : K.lambda i = 0 := by
    have hc := K.budget_complementary i
    rcases mul_eq_zero.mp hc with hlam | hdiff
    · exact hlam
    · linarith
  have hcap_le := K.feasible.2.2 (edgeProject e.1)
  have hcap_lt : projectTotal I b (edgeProject e.1) < I.cap (edgeProject e.1) :=
    lt_of_le_of_ne hcap_le hnotcap
  have hmu_zero : K.mu (edgeProject e.1) = 0 := by
    have hc := K.cap_complementary (edgeProject e.1)
    rcases mul_eq_zero.mp hc with hmu | hdiff
    · exact hmu
    · linarith
  have hstation := K.stationarity e
  rw [hei, hlambda_zero, hmu_zero] at hstation
  have hg_eq_eta : K.g e = K.eta e := by linarith
  have hg_nonneg : 0 <= K.g e := by
    rw [hg_eq_eta]
    exact K.eta_nonneg e
  have htotal_nonneg := projectTotal_nonneg I K.feasible.1 (edgeProject e.1)
  by_cases hzero : projectTotal I b (edgeProject e.1) = 0
  · have hsum := K.subgradient.2.2 (edgeProject e.1) hzero
    have hterm_le_sum : Real.exp (K.g e + Real.log (I.edgeValuation e)) <=
        ∑ i : Agent nAgents,
          if h : (i, edgeProject e.1) ∈ I.positiveEdges then
            Real.exp (K.g ⟨(i, edgeProject e.1), h⟩ +
              Real.log (I.edgeValuation ⟨(i, edgeProject e.1), h⟩))
          else 0 := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Agent nAgents)), 0 <=
          (if h : (k, edgeProject e.1) ∈ I.positiveEdges then
            Real.exp (K.g ⟨(k, edgeProject e.1), h⟩ +
              Real.log (I.edgeValuation ⟨(k, edgeProject e.1), h⟩)) else 0) := by
        intro k _
        by_cases h : (k, edgeProject e.1) ∈ I.positiveEdges
        · simp [h, (Real.exp_pos _).le]
        · simp [h]
      have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
      have hmem : (i, edgeProject e.1) ∈ I.positiveEdges := by
        simp [← hei, edgeAgent, edgeProject, e.2]
      have heq : (⟨(i, edgeProject e.1), hmem⟩ : I.PositiveEdge) = e := by
        apply Subtype.ext
        exact Prod.ext hei.symm rfl
      simpa [hmem, heq] using hsingle
    have hexp_le_one :
        Real.exp (K.g e + Real.log (I.edgeValuation e)) <= 1 :=
      le_trans hterm_le_sum hsum
    have hgle : K.g e + Real.log (I.edgeValuation e) <= 0 := by
      rw [← Real.exp_zero, Real.exp_le_exp] at hexp_le_one
      exact hexp_le_one
    have hlogpos : 0 < Real.log (I.edgeValuation e) :=
      Real.log_pos (I.edgeValuation_gt_one e)
    linarith
  · have hpos : 0 < projectTotal I b (edgeProject e.1) :=
      lt_of_le_of_ne htotal_nonneg (Ne.symm hzero)
    have hbpos : 0 < b e := K.subgradient.1 e hpos
    have heta_zero : K.eta e = 0 := by
      have hc := K.nonneg_complementary e
      rcases mul_eq_zero.mp hc with heta | hbzero
      · exact heta
      · linarith
    have hg_zero : K.g e = 0 := by
      rw [hg_eq_eta, heta_zero]
    have hg_formula := K.subgradient.2.1 e hpos
    have hble : b e <= projectTotal I b (edgeProject e.1) := by
      have hmem : contributionAt I b (edgeAgent e.1) (edgeProject e.1) = b e := by
        unfold contributionAt
        have hm : (edgeAgent e.1, edgeProject e.1) ∈ I.positiveEdges := by
          simp [edgeAgent, edgeProject, e.2]
        have heq : (⟨(edgeAgent e.1, edgeProject e.1), hm⟩ : I.PositiveEdge) = e := by
          ext <;> simp [edgeAgent, edgeProject]
        simp [hm, heq]
      rw [← hmem]
      exact contributionAt_le_projectTotal I K.feasible.1
        (edgeAgent e.1) (edgeProject e.1)
    have hratio_nonneg : 0 <= b e / projectTotal I b (edgeProject e.1) := by
      positivity
    have hratio_le_one : b e / projectTotal I b (edgeProject e.1) <= 1 :=
      (div_le_one hpos).mpr hble
    have hlog_ratio_nonpos :
        Real.log (b e / projectTotal I b (edgeProject e.1)) <= 0 :=
      Real.log_nonpos hratio_nonneg hratio_le_one
    have hlogpos : 0 < Real.log (I.edgeValuation e) :=
      Real.log_pos (I.edgeValuation_gt_one e)
    rw [hg_zero] at hg_formula
    linarith

theorem utility_term_le_exp_price_term
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (K : KKTConditions I b) (i : Agent nAgents) (j : Project nProjects)
    {y : Allocation I} (hy : 0 <= y j ∧ y j <= I.cap j) :
    I.valuation i j * (y j - allocationOf I b j) <=
      Real.exp (K.lambda i) * priceOfKKT I K i j *
        (y j - allocationOf I b j) := by
  by_cases hcap : allocationOf I b j = I.cap j
  · have hd_nonpos : y j - allocationOf I b j <= 0 := by
      rw [hcap]
      linarith [hy.2]
    by_cases hvzero : I.valuation i j = 0
    · have hpzero : priceOfKKT I K i j = 0 := by
        apply price_zeroRespecting I K i j hvzero
        rw [hcap]
        exact I.cap_pos j
      simp [hvzero, hpzero]
    · have hvpos : 0 < I.valuation i j :=
        lt_of_le_of_ne (I.valuation_nonneg i j) (Ne.symm hvzero)
      have hmem : (i, j) ∈ I.positiveEdges :=
        (I.positiveEdges_iff i j).mpr hvpos
      let e : I.PositiveEdge := ⟨(i, j), hmem⟩
      have htotpos : 0 < projectTotal I b j := by
        rw [allocationOf] at hcap
        rw [hcap]
        exact I.cap_pos j
      have hratio_pos : 0 < b e / projectTotal I b j := by
        exact div_pos (K.subgradient.1 e (by simpa [e, edgeProject] using htotpos)) htotpos
      have hp_eq : priceOfKKT I K i j = b e / projectTotal I b j := by
        unfold priceOfKKT
        simp [hmem, show ¬ projectTotal I b j = 0 from ne_of_gt htotpos, e]
      have hbpb := kkt_capped_project_bang_per_buck I K
        (e := e) (by simpa [allocationOf, e, edgeProject] using hcap)
        (by simpa [e, edgeProject] using htotpos)
      have hbpb' :
          Real.exp (K.lambda i) <=
            I.valuation i j / (b e / projectTotal I b j) := by
        simpa [e, edgeAgent, edgeProject] using hbpb
      have hA_le_v :
          Real.exp (K.lambda i) * priceOfKKT I K i j <= I.valuation i j := by
        rw [hp_eq]
        have hmul := mul_le_mul_of_nonneg_right hbpb' (le_of_lt hratio_pos)
        have hcancel :
            I.valuation i j / (b e / projectTotal I b j) *
              (b e / projectTotal I b j) = I.valuation i j := by
          exact div_mul_cancel₀ _ (ne_of_gt hratio_pos)
        calc
          Real.exp (K.lambda i) * (b e / projectTotal I b j)
              <= I.valuation i j / (b e / projectTotal I b j) *
                    (b e / projectTotal I b j) := hmul
          _ = I.valuation i j := hcancel
      exact mul_le_mul_of_nonpos_right hA_le_v hd_nonpos
  · by_cases hvzero : I.valuation i j = 0
    · have hpzero : priceOfKKT I K i j = 0 := by
        unfold priceOfKKT
        have hnotmem : (i, j) ∉ I.positiveEdges := by
          intro hmem
          have hvpos := (I.positiveEdges_iff i j).mp hmem
          linarith
        simp [hnotmem]
      simp [hvzero, hpzero]
    · have hvpos : 0 < I.valuation i j :=
        lt_of_le_of_ne (I.valuation_nonneg i j) (Ne.symm hvzero)
      have hmem : (i, j) ∈ I.positiveEdges :=
        (I.positiveEdges_iff i j).mpr hvpos
      let e : I.PositiveEdge := ⟨(i, j), hmem⟩
      by_cases htot : projectTotal I b j = 0
      · have hxzero : allocationOf I b j = 0 := by
          simpa [allocationOf] using htot
        have hd_nonneg : 0 <= y j - allocationOf I b j := by
          rw [hxzero]
          simpa using hy.1
        have hp_eq : priceOfKKT I K i j = edgeWeightAtUnfunded I K e := by
          unfold priceOfKKT
          simp [hmem, htot, e]
        have hp_pos : 0 < priceOfKKT I K i j := by
          rw [hp_eq]
          exact Real.exp_pos _
        have hbpb := kkt_unfunded_project_bang_per_buck I K
          (e := e) (by simpa [e, edgeProject] using htot)
        have hbpb' :
            I.valuation i j / edgeWeightAtUnfunded I K e <=
              Real.exp (K.lambda i) := by
          simpa [e, edgeAgent, edgeProject] using hbpb
        have hv_le_A :
            I.valuation i j <= Real.exp (K.lambda i) * priceOfKKT I K i j := by
          rw [hp_eq]
          have hmul := mul_le_mul_of_nonneg_right hbpb'
            (le_of_lt (by rw [hp_eq] at hp_pos; exact hp_pos))
          have hcancel :
              I.valuation i j / edgeWeightAtUnfunded I K e *
                edgeWeightAtUnfunded I K e = I.valuation i j := by
            exact div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos _))
          calc
            I.valuation i j =
                I.valuation i j / edgeWeightAtUnfunded I K e *
                  edgeWeightAtUnfunded I K e := hcancel.symm
            _ <= Real.exp (K.lambda i) * edgeWeightAtUnfunded I K e := hmul
        exact mul_le_mul_of_nonneg_right hv_le_A hd_nonneg
      · have htot_nonneg := projectTotal_nonneg I K.feasible.1 j
        have htotpos : 0 < projectTotal I b j :=
          lt_of_le_of_ne htot_nonneg (Ne.symm htot)
        have hcap_lt : projectTotal I b j < I.cap j := by
          have hcap_le := K.feasible.2.2 j
          have hx_ne : projectTotal I b j ≠ I.cap j := by
            intro hc
            exact hcap (by simpa [allocationOf] using hc)
          exact lt_of_le_of_ne hcap_le hx_ne
        have hp_eq : priceOfKKT I K i j = b e / projectTotal I b j := by
          unfold priceOfKKT
          simp [hmem, htot, e]
        have hbpb := kkt_interior_project_bang_per_buck I K
          (e := e) (by simpa [e, edgeProject] using htotpos)
          (by simpa [e, edgeProject] using hcap_lt)
        have hbpb' :
            I.valuation i j / (b e / projectTotal I b j) =
              Real.exp (K.lambda i) := by
          simpa [e, edgeAgent, edgeProject] using hbpb
        have hv_eq_A :
            I.valuation i j = Real.exp (K.lambda i) * priceOfKKT I K i j := by
          rw [hp_eq]
          have hbpos : 0 < b e := K.subgradient.1 e
            (by simpa [e, edgeProject] using htotpos)
          have hratio_ne : b e / projectTotal I b j ≠ 0 :=
            div_ne_zero (ne_of_gt hbpos) (ne_of_gt htotpos)
          rw [← hbpb']
          field_simp [hratio_ne]
        rw [hv_eq_A]

theorem utilityMaximizing_of_kkt
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevFeasible I b) (K : KKTConditions I b) :
    utilityMaximizing I (allocationOf I b) (priceOfKKT I K) := by
  intro i y hy hbudget
  by_cases hunder : agentSpend I b i < I.budget i
  · unfold utility
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hvzero : I.valuation i j = 0
    · simp [hvzero]
    · have hvpos : 0 < I.valuation i j :=
        lt_of_le_of_ne (I.valuation_nonneg i j) (Ne.symm hvzero)
      have hmem : (i, j) ∈ I.positiveEdges :=
        (I.positiveEdges_iff i j).mpr hvpos
      have hcap : projectTotal I b j = I.cap j :=
        underspending_agent_liked_projects_capped I K hunder ⟨(i, j), hmem⟩ rfl
      apply mul_le_mul_of_nonneg_left _ (I.valuation_nonneg i j)
      rw [allocationOf, hcap]
      exact (hy j).2
  · have hspend_eq_budget : agentSpend I b i = I.budget i := by
      exact le_antisymm (hb.2.1 i) (not_lt.mp hunder)
    have hcost_x_budget :
        priceCost I (priceOfKKT I K) i (allocationOf I b) = I.budget i := by
      rw [priceCost_allocationOf_eq_agentSpend I K i, hspend_eq_budget]
    have hcost_y_le_x :
        priceCost I (priceOfKKT I K) i y <=
          priceCost I (priceOfKKT I K) i (allocationOf I b) := by
      rw [hcost_x_budget]
      exact hbudget
    have hdiff_le :
        utility I i y - utility I i (allocationOf I b) <=
          Real.exp (K.lambda i) *
            (priceCost I (priceOfKKT I K) i y -
              priceCost I (priceOfKKT I K) i (allocationOf I b)) := by
      calc
        utility I i y - utility I i (allocationOf I b)
            = ∑ j : Project nProjects,
                I.valuation i j * (y j - allocationOf I b j) := by
              unfold utility
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _hj
              ring
        _ <= ∑ j : Project nProjects,
                Real.exp (K.lambda i) * priceOfKKT I K i j *
                  (y j - allocationOf I b j) := by
              apply Finset.sum_le_sum
              intro j _hj
              exact utility_term_le_exp_price_term I K i j (hy j)
        _ = Real.exp (K.lambda i) *
              (priceCost I (priceOfKKT I K) i y -
                priceCost I (priceOfKKT I K) i (allocationOf I b)) := by
              unfold priceCost
              calc
                (∑ j : Project nProjects,
                    Real.exp (K.lambda i) * priceOfKKT I K i j *
                      (y j - allocationOf I b j))
                    = ∑ j : Project nProjects,
                        Real.exp (K.lambda i) *
                          (priceOfKKT I K i j * y j -
                            priceOfKKT I K i j * allocationOf I b j) := by
                      apply Finset.sum_congr rfl
                      intro j _hj
                      ring
                _ = Real.exp (K.lambda i) *
                      ∑ j : Project nProjects,
                        (priceOfKKT I K i j * y j -
                          priceOfKKT I K i j * allocationOf I b j) := by
                      rw [Finset.mul_sum]
                _ = Real.exp (K.lambda i) *
                      ((∑ j : Project nProjects, priceOfKKT I K i j * y j) -
                        ∑ j : Project nProjects,
                          priceOfKKT I K i j * allocationOf I b j) := by
                      rw [Finset.sum_sub_distrib]
    have hright_nonpos :
        Real.exp (K.lambda i) *
            (priceCost I (priceOfKKT I K) i y -
              priceCost I (priceOfKKT I K) i (allocationOf I b)) <= 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact le_of_lt (Real.exp_pos _)
      · exact sub_nonpos.mpr hcost_y_le_x
    linarith

end

end ShmyrevCapped
end Lindahl
end Optlib
