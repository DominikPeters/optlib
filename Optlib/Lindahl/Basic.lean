/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic capped Lindahl model

This file contains the model-level definitions for capped Lindahl economies:
finite agents and projects, valuations, allocations, personalized prices,
feasibility, affordability, utility maximization, profit maximization, and
Lindahl equilibrium.

It intentionally avoids the Shmyrev objective and KKT machinery.
-/

open BigOperators

namespace Optlib
namespace Lindahl
namespace ShmyrevCapped

noncomputable section

set_option linter.unusedSectionVars false

abbrev Agent (nAgents : ℕ) := Fin nAgents
abbrev Project (nProjects : ℕ) := Fin nProjects
abbrev Edge (nAgents nProjects : ℕ) := Agent nAgents × Project nProjects

def edgeAgent {nAgents nProjects : ℕ} (e : Edge nAgents nProjects) :
    Agent nAgents :=
  e.1

def edgeProject {nAgents nProjects : ℕ} (e : Edge nAgents nProjects) :
    Project nProjects :=
  e.2

/-- Data for the capped public-goods instance, with positive-valuation
agent-project pairs exposed as a finite edge set. -/
structure CappedInstance (nAgents nProjects : ℕ) where
  budget : Agent nAgents -> ℝ
  cap : Project nProjects -> ℝ
  valuation : Agent nAgents -> Project nProjects -> ℝ
  positiveEdges : Finset (Edge nAgents nProjects)
  budget_pos : ∀ i, 0 < budget i
  budget_nonneg : ∀ i, 0 <= budget i
  cap_pos : ∀ j, 0 < cap j
  valuation_nonneg : ∀ i j, 0 <= valuation i j
  positiveEdges_iff : ∀ i j, (i, j) ∈ positiveEdges ↔ 0 < valuation i j
  valuation_gt_one_on_positive : ∀ i j, 0 < valuation i j -> 1 < valuation i j
  cap_feasible : (∑ j : Project nProjects, cap j) >=
    ∑ i : Agent nAgents, budget i

namespace CappedInstance

variable {nAgents nProjects : ℕ} (I : CappedInstance nAgents nProjects)

abbrev PositiveEdge := {e : Edge nAgents nProjects // e ∈ I.positiveEdges}

def edgeValuation (e : I.PositiveEdge) : ℝ :=
  I.valuation (edgeAgent e.1) (edgeProject e.1)

theorem edgeValuation_pos (e : I.PositiveEdge) : 0 < I.edgeValuation e := by
  rw [edgeValuation]
  exact (I.positiveEdges_iff (edgeAgent e.1) (edgeProject e.1)).mp e.2

theorem edgeValuation_gt_one (e : I.PositiveEdge) : 1 < I.edgeValuation e := by
  exact I.valuation_gt_one_on_positive _ _ (I.edgeValuation_pos e)

end CappedInstance

variable {nAgents nProjects : ℕ}

abbrev Contribution (I : CappedInstance nAgents nProjects) :=
  I.PositiveEdge -> ℝ

abbrev Allocation (_I : CappedInstance nAgents nProjects) :=
  Project nProjects -> ℝ

abbrev Prices (_I : CappedInstance nAgents nProjects) :=
  Agent nAgents -> Project nProjects -> ℝ

def contributionAt (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (i : Agent nAgents) (j : Project nProjects) : ℝ :=
  if h : (i, j) ∈ I.positiveEdges then b ⟨(i, j), h⟩ else 0

def projectTotal (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (j : Project nProjects) : ℝ :=
  ∑ i : Agent nAgents, contributionAt I b i j

def agentSpend (I : CappedInstance nAgents nProjects) (b : Contribution I)
    (i : Agent nAgents) : ℝ :=
  ∑ j : Project nProjects, contributionAt I b i j

def allocationOf (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : Allocation I :=
  fun j => projectTotal I b j

def utility (I : CappedInstance nAgents nProjects) (i : Agent nAgents)
    (x : Allocation I) : ℝ :=
  ∑ j : Project nProjects, I.valuation i j * x j

def priceCost (I : CappedInstance nAgents nProjects) (p : Prices I)
    (i : Agent nAgents) (x : Allocation I) : ℝ :=
  ∑ j : Project nProjects, p i j * x j

def allocationFeasible (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  (∀ j, 0 <= x j ∧ x j <= I.cap j) ∧
    (∑ j : Project nProjects, x j) <= ∑ i : Agent nAgents, I.budget i

def pricesNonnegative (I : CappedInstance nAgents nProjects)
    (p : Prices I) : Prop :=
  ∀ i j, 0 <= p i j

def affordable (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (p : Prices I) : Prop :=
  ∀ i, priceCost I p i x <= I.budget i

def utilityMaximizing (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (p : Prices I) : Prop :=
  ∀ i y, (∀ j, 0 <= y j ∧ y j <= I.cap j) ->
    priceCost I p i y <= I.budget i ->
      utility I i y <= utility I i x

def profitMaximizing (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (p : Prices I) : Prop :=
  ∀ j,
    (∑ i : Agent nAgents, p i j) <= 1 ∧
      (0 < x j -> (∑ i : Agent nAgents, p i j) = 1)

def zeroRespecting (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (p : Prices I) : Prop :=
  ∀ i j, I.valuation i j = 0 -> 0 < x j -> p i j = 0

def LindahlEquilibrium (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (p : Prices I) : Prop :=
  allocationFeasible I x ∧
    pricesNonnegative I p ∧
    affordable I x p ∧
    utilityMaximizing I x p ∧
    profitMaximizing I x p

theorem contributionAt_add (I : CappedInstance nAgents nProjects)
    (b c : Contribution I) (i : Agent nAgents) (j : Project nProjects) :
    contributionAt I (b + c) i j = contributionAt I b i j + contributionAt I c i j := by
  unfold contributionAt
  by_cases h : (i, j) ∈ I.positiveEdges
  · simp [h]
  · simp [h]

theorem contributionAt_smul (I : CappedInstance nAgents nProjects)
    (r : ℝ) (b : Contribution I) (i : Agent nAgents) (j : Project nProjects) :
    contributionAt I (r • b) i j = r * contributionAt I b i j := by
  unfold contributionAt
  by_cases h : (i, j) ∈ I.positiveEdges
  · simp [h, Pi.smul_apply, smul_eq_mul]
  · simp [h]

theorem agentSpend_add (I : CappedInstance nAgents nProjects)
    (b c : Contribution I) (i : Agent nAgents) :
    agentSpend I (b + c) i = agentSpend I b i + agentSpend I c i := by
  unfold agentSpend
  simp_rw [contributionAt_add]
  rw [Finset.sum_add_distrib]

theorem agentSpend_smul (I : CappedInstance nAgents nProjects)
    (r : ℝ) (b : Contribution I) (i : Agent nAgents) :
    agentSpend I (r • b) i = r * agentSpend I b i := by
  unfold agentSpend
  simp_rw [contributionAt_smul]
  rw [Finset.mul_sum]

theorem projectTotal_add (I : CappedInstance nAgents nProjects)
    (b c : Contribution I) (j : Project nProjects) :
    projectTotal I (b + c) j = projectTotal I b j + projectTotal I c j := by
  unfold projectTotal
  simp_rw [contributionAt_add]
  rw [Finset.sum_add_distrib]

theorem projectTotal_smul (I : CappedInstance nAgents nProjects)
    (r : ℝ) (b : Contribution I) (j : Project nProjects) :
    projectTotal I (r • b) j = r * projectTotal I b j := by
  unfold projectTotal
  simp_rw [contributionAt_smul]
  rw [Finset.mul_sum]

end
end ShmyrevCapped
end Lindahl
end Optlib
