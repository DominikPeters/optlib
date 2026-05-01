/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Data.Fintype.BigOperators
import Optlib.Convex.DomainSubgradient

/-!
# Domain-aware KKT theorem for affine inequalities

This file scaffolds the KKT theorem needed before formalizing the capped
Shmyrev program.  It is intentionally specialized and algebraic:

* a convex domain `D`, used in place of an extended-valued indicator;
* finitely many affine inequalities represented by linear functionals
  `a k : E -> Real` and constants `c k`;
* subgradients and constraint gradients represented as linear functionals.

The file contains definitions and theorem statements with `sorry` proofs.  It
is a proof roadmap, not the completed KKT development.
-/

open BigOperators

namespace Optlib
namespace KKT

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [AddCommGroup E] [Module Real E]
variable {ι : Type*} [Fintype ι]

/-- Normal cone to a set, represented in the algebraic dual. -/
def NormalCone (C : Set E) (x : E) : Set (E -> Real) :=
  {n | x ∈ C ∧ Optlib.DomainSubgradient.IsLinearFunctional n ∧
    ∀ y, y ∈ C -> n (y - x) <= 0}

/-- Feasible set for finitely many affine inequalities `a k x <= c k`. -/
def AffineIneqFeasible (a : ι -> E -> Real) (c : ι -> Real) : Set E :=
  {x | ∀ k, a k x <= c k}

/-- The slack of affine inequality `k` at `x`.
Feasibility is `AffineIneqSlack a c x k <= 0`. -/
def AffineIneqSlack (a : ι -> E -> Real) (c : ι -> Real) (x : E)
    (k : ι) : Real :=
  a k x - c k

/-- Constraint `k` is active at `x`. -/
def AffineIneqActive (a : ι -> E -> Real) (c : ι -> Real) (x : E)
    (k : ι) : Prop :=
  a k x = c k

/-- Feasible set obtained by intersecting a domain with affine inequalities. -/
def DomainAffineFeasible (D : Set E) (a : ι -> E -> Real)
    (c : ι -> Real) : Set E :=
  D ∩ AffineIneqFeasible a c

/-- Strict feasibility relative to the domain.  This is the Slater-like
regularity hypothesis for the affine constraints. -/
def StrictlyFeasibleInDomain (D : Set E) (a : ι -> E -> Real)
    (c : ι -> Real) : Prop :=
  ∃ x0, x0 ∈ D ∧ (∀ k, a k x0 < c k)

/-- A placeholder for the regularity assumptions needed by the KKT theorem.

When proving the theorem, this should be expanded to include the exact
continuity/closedness/interior assumptions required by the separation
argument. -/
def DomainKKTRegularity (D : Set E) (f : E -> Real) (a : ι -> E -> Real)
    (c : ι -> Real) : Prop :=
  Optlib.DomainSubgradient.ConvexDomain D ∧
    Optlib.DomainSubgradient.ConvexOnDomain D f ∧
    (∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k)) ∧
    StrictlyFeasibleInDomain D a c

/-- Multipliers satisfy nonnegativity and complementary slackness. -/
def AffineKKTMultipliers (a : ι -> E -> Real) (c : ι -> Real) (x : E)
    (lambda : ι -> Real) : Prop :=
  (∀ k, 0 <= lambda k) ∧
    ∀ k, lambda k * AffineIneqSlack a c x k = 0

/-- Linear combination of active affine constraint gradients in the algebraic
dual. -/
def multiplierFunctional (a : ι -> E -> Real) (lambda : ι -> Real) :
    E -> Real :=
  fun z => Finset.univ.sum fun k => lambda k * a k z

/-- Stationarity for the domain-aware affine KKT system. -/
def AffineKKTStationarity (a : ι -> E -> Real) (g : E -> Real)
    (lambda : ι -> Real) : Prop :=
  ∀ z, g z + multiplierFunctional a lambda z = 0

theorem mem_domainAffineFeasible {D : Set E} {a : ι -> E -> Real}
    {c : ι -> Real} {x : E} :
    x ∈ DomainAffineFeasible D a c <->
      x ∈ D ∧ ∀ k, a k x <= c k := by
  rfl

theorem affineIneqSlack_nonpos_iff {a : ι -> E -> Real} {c : ι -> Real}
    {x : E} {k : ι} :
    AffineIneqSlack a c x k <= 0 <-> a k x <= c k := by
  sorry

theorem affineIneqActive_iff_slack_eq_zero {a : ι -> E -> Real}
    {c : ι -> Real} {x : E} {k : ι} :
    AffineIneqActive a c x k <-> AffineIneqSlack a c x k = 0 := by
  sorry

/-- Easy direction of the polyhedral normal-cone formula. -/
theorem affineCombination_mem_normalCone {a : ι -> E -> Real} {c : ι -> Real}
    {x : E} {lambda : ι -> Real}
    (ha : ∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k))
    (hx : x ∈ AffineIneqFeasible a c)
    (hlambda : AffineKKTMultipliers a c x lambda) :
    multiplierFunctional a lambda ∈ NormalCone (AffineIneqFeasible a c) x := by
  sorry

/-- Hard direction of the polyhedral normal-cone formula.  This is where the
future proof should use a finite-dimensional Farkas/separation argument. -/
theorem normalCone_affineIneq_exists_multipliers {a : ι -> E -> Real}
    {c : ι -> Real} {x : E} {nrm : E -> Real}
    (ha : ∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k))
    (hx : x ∈ AffineIneqFeasible a c)
    (hnrm : nrm ∈ NormalCone (AffineIneqFeasible a c) x) :
    ∃ lambda : ι -> Real,
      AffineKKTMultipliers a c x lambda ∧
        nrm = multiplierFunctional a lambda := by
  sorry

/-- Domain-aware first-order condition before expanding the normal cone.

This is the analogue of Ruszczynski Theorem 3.33 for a real-valued function on
a domain.  It is the key nonsmooth convex-analysis step. -/
theorem domain_minimum_subgradient_normalCone {D : Set E} {f : E -> Real}
    {a : ι -> E -> Real} {c : ι -> Real} {x : E}
    (hregular : DomainKKTRegularity D f a c)
    (hx : x ∈ DomainAffineFeasible D a c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        (fun z => -g z) ∈ NormalCone (AffineIneqFeasible a c) x := by
  sorry

/-- Final roadmap theorem: KKT multipliers for a convex objective on a domain
with finitely many affine inequalities. -/
theorem exists_kkt_multipliers_domain_affine {D : Set E} {f : E -> Real}
    {a : ι -> E -> Real} {c : ι -> Real} {x : E}
    (hregular : DomainKKTRegularity D f a c)
    (hx : x ∈ DomainAffineFeasible D a c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        ∃ lambda : ι -> Real,
          AffineKKTMultipliers a c x lambda ∧
            AffineKKTStationarity a g lambda := by
  sorry

end

end KKT
end Optlib
