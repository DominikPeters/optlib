/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Optlib.Convex.DomainSubgradient

/-!
# Domain-aware KKT theorem for affine inequalities

This file contains an algebraic KKT assembly theorem for convex minimization on
a domain with finitely many affine inequalities:

* a convex domain `D`, used in place of an extended-valued indicator;
* finitely many affine inequalities represented by linear functionals
  `a k : E -> Real` and constants `c k`;
* subgradients and constraint gradients represented as linear functionals.

The theorem is generic in the ambient module.  Finite-dimensional separation
and Farkas arguments in `ConvexKKTFinite` provide the normal-cone ingredients
needed to instantiate it for Euclidean spaces.
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

/-- The affine normal-cone formula expressed as existence of nonnegative
complementary multipliers. -/
def HasAffineNormalConeMultipliers (a : ι -> E -> Real)
    (c : ι -> Real) : Prop :=
  ∀ {x : E} {nrm : E -> Real},
    (∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k)) ->
    x ∈ AffineIneqFeasible a c ->
    nrm ∈ NormalCone (AffineIneqFeasible a c) x ->
      ∃ lambda : ι -> Real,
        AffineKKTMultipliers a c x lambda ∧
          nrm = multiplierFunctional a lambda

/-- The domain first-order condition before expanding the affine normal cone. -/
def HasDomainMinimumNormalConeCertificate (D : Set E) (f : E -> Real)
    (a : ι -> E -> Real) (c : ι -> Real) : Prop :=
  ∀ {x : E},
    x ∈ DomainAffineFeasible D a c ->
    Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x ->
      ∃ g,
        g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
          (fun z => -g z) ∈ NormalCone (AffineIneqFeasible a c) x

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
  unfold AffineIneqSlack
  exact sub_nonpos

theorem affineIneqActive_iff_slack_eq_zero {a : ι -> E -> Real}
    {c : ι -> Real} {x : E} {k : ι} :
    AffineIneqActive a c x k <-> AffineIneqSlack a c x k = 0 := by
  unfold AffineIneqActive AffineIneqSlack
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

/-- Easy direction of the polyhedral normal-cone formula. -/
theorem affineCombination_mem_normalCone {a : ι -> E -> Real} {c : ι -> Real}
    {x : E} {lambda : ι -> Real}
    (ha : ∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k))
    (hx : x ∈ AffineIneqFeasible a c)
    (hlambda : AffineKKTMultipliers a c x lambda) :
    multiplierFunctional a lambda ∈ NormalCone (AffineIneqFeasible a c) x := by
  refine ⟨hx, ?_, ?_⟩
  · constructor
    · intro u v
      calc
        multiplierFunctional a lambda (u + v)
            = Finset.univ.sum
                (fun k => lambda k * (a k u + a k v)) := by
              unfold multiplierFunctional
              apply Finset.sum_congr rfl
              intro k _hk
              rw [(ha k).1 u v]
        _ = Finset.univ.sum
                (fun k => lambda k * a k u + lambda k * a k v) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [mul_add]
        _ = multiplierFunctional a lambda u + multiplierFunctional a lambda v := by
              unfold multiplierFunctional
              rw [Finset.sum_add_distrib]
    · intro r u
      calc
        multiplierFunctional a lambda (r • u)
            = Finset.univ.sum (fun k => lambda k * (r * a k u)) := by
              unfold multiplierFunctional
              apply Finset.sum_congr rfl
              intro k _hk
              rw [(ha k).2 r u]
        _ = Finset.univ.sum (fun k => r * (lambda k * a k u)) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [← mul_assoc, mul_comm (lambda k) r, mul_assoc]
        _ = r * multiplierFunctional a lambda u := by
              unfold multiplierFunctional
              rw [← Finset.mul_sum]
  · intro y hy
    unfold multiplierFunctional
    apply Finset.sum_nonpos
    intro k _hk
    have hak_neg : a k (-x) = -a k x := by
      have h := (ha k).2 (-1 : Real) x
      simpa using h
    have hak_sub : a k (y - x) = a k y - a k x := by
      rw [sub_eq_add_neg, (ha k).1 y (-x), hak_neg]
      rfl
    have hyle : a k y - c k <= 0 := sub_nonpos.mpr (hy k)
    have hcomp : lambda k * (a k x - c k) = 0 := by
      simpa [AffineIneqSlack] using hlambda.2 k
    have hprod : lambda k * (a k y - c k) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hlambda.1 k) hyle
    calc
      lambda k * a k (y - x)
          = lambda k * (a k y - a k x) := by rw [hak_sub]
      _ = lambda k * (a k y - c k) -
            lambda k * (a k x - c k) := by
            rw [mul_sub, mul_sub, mul_sub]
            abel
      _ = lambda k * (a k y - c k) := by rw [hcomp, sub_zero]
      _ <= 0 := hprod

/-- Expands an affine normal-cone element into nonnegative complementary
multipliers. -/
theorem normalCone_affineIneq_exists_multipliers {a : ι -> E -> Real}
    {c : ι -> Real} {x : E} {nrm : E -> Real}
    (hmultipliers : HasAffineNormalConeMultipliers a c)
    (ha : ∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k))
    (hx : x ∈ AffineIneqFeasible a c)
    (hnrm : nrm ∈ NormalCone (AffineIneqFeasible a c) x) :
    ∃ lambda : ι -> Real,
      AffineKKTMultipliers a c x lambda ∧
        nrm = multiplierFunctional a lambda := by
  exact hmultipliers ha hx hnrm

/-- Domain-aware first-order condition before expanding the normal cone.

This is the analogue of Ruszczynski Theorem 3.33 for a real-valued function on
a domain.  It is the key nonsmooth convex-analysis step. -/
theorem domain_minimum_subgradient_normalCone {D : Set E} {f : E -> Real}
    {a : ι -> E -> Real} {c : ι -> Real} {x : E}
    (hdomain : HasDomainMinimumNormalConeCertificate D f a c)
    (hx : x ∈ DomainAffineFeasible D a c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        (fun z => -g z) ∈ NormalCone (AffineIneqFeasible a c) x := by
  exact hdomain hx hmin

/-- Degenerate domain first-order condition when there are no affine
constraints.  This is the base case of the Slater/separation theorem: a
minimizer on the domain has the zero domain subgradient, and the zero
functional is normal to the unconstrained affine feasible set. -/
theorem domain_minimum_subgradient_normalCone_of_isEmpty
    {D : Set E} {f : E -> Real} {a : ι -> E -> Real} {c : ι -> Real}
    {x : E} [IsEmpty ι]
    (hx : x ∈ DomainAffineFeasible D a c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        (fun z => -g z) ∈ NormalCone (AffineIneqFeasible a c) x := by
  have hminD : Optlib.DomainSubgradient.MinimizesOn f D x := by
    refine ⟨hx.1, ?_⟩
    intro y hy
    exact hmin.2 y ⟨hy, fun k => False.elim (IsEmpty.false k)⟩
  refine ⟨fun _ : E => 0, ?_, ?_⟩
  · exact Optlib.DomainSubgradient.zero_mem_domainSubderiv_of_minimizesOn hminD
  · refine ⟨fun k => False.elim (IsEmpty.false k), ?_, ?_⟩
    · constructor <;> simp
    · intro y _hy
      simp

/-- KKT multipliers for a convex objective on a domain with finitely many
affine inequalities, assembled from the domain first-order condition and the
affine normal-cone multiplier formula. -/
theorem exists_kkt_multipliers_domain_affine {D : Set E} {f : E -> Real}
    {a : ι -> E -> Real} {c : ι -> Real} {x : E}
    (ha : ∀ k, Optlib.DomainSubgradient.IsLinearFunctional (a k))
    (hmultipliers : HasAffineNormalConeMultipliers a c)
    (hdomain : HasDomainMinimumNormalConeCertificate D f a c)
    (hx : x ∈ DomainAffineFeasible D a c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f (DomainAffineFeasible D a c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        ∃ lambda : ι -> Real,
          AffineKKTMultipliers a c x lambda ∧
            AffineKKTStationarity a g lambda := by
  rcases domain_minimum_subgradient_normalCone
      (D := D) (f := f) (a := a) (c := c) (x := x)
      hdomain hx hmin with
      ⟨g, hg, hnormal⟩
  have hxAffine : x ∈ AffineIneqFeasible a c := hx.2
  rcases normalCone_affineIneq_exists_multipliers
      (a := a) (c := c) (x := x) (nrm := fun z => -g z)
      hmultipliers ha hxAffine hnormal with ⟨lambda, hlambda, hrepr⟩
  refine ⟨g, hg, lambda, hlambda, ?_⟩
  intro z
  have hz := congrFun hrepr z
  dsimp [AffineKKTStationarity, multiplierFunctional] at hz ⊢
  rw [← hz]
  exact add_neg_cancel (g z)

end

end KKT
end Optlib
