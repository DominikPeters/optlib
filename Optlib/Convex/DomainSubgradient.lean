/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# Domain-aware subgradients

This file records a lightweight subgradient interface for functions that are
intended to be used only on a convex domain.

The values of the subgradient are written as linear functionals `E -> Real`
rather than as inner-product vectors.  This keeps the KKT roadmap independent
of a full Euclidean-space setup; a later proof can specialize these
functionals to coordinate maps or to `fun y => inner g y`.
-/

namespace Optlib
namespace DomainSubgradient

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module Real E]

/-- A bare convexity predicate for a domain.  This mirrors the part of
`Convex Real D` that the KKT roadmap needs. -/
def ConvexDomain (D : Set E) : Prop :=
  ∀ x, x ∈ D -> ∀ y, y ∈ D -> ∀ a b : Real,
    0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y ∈ D

/-- Convexity of a real-valued function on a domain. -/
def ConvexOnDomain (D : Set E) (f : E -> Real) : Prop :=
  ConvexDomain D ∧
    ∀ x, x ∈ D -> ∀ y, y ∈ D -> ∀ a b : Real,
      0 <= a -> 0 <= b -> a + b = 1 ->
        f (a • x + b • y) <= a * f x + b * f y

/-- `x` minimizes `f` over `D`. -/
def MinimizesOn (f : E -> Real) (D : Set E) (x : E) : Prop :=
  x ∈ D ∧ ∀ y, y ∈ D -> f x <= f y

/-- An algebraic linear-functional predicate.

The proof roadmap mostly passes these assumptions around; it does not need a
bundled continuous dual space yet. -/
def IsLinearFunctional (ell : E -> Real) : Prop :=
  (∀ x y, ell (x + y) = ell x + ell y) ∧
    ∀ (a : Real) x, ell (a • x) = a * ell x

/-- A domain-aware subgradient of `f` at `x`. -/
def HasDomainSubgradient (D : Set E) (f : E -> Real) (g : E -> Real)
    (x : E) : Prop :=
  x ∈ D ∧ IsLinearFunctional g ∧
    ∀ y, y ∈ D -> f x + g (y - x) <= f y

/-- The set of all domain-aware subgradients. -/
def DomainSubderiv (D : Set E) (f : E -> Real) (x : E) : Set (E -> Real) :=
  {g | HasDomainSubgradient D f g x}

theorem mem_domainSubderiv {D : Set E} {f : E -> Real} {g : E -> Real}
    {x : E} :
    g ∈ DomainSubderiv D f x <-> HasDomainSubgradient D f g x := by
  rfl

/-- Roadmap lemma: if the zero functional is a domain-aware subgradient, then
`x` minimizes `f` over the domain. -/
theorem minimizesOn_of_zero_mem_domainSubderiv {D : Set E} {f : E -> Real}
    {x : E}
    (hzero : (fun _ : E => 0) ∈ DomainSubderiv D f x) :
    MinimizesOn f D x := by
  rcases hzero with ⟨hx, _hlin, hsub⟩
  refine ⟨hx, ?_⟩
  intro y hy
  have h := hsub y hy
  simpa using h

/-- Roadmap lemma: a minimizer over a domain has the zero functional as a
domain-aware subgradient. -/
theorem zero_mem_domainSubderiv_of_minimizesOn {D : Set E} {f : E -> Real}
    {x : E} (hmin : MinimizesOn f D x) :
    (fun _ : E => 0) ∈ DomainSubderiv D f x := by
  rcases hmin with ⟨hx, hmin⟩
  refine ⟨hx, ?_, ?_⟩
  · constructor <;> simp
  · intro y hy
    simpa using hmin y hy

/-- Roadmap lemma: sum rule for domain-aware subgradients. -/
theorem domainSubderiv_add_mem {D : Set E} {f1 f2 : E -> Real} {x : E}
    {g1 g2 : E -> Real}
    (hg1 : g1 ∈ DomainSubderiv D f1 x)
    (hg2 : g2 ∈ DomainSubderiv D f2 x) :
    (fun z => g1 z + g2 z) ∈
      DomainSubderiv D (fun y => f1 y + f2 y) x := by
  rcases hg1 with ⟨hx, hlin1, hsub1⟩
  rcases hg2 with ⟨_hx, hlin2, hsub2⟩
  refine ⟨hx, ?_, ?_⟩
  · constructor
    · intro u v
      change g1 (u + v) + g2 (u + v) = (g1 u + g2 u) + (g1 v + g2 v)
      rw [hlin1.1 u v, hlin2.1 u v]
      ac_rfl
    · intro a u
      change g1 (a • u) + g2 (a • u) = a * (g1 u + g2 u)
      rw [hlin1.2 a u, hlin2.2 a u]
      exact (mul_add a (g1 u) (g2 u)).symm
  · intro y hy
    have h1 := hsub1 y hy
    have h2 := hsub2 y hy
    calc
      f1 x + f2 x + (g1 (y - x) + g2 (y - x))
          = (f1 x + g1 (y - x)) + (f2 x + g2 (y - x)) := by
            ac_rfl
      _ <= f1 y + f2 y := add_le_add h1 h2

/-- Roadmap lemma: adding a linear functional shifts the domain
subdifferential. -/
theorem domainSubderiv_add_linear_mem {D : Set E} {f : E -> Real} {x : E}
    {g ell : E -> Real}
    (hg : g ∈ DomainSubderiv D f x)
    (hell : IsLinearFunctional ell) :
    (fun z => g z + ell z) ∈ DomainSubderiv D (fun y => f y + ell y) x := by
  rcases hg with ⟨hx, hlin, hsub⟩
  refine ⟨hx, ?_, ?_⟩
  · constructor
    · intro u v
      change g (u + v) + ell (u + v) = (g u + ell u) + (g v + ell v)
      rw [hlin.1 u v, hell.1 u v]
      ac_rfl
    · intro a u
      change g (a • u) + ell (a • u) = a * (g u + ell u)
      rw [hlin.2 a u, hell.2 a u]
      exact (mul_add a (g u) (ell u)).symm
  · intro y hy
    have h := hsub y hy
    have hell_sub : ell (y - x) = ell y + ell (-x) := by
      rw [sub_eq_add_neg]
      exact hell.1 y (-x)
    have hell_neg : ell (-x) = -ell x := by
      have hneg := hell.2 (-1 : Real) x
      simpa using hneg
    change f x + ell x + (g (y - x) + ell (y - x)) <= f y + ell y
    calc
      f x + ell x + (g (y - x) + ell (y - x))
          = (f x + g (y - x)) + (ell x + ell (y - x)) := by
            ac_rfl
      _ = (f x + g (y - x)) + ell y := by
            rw [hell_sub, hell_neg]
            calc
              (f x + g (y - x)) + (ell x + (ell y + -ell x))
                  = (f x + g (y - x)) + ((ell x + -ell x) + ell y) := by
                    ac_rfl
              _ = (f x + g (y - x)) + ell y := by simp
      _ <= f y + ell y := add_le_add_right h (ell y)

end

end DomainSubgradient
end Optlib
