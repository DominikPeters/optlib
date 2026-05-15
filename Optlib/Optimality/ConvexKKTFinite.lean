/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Optlib.Convex.Farkas
import Optlib.Convex.Subgradient
import Optlib.Optimality.ConvexKKTDomain

/-!
# Finite-dimensional bridge for the domain-aware KKT theorem

`ConvexKKTDomain` states KKT conditions using algebraic linear functionals
`E -> ℝ`.  Optlib's existing Farkas theorem is stated for vectors in
`EuclideanSpace ℝ (Fin n)` and inner products.  This file provides the bridge
definitions and the finite-dimensional separation/Farkas results used to prove
the domain-aware KKT theorem under Slater-style hypotheses.
-/

open BigOperators
open InnerProductSpace

namespace Optlib
namespace KKT

noncomputable section

variable {n : ℕ}

/-- The algebraic functional represented by a Euclidean vector. -/
def innerFunctional (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) -> ℝ :=
  fun z => inner v z

/-- Inner-product functionals are algebraically linear. -/
theorem innerFunctional_isLinear (v : EuclideanSpace ℝ (Fin n)) :
    Optlib.DomainSubgradient.IsLinearFunctional (innerFunctional v) := by
  constructor
  · intro x y
    unfold innerFunctional
    rw [inner_add_right]
  · intro r x
    unfold innerFunctional
    rw [inner_smul_right]

/-- Finite-dimensional Riesz bridge for the lightweight algebraic functional
predicate used in `ConvexKKTDomain`. -/
theorem exists_innerFunctional_eq_of_isLinearFunctional
    (ell : EuclideanSpace ℝ (Fin n) -> ℝ)
    (hell : Optlib.DomainSubgradient.IsLinearFunctional ell) :
    ∃ q : EuclideanSpace ℝ (Fin n), ell = innerFunctional q := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := ell
      map_add' := hell.1
      map_smul' := fun r x => hell.2 r x }
  let q : EuclideanSpace ℝ (Fin n) := ∑ i : Fin n, L (b i) • b i
  refine ⟨q, ?_⟩
  funext z
  have hL :
      L z = ∑ i : Fin n, (b.repr z i) * L (b i) := by
    calc
      L z = L (∑ i : Fin n, (b.repr z i) • b i) := by
        rw [b.sum_repr z]
      _ = ∑ i : Fin n, L ((b.repr z i) • b i) := by
        rw [map_sum]
      _ = ∑ i : Fin n, (b.repr z i) * L (b i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_smul]
        rfl
  have hinner :
      inner (𝕜 := ℝ) q z = ∑ i : Fin n, L (b i) * (b.repr z i) := by
    calc
      inner (𝕜 := ℝ) q z =
          ∑ i : Fin n, inner (𝕜 := ℝ) (L (b i) • b i) z := by
        unfold q
        rw [sum_inner]
      _ = ∑ i : Fin n, L (b i) * (b.repr z i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [real_inner_smul_left, ← b.repr_apply_apply]
  calc
    ell z = L z := rfl
    _ = ∑ i : Fin n, (b.repr z i) * L (b i) := hL
    _ = ∑ i : Fin n, L (b i) * (b.repr z i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [mul_comm]
    _ = inner (𝕜 := ℝ) q z := hinner.symm

/-- Feasible set for vector affine inequalities `inner (a k) x <= c k`. -/
def EuclideanAffineIneqFeasible {ι : Type*}
    (a : ι -> EuclideanSpace ℝ (Fin n)) (c : ι -> ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ k, inner (𝕜 := ℝ) (a k) x <= c k}

/-- The vector presentation of affine inequalities is definitionally the
algebraic presentation using `innerFunctional`. -/
theorem euclideanAffineIneqFeasible_eq {ι : Type*}
    [Fintype ι] (a : ι -> EuclideanSpace ℝ (Fin n)) (c : ι -> ℝ) :
    EuclideanAffineIneqFeasible a c =
      AffineIneqFeasible (fun k => innerFunctional (a k)) c := by
  rfl

/-- Multipliers for vector affine inequalities, expressed through the
algebraic multiplier predicate. -/
def EuclideanAffineKKTMultipliers {ι : Type*} [Fintype ι]
    (a : ι -> EuclideanSpace ℝ (Fin n)) (c : ι -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (lambda : ι -> ℝ) : Prop :=
  AffineKKTMultipliers (fun k => innerFunctional (a k)) c x lambda

/-- Stationarity for vector affine inequalities, expressed in the dual
functional form used by `ConvexKKTDomain`. -/
def EuclideanAffineKKTStationarity {ι : Type*} [Fintype ι]
    (a : ι -> EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) -> ℝ) (lambda : ι -> ℝ) : Prop :=
  AffineKKTStationarity (fun k => innerFunctional (a k)) g lambda

/-- Vector normal cone to vector affine inequalities. -/
def EuclideanNormalCone {ι : Type*} [Fintype ι]
  (a : ι -> EuclideanSpace ℝ (Fin n)) (c : ι -> ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {q | x ∈ EuclideanAffineIneqFeasible a c ∧
    ∀ y, y ∈ EuclideanAffineIneqFeasible a c →
      inner (𝕜 := ℝ) q (y - x) <= 0}

/-- Complementary nonnegative multipliers in vector form. -/
def EuclideanAffineKKTMultipliersVector {ι : Type*} [Fintype ι]
    (a : ι -> EuclideanSpace ℝ (Fin n)) (c : ι -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (lambda : ι -> ℝ) : Prop :=
  (∀ k, 0 <= lambda k) ∧
    ∀ k, lambda k * (inner (𝕜 := ℝ) (a k) x - c k) = 0

/-- Feasible set for the Farkas-native indexing used in
`Optlib.Convex.Farkas`. -/
def EuclideanAffineIneqFeasibleOn (σ : Finset ℕ)
    (a : ℕ -> EuclideanSpace ℝ (Fin n)) (c : ℕ -> ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ k ∈ σ, inner (𝕜 := ℝ) (a k) x <= c k}

/-- Active constraints among a finite set of affine inequalities. -/
def EuclideanAffineActiveSet (σ : Finset ℕ)
    (a : ℕ -> EuclideanSpace ℝ (Fin n)) (c : ℕ -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Finset ℕ :=
  σ.filter fun k => inner (𝕜 := ℝ) (a k) x = c k

theorem mem_euclideanAffineActiveSet {σ : Finset ℕ}
    {a : ℕ -> EuclideanSpace ℝ (Fin n)} {c : ℕ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {k : ℕ} :
    k ∈ EuclideanAffineActiveSet σ a c x ↔
      k ∈ σ ∧ inner (𝕜 := ℝ) (a k) x = c k := by
  unfold EuclideanAffineActiveSet
  simp

theorem euclideanAffineActiveSet_subset {σ : Finset ℕ}
    {a : ℕ -> EuclideanSpace ℝ (Fin n)} {c : ℕ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    EuclideanAffineActiveSet σ a c x ⊆ σ := by
  intro k hk
  exact (mem_euclideanAffineActiveSet.mp hk).1

theorem inactive_strict_slack_of_feasible {σ : Finset ℕ}
    {a : ℕ -> EuclideanSpace ℝ (Fin n)} {c : ℕ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hx : x ∈ EuclideanAffineIneqFeasibleOn σ a c)
    (hkσ : k ∈ σ) (hkinactive : k ∉ EuclideanAffineActiveSet σ a c x) :
    inner (𝕜 := ℝ) (a k) x < c k := by
  have hle := hx k hkσ
  have hne : inner (𝕜 := ℝ) (a k) x ≠ c k := by
    intro heq
    exact hkinactive (mem_euclideanAffineActiveSet.mpr ⟨hkσ, heq⟩)
  exact lt_of_le_of_ne hle hne

private theorem exists_pos_uniform_bound_of_finset
    {α : Type*} (s : Finset α) (P : α -> ℝ -> Prop)
    (h :
      ∀ i ∈ s, ∃ ε : ℝ, 0 < ε ∧
        ∀ δ : ℝ, 0 < δ -> δ <= ε -> P i δ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ -> δ <= ε -> ∀ i ∈ s, P i δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro δ _ _ i hi
      simp at hi
  | @insert i s his ih =>
      have hs :
          ∀ j ∈ s, ∃ ε : ℝ, 0 < ε ∧
            ∀ δ : ℝ, 0 < δ -> δ <= ε -> P j δ := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      rcases ih hs with ⟨εs, hεs_pos, hεs⟩
      rcases h i (Finset.mem_insert_self i s) with ⟨εi, hεi_pos, hεi⟩
      refine ⟨min εs εi, lt_min hεs_pos hεi_pos, ?_⟩
      intro δ hδpos hδle j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hjs
      · exact hεi δ hδpos (le_trans hδle (min_le_right εs εi))
      · exact hεs δ hδpos (le_trans hδle (min_le_left εs εi)) j hjs

/-- Vector normal cone for Farkas-native affine inequalities. -/
def EuclideanNormalConeOn (σ : Finset ℕ)
    (a : ℕ -> EuclideanSpace ℝ (Fin n)) (c : ℕ -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {q | x ∈ EuclideanAffineIneqFeasibleOn σ a c ∧
    ∀ y, y ∈ EuclideanAffineIneqFeasibleOn σ a c →
      inner (𝕜 := ℝ) q (y - x) <= 0}

/-- If `z` points inward or tangent for every active affine constraint, then a
small step from `x` in direction `-z` remains feasible.

This is the finite-slack lemma needed to connect the normal cone inequality to
the Farkas alternative.  The proof should use strict slack on inactive
constraints and finiteness of `σ`. -/
theorem exists_pos_sub_smul_mem_feasibleOn_of_active_nonneg
    {σ : Finset ℕ} {a : ℕ -> EuclideanSpace ℝ (Fin n)} {c : ℕ -> ℝ}
    {x z : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ EuclideanAffineIneqFeasibleOn σ a c)
    (hzactive :
      ∀ k ∈ EuclideanAffineActiveSet σ a c x,
        0 <= inner (𝕜 := ℝ) (a k) z) :
    ∃ ε : ℝ, 0 < ε ∧
      x - ε • z ∈ EuclideanAffineIneqFeasibleOn σ a c := by
  classical
  let P : ℕ -> ℝ -> Prop :=
    fun k δ => inner (𝕜 := ℝ) (a k) (x - δ • z) <= c k
  have h_each :
      ∀ k ∈ σ, ∃ ε : ℝ, 0 < ε ∧
        ∀ δ : ℝ, 0 < δ -> δ <= ε -> P k δ := by
    intro k hkσ
    have hstep (δ : ℝ) :
        inner (𝕜 := ℝ) (a k) (x - δ • z) =
          inner (𝕜 := ℝ) (a k) x -
            δ * inner (𝕜 := ℝ) (a k) z := by
      simp [sub_eq_add_neg, inner_add_right, inner_neg_right, inner_smul_right]
    by_cases hkactive : k ∈ EuclideanAffineActiveSet σ a c x
    · have hx_eq : inner (𝕜 := ℝ) (a k) x = c k :=
        (mem_euclideanAffineActiveSet.mp hkactive).2
      have hz_nonneg : 0 <= inner (𝕜 := ℝ) (a k) z :=
        hzactive k hkactive
      refine ⟨1, by norm_num, ?_⟩
      intro δ hδpos _hδle
      change inner (𝕜 := ℝ) (a k) (x - δ • z) <= c k
      rw [hstep δ, hx_eq]
      have hmul_nonneg : 0 <= δ * inner (𝕜 := ℝ) (a k) z :=
        mul_nonneg (le_of_lt hδpos) hz_nonneg
      linarith
    · have hx_lt : inner (𝕜 := ℝ) (a k) x < c k :=
        inactive_strict_slack_of_feasible hx hkσ hkactive
      by_cases hz_nonneg : 0 <= inner (𝕜 := ℝ) (a k) z
      · refine ⟨1, by norm_num, ?_⟩
        intro δ hδpos _hδle
        change inner (𝕜 := ℝ) (a k) (x - δ • z) <= c k
        rw [hstep δ]
        have hmul_nonneg : 0 <= δ * inner (𝕜 := ℝ) (a k) z :=
          mul_nonneg (le_of_lt hδpos) hz_nonneg
        linarith
      · push_neg at hz_nonneg
        refine ⟨(c k - inner (𝕜 := ℝ) (a k) x) /
            (-(inner (𝕜 := ℝ) (a k) z)), ?_, ?_⟩
        · exact div_pos (sub_pos.mpr hx_lt) (neg_pos.mpr hz_nonneg)
        · intro δ _hδpos hδle
          change inner (𝕜 := ℝ) (a k) (x - δ • z) <= c k
          rw [hstep δ]
          have hden_pos : 0 < -(inner (𝕜 := ℝ) (a k) z) :=
            neg_pos.mpr hz_nonneg
          have hmul_le :
              δ * (-(inner (𝕜 := ℝ) (a k) z)) <=
                c k - inner (𝕜 := ℝ) (a k) x := by
            have h :=
              mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
            have hden_ne : -(inner (𝕜 := ℝ) (a k) z) ≠ 0 :=
              ne_of_gt hden_pos
            rwa [div_mul_cancel₀ _ hden_ne] at h
          nlinarith
  rcases exists_pos_uniform_bound_of_finset σ P h_each with
    ⟨ε, hεpos, hεall⟩
  refine ⟨ε, hεpos, ?_⟩
  intro k hkσ
  exact hεall ε hεpos le_rfl k hkσ

theorem not_exists_active_nonneg_inner_neg_of_mem_normalConeOn
    {σ : Finset ℕ} {a : ℕ -> EuclideanSpace ℝ (Fin n)} {c : ℕ -> ℝ}
    {x q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ EuclideanNormalConeOn σ a c x) :
    ¬ ∃ z : EuclideanSpace ℝ (Fin n),
      (∀ k ∈ EuclideanAffineActiveSet σ a c x,
        0 <= inner (𝕜 := ℝ) (a k) z) ∧
        inner (𝕜 := ℝ) q z < 0 := by
  intro hbad
  rcases hq with ⟨hx, hnormal⟩
  rcases hbad with ⟨z, hzactive, hqz⟩
  rcases exists_pos_sub_smul_mem_feasibleOn_of_active_nonneg
      (σ := σ) (a := a) (c := c) (x := x) (z := z) hx hzactive with
    ⟨ε, hεpos, hεfeas⟩
  have hnormal_step := hnormal (x - ε • z) hεfeas
  have hstep_pos : 0 < inner (𝕜 := ℝ) q ((x - ε • z) - x) := by
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right]
    nlinarith
  exact not_lt_of_ge hnormal_step hstep_pos

/-- Farkas-native hard direction of the affine normal-cone formula.

This version avoids arbitrary finite-type reindexing: constraints are indexed
by a finite set `σ : Finset ℕ`, exactly as in `Optlib.Convex.Farkas`. -/
theorem euclideanNormalConeOn_exists_multipliers
    (σ : Finset ℕ) (a : ℕ -> EuclideanSpace ℝ (Fin n)) (c : ℕ -> ℝ)
    {x q : EuclideanSpace ℝ (Fin n)}
    (_hx : x ∈ EuclideanAffineIneqFeasibleOn σ a c)
    (hq : q ∈ EuclideanNormalConeOn σ a c x) :
    ∃ lambda : σ -> ℝ,
      (∀ k, 0 <= lambda k) ∧
        (∀ k, lambda k * (inner (𝕜 := ℝ) (a k) x - c k) = 0) ∧
        q = Finset.univ.sum fun k : σ => lambda k • a k := by
  classical
  let active := EuclideanAffineActiveSet σ a c x
  have hno :
      ¬ ∃ z : EuclideanSpace ℝ (Fin n),
        (∀ k ∈ active, 0 <= inner (𝕜 := ℝ) (a k) z) ∧
          inner (𝕜 := ℝ) q z < 0 := by
    simpa [active] using
      not_exists_active_nonneg_inner_neg_of_mem_normalConeOn
        (σ := σ) (a := a) (c := c) (x := x) (q := q) hq
  have hF :=
    (Farkas (τ := (∅ : Finset ℕ)) (σ := active)
      (a := fun _ => (0 : EuclideanSpace ℝ (Fin n))) (b := a) (c := q)).mpr
      (by
        intro hbad
        rcases hbad with ⟨z, _hempty, hactive, hqz⟩
        exact hno ⟨z, hactive, hqz⟩)
  rcases hF with ⟨_lam, mu, hmu_nonneg, hq_repr⟩
  let lambda : σ -> ℝ :=
    fun k => if h : k.1 ∈ active then mu ⟨k.1, h⟩ else 0
  refine ⟨lambda, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k.1 ∈ active
    · simp [lambda, hk, hmu_nonneg ⟨k.1, hk⟩]
    · simp [lambda, hk]
  · intro k
    by_cases hk : k.1 ∈ active
    · have hactive_eq :
          inner (𝕜 := ℝ) (a k.1) x = c k.1 := by
        exact (mem_euclideanAffineActiveSet.mp hk).2
      simp [lambda, hk, hactive_eq]
    · simp [lambda, hk]
  · have hsum :
        (Finset.univ.sum fun k : σ => lambda k • a k) =
          Finset.univ.sum fun k : active => mu k • a k := by
      let f : ℕ -> EuclideanSpace ℝ (Fin n) :=
        fun k => if h : k ∈ active then mu ⟨k, h⟩ • a k else 0
      have hleft :
          Finset.univ.sum (fun k : σ => lambda k • a k) = ∑ k in σ, f k := by
        rw [← Finset.sum_attach σ f]
        simp [f, lambda]
      have hmiddle : (∑ k in σ, f k) = ∑ k in active, f k := by
        symm
        apply Finset.sum_subset
        · exact euclideanAffineActiveSet_subset
        · intro k _hkσ hk_not_active
          simp [f, hk_not_active]
      have hright : (∑ k in active, f k) =
          Finset.univ.sum fun k : active => mu k • a k := by
        rw [← Finset.sum_attach active f]
        simp [f]
      exact hleft.trans (hmiddle.trans hright)
    rw [hsum]
    simpa using hq_repr

/-- The algebraic affine-normal-cone multiplier formula, proved from the
Farkas-native vector theorem for constraints indexed by a finite set of natural
labels.

This is the form that can be fed back into `ConvexKKTDomain` when the
constraint index type is a subtype of a `Finset ℕ`. -/
theorem hasAffineNormalConeMultipliers_finsetSubtype
    (σ : Finset ℕ) (a : σ -> EuclideanSpace ℝ (Fin n)) (c : σ -> ℝ) :
    HasAffineNormalConeMultipliers (fun k : σ => innerFunctional (a k)) c := by
  classical
  intro x nrm _ha hx hnrm
  rcases hnrm with ⟨_hx, hnrm_linear, hnrm_normal⟩
  rcases exists_innerFunctional_eq_of_isLinearFunctional nrm hnrm_linear with
    ⟨q, hq_repr⟩
  let aN : ℕ -> EuclideanSpace ℝ (Fin n) :=
    fun k => if h : k ∈ σ then a ⟨k, h⟩ else 0
  let cN : ℕ -> ℝ :=
    fun k => if h : k ∈ σ then c ⟨k, h⟩ else 0
  have hxOn : x ∈ EuclideanAffineIneqFeasibleOn σ aN cN := by
    intro k hk
    simpa [aN, cN, hk, innerFunctional] using hx ⟨k, hk⟩
  have hqOn : q ∈ EuclideanNormalConeOn σ aN cN x := by
    refine ⟨hxOn, ?_⟩
    intro y hy
    have hyAlg :
        y ∈ AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c := by
      intro k
      simpa [aN, cN, k.2, innerFunctional] using hy k.1 k.2
    have hnormal := hnrm_normal y hyAlg
    rw [hq_repr] at hnormal
    simpa [innerFunctional] using hnormal
  rcases euclideanNormalConeOn_exists_multipliers
      (σ := σ) (a := aN) (c := cN) (x := x) (q := q) hxOn hqOn with
    ⟨lambda, hlambda_nonneg, hlambda_comp, hq_sum⟩
  refine ⟨lambda, ?_, ?_⟩
  · refine ⟨hlambda_nonneg, ?_⟩
    intro k
    simpa [AffineIneqSlack, innerFunctional, aN, cN, k.2] using
      hlambda_comp k
  · funext z
    rw [hq_repr]
    unfold innerFunctional multiplierFunctional
    calc
      inner (𝕜 := ℝ) q z =
          inner (𝕜 := ℝ) (Finset.univ.sum fun k : σ => lambda k • aN k) z := by
            rw [hq_sum]
      _ = ∑ k : σ, inner (𝕜 := ℝ) (lambda k • aN k) z := by
            rw [sum_inner]
      _ = ∑ k : σ, lambda k * inner (𝕜 := ℝ) (a k) z := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp [aN, k.2, real_inner_smul_left, Finset.mul_sum, mul_assoc]

/-- Finite-dimensional affine KKT theorem with the affine normal-cone
multiplier formula discharged by Farkas.

This theorem is kept as an assembly layer for callers that already have the
domain-minimum normal-cone condition.  The Slater theorem below proves that
certificate from concrete finite-dimensional hypotheses. -/
theorem exists_kkt_multipliers_domain_affine_finsetSubtype
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)}
    {c : σ -> ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hdomain : HasDomainMinimumNormalConeCertificate D f
      (fun k : σ => innerFunctional (a k)) c)
    (hx : x ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f
        (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        ∃ lambda : σ -> ℝ,
          AffineKKTMultipliers (fun k : σ => innerFunctional (a k)) c x lambda ∧
            AffineKKTStationarity (fun k : σ => innerFunctional (a k)) g lambda := by
  exact exists_kkt_multipliers_domain_affine
    (D := D) (f := f) (a := fun k : σ => innerFunctional (a k)) (c := c) (x := x)
    (fun k => innerFunctional_isLinear (a k))
    (hasAffineNormalConeMultipliers_finsetSubtype σ a c)
    hdomain
    hx hmin

/-- Concrete finite-dimensional Slater-style assumptions replacing the
domain-minimum normal-cone condition in the public Slater theorem.

This is deliberately stronger and more concrete than the lightweight
algebraic assembly theorem: the objective is assumed continuous on the domain,
and the affine constraints satisfy a domain-relative strict feasibility
condition. -/
def EuclideanDomainKKTSlaterRegularity
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) -> ℝ)
    (σ : Finset ℕ) (a : σ -> EuclideanSpace ℝ (Fin n)) (c : σ -> ℝ) :
    Prop :=
  Optlib.DomainSubgradient.ConvexDomain D ∧
    Optlib.DomainSubgradient.ConvexOnDomain D f ∧
    ContinuousOn f D ∧
    ∃ x0, x0 ∈ interior D ∧ (∀ k, innerFunctional (a k) x0 < c k)

theorem strictlyFeasibleInDomain_of_euclideanSlaterRegularity
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c) :
    StrictlyFeasibleInDomain D (fun k : σ => innerFunctional (a k)) c := by
  rcases hregular with ⟨_hD, _hf, _hcont, x0, hx0int, hx0strict⟩
  exact ⟨x0, interior_subset hx0int, hx0strict⟩

theorem convexOn_of_convexOnDomain_euclidean
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    (hf : Optlib.DomainSubgradient.ConvexOnDomain D f) :
    ConvexOn ℝ D f := by
  rcases hf with ⟨hD, hf⟩
  rw [convexOn_iff_forall_pos]
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact hD x hx y hy a b ha hb hab
  · intro x hx y hy a b ha hb hab
    exact hf x hx y hy a b (le_of_lt ha) (le_of_lt hb) hab

theorem continuousOn_interior_of_continuousOn
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    (hcont : ContinuousOn f D) :
    ContinuousOn f (interior D) :=
  hcont.mono interior_subset

theorem exists_subgradient_at_slaterPoint
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c) :
    ∃ x0 ∈ interior D,
      (∀ k, innerFunctional (a k) x0 < c k) ∧
        (SubderivWithinAt f D x0).Nonempty := by
  rcases hregular with ⟨_hD, hf, hcont, x0, hx0int, hx0strict⟩
  refine ⟨x0, hx0int, hx0strict, ?_⟩
  exact SubderivWithinAt.Nonempty
    (hf := convexOn_of_convexOnDomain_euclidean hf)
    (hc := continuousOn_interior_of_continuousOn hcont)
    x0 hx0int

theorem affine_strict_combo_of_slater
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x0 y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hx0strict : ∀ k, innerFunctional (a k) x0 < c k)
    (hyfeas : y ∈ AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c)
    (ht_nonneg : 0 <= t) (ht_lt : t < 1) :
    ∀ k : σ,
      innerFunctional (a k) ((1 - t) • x0 + t • y) < c k := by
  intro k
  have hpos : 0 < 1 - t := sub_pos.mpr ht_lt
  have hx0mul :
      (1 - t) * innerFunctional (a k) x0 < (1 - t) * c k :=
    mul_lt_mul_of_pos_left (hx0strict k) hpos
  have hymul :
      t * innerFunctional (a k) y <= t * c k :=
    mul_le_mul_of_nonneg_left (hyfeas k) ht_nonneg
  have hlin :
      innerFunctional (a k) ((1 - t) • x0 + t • y) =
        (1 - t) * innerFunctional (a k) x0 +
          t * innerFunctional (a k) y := by
    unfold innerFunctional
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  rw [hlin]
  nlinarith

theorem domain_combo_mem_of_convexDomain
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {x0 y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hD : Optlib.DomainSubgradient.ConvexDomain D)
    (hx0 : x0 ∈ D) (hy : y ∈ D)
    (ht_nonneg : 0 <= t) (ht_le : t <= 1) :
    (1 - t) • x0 + t • y ∈ D := by
  exact hD x0 hx0 y hy (1 - t) t (sub_nonneg.mpr ht_le) ht_nonneg (by ring)

theorem domain_strictAffineFeasible_combo_of_slater
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x0 y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hD : Optlib.DomainSubgradient.ConvexDomain D)
    (hx0D : x0 ∈ D)
    (hx0strict : ∀ k, innerFunctional (a k) x0 < c k)
    (hy : y ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c)
    (ht_nonneg : 0 <= t) (ht_lt : t < 1) :
    (1 - t) • x0 + t • y ∈ D ∧
      ∀ k, innerFunctional (a k) ((1 - t) • x0 + t • y) < c k := by
  exact ⟨
    domain_combo_mem_of_convexDomain hD hx0D hy.1 ht_nonneg (le_of_lt ht_lt),
    affine_strict_combo_of_slater hx0strict hy.2 ht_nonneg ht_lt⟩

/-- The open strict epigraph set used in the finite-dimensional separation
proof of the domain/affine KKT sum rule.

It is written in displacement coordinates around the candidate minimizer `x`.
The first coordinate `p.1` represents `y - x`; the point tested in the domain is
`p.1 + x`. -/
def kktSeparationOpenSet
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | p.1 + x ∈ interior D ∧ f (p.1 + x) - f x < p.2}

/-- The affine-constraint side of the separation proof.  The first coordinate
again represents displacement from `x`, while the second coordinate is forced
to be nonpositive. -/
def kktSeparationConstraintSet
    {σ : Finset ℕ} (a : σ -> EuclideanSpace ℝ (Fin n)) (c : σ -> ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | p.1 + x ∈ AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c ∧
    p.2 <= 0}

theorem isOpen_kktSeparationOpenSet
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hcont : ContinuousOn f D) :
    IsOpen (kktSeparationOpenSet D f x) := by
  let s : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (fun p => p.1 + x) ⁻¹' interior D
  have hs : IsOpen s := by
    exact IsOpen.preimage (continuous_fst.add continuous_const) isOpen_interior
  have hcont_s :
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => f (p.1 + x) - f x) s := by
    refine ContinuousOn.sub ?_ continuousOn_const
    exact ContinuousOn.comp
      (continuousOn_interior_of_continuousOn hcont)
      ((continuous_fst.add continuous_const).continuousOn)
      (fun p hp => hp)
  have hopen :
      IsOpen {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p ∈ s ∧ f (p.1 + x) - f x < p.2} := by
    exact ContinuousOn.isOpen_inter_preimage
      (hcont_s.prod continuousOn_snd) hs isOpen_lt_prod
  simpa [kktSeparationOpenSet, s] using hopen

theorem convex_kktSeparationOpenSet
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : Optlib.DomainSubgradient.ConvexOnDomain D f) :
    Convex ℝ (kktSeparationOpenSet D f x) := by
  rw [convex_iff_forall_pos]
  intro p hp q hq α β hα hβ hαβ
  rcases hp with ⟨hpD, hpt⟩
  rcases hq with ⟨hqD, hqt⟩
  have hconvD : Convex ℝ D := (convexOn_of_convexOnDomain_euclidean hf).1
  have hcoord :
      (α • p + β • q).1 + x =
        α • (p.1 + x) + β • (q.1 + x) := by
    calc
      (α • p + β • q).1 + x = α • p.1 + β • q.1 + (α + β) • x := by
        rw [hαβ]
        simp [add_comm, add_left_comm, add_assoc]
      _ = α • (p.1 + x) + β • (q.1 + x) := by
        simp [smul_add, add_smul, add_comm, add_left_comm, add_assoc]
  refine ⟨?_, ?_⟩
  · rw [hcoord]
    have hconvInt : Convex ℝ (interior D) := Convex.interior hconvD
    rw [convex_iff_forall_pos] at hconvInt
    exact hconvInt hpD hqD hα hβ hαβ
  · rw [hcoord]
    change f (α • (p.1 + x) + β • (q.1 + x)) - f x < (α • p + β • q).2
    have hf_le :
        f (α • (p.1 + x) + β • (q.1 + x)) <=
          α * f (p.1 + x) + β * f (q.1 + x) :=
      hf.2 (p.1 + x) (interior_subset hpD) (q.1 + x) (interior_subset hqD)
        α β (le_of_lt hα) (le_of_lt hβ) hαβ
    have hp_scaled : α * (f (p.1 + x) - f x) < α * p.2 :=
      mul_lt_mul_of_pos_left hpt hα
    have hq_scaled : β * (f (q.1 + x) - f x) < β * q.2 :=
      mul_lt_mul_of_pos_left hqt hβ
    simp
    have harg :
        α • p.1 + α • x + (β • q.1 + β • x) =
          α • (p.1 + x) + β • (q.1 + x) := by
      simp [smul_add, add_comm, add_left_comm, add_assoc]
    have hf_le' :
        f (α • p.1 + α • x + (β • q.1 + β • x)) <=
          α * f (p.1 + x) + β * f (q.1 + x) := by
      rw [harg]
      exact hf_le
    have hcombo_rhs :
        α * (f (p.1 + x) - f x) + β * (f (q.1 + x) - f x) =
          α * f (p.1 + x) + β * f (q.1 + x) - f x := by
      calc
        α * (f (p.1 + x) - f x) + β * (f (q.1 + x) - f x)
            = α * f (p.1 + x) + β * f (q.1 + x) - (α + β) * f x := by
              ring
        _ = α * f (p.1 + x) + β * f (q.1 + x) - f x := by
              rw [hαβ, one_mul]
    nlinarith

theorem convex_kktSeparationConstraintSet
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    Convex ℝ (kktSeparationConstraintSet a c x) := by
  intro p hp q hq α β hα hβ hαβ
  rcases hp with ⟨hpP, hpt⟩
  rcases hq with ⟨hqP, hqt⟩
  refine ⟨?_, ?_⟩
  · intro k
    have hcoord :
        (α • p + β • q).1 + x =
          α • (p.1 + x) + β • (q.1 + x) := by
      calc
        (α • p + β • q).1 + x = α • p.1 + β • q.1 + (α + β) • x := by
          rw [hαβ]
          simp [add_comm, add_left_comm, add_assoc]
        _ = α • (p.1 + x) + β • (q.1 + x) := by
          simp [smul_add, add_smul, add_comm, add_left_comm, add_assoc]
    rw [hcoord]
    have hp_le := hpP k
    have hq_le := hqP k
    have hlin :
        innerFunctional (a k) (α • (p.1 + x) + β • (q.1 + x)) =
          α * innerFunctional (a k) (p.1 + x) +
            β * innerFunctional (a k) (q.1 + x) := by
      simp [innerFunctional, inner_add_right, inner_smul_right]
      ring
    change innerFunctional (a k) (α • (p.1 + x) + β • (q.1 + x)) <= c k
    rw [hlin]
    calc
      α * innerFunctional (a k) (p.1 + x) +
          β * innerFunctional (a k) (q.1 + x)
          <= α * c k + β * c k := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hp_le hα)
              (mul_le_mul_of_nonneg_left hq_le hβ)
      _ = c k := by rw [← add_mul, hαβ, one_mul]
  · simp
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hpt,
      mul_nonpos_of_nonneg_of_nonpos hβ hqt]

theorem kktSeparation_sets_disjoint
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x) :
    Disjoint (kktSeparationOpenSet D f x)
      (kktSeparationConstraintSet a c x) := by
  rw [Set.disjoint_iff]
  rintro ⟨u, t⟩ hmem
  rcases hmem with ⟨hopen, hconstraint⟩
  rcases hopen with ⟨huD, hut⟩
  rcases hconstraint with ⟨huP, ht⟩
  have hmin :
      Optlib.DomainSubgradient.MinimizesOn f
        (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) x :=
    Optlib.DomainSubgradient.minimizesOn_of_zero_mem_domainSubderiv hzero
  have hfeas :
      u + x ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c :=
    ⟨interior_subset huD, huP⟩
  have hfx_le : f x <= f (u + x) := hmin.2 (u + x) hfeas
  linarith

theorem exists_kktSeparation_separator
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (r u : ℝ),
      (∀ p ∈ kktSeparationOpenSet D f x, inner v p.1 + r * p.2 < u) ∧
        ∀ p ∈ kktSeparationConstraintSet a c x, u <= inner v p.1 + r * p.2 := by
  rcases hregular with ⟨_hD, hf, hcont, _hslater⟩
  obtain ⟨φ, u, hφ_open, hφ_constraint⟩ :=
    geometric_hahn_banach_open
      (convex_kktSeparationOpenSet (D := D) (f := f) (x := x) hf)
      (isOpen_kktSeparationOpenSet (D := D) (f := f) (x := x) hcont)
      (convex_kktSeparationConstraintSet (a := a) (c := c) (x := x))
      (kktSeparation_sets_disjoint (D := D) (f := f) (a := a) (c := c)
        (x := x) hzero)
  let v : EuclideanSpace ℝ (Fin n) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (ContinuousLinearMap.comp φ
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ))
  let r : ℝ :=
    (toDual ℝ ℝ).symm
      (ContinuousLinearMap.comp φ
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ))
  have hφ_coord :
      ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, φ p = inner v p.1 + r * p.2 := by
    intro p
    have hr_inner : r * p.2 = inner r p.2 := by
      simp [r]
    have hr_apply :
        r * p.2 =
          (ContinuousLinearMap.comp φ
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ)) p.2 := by
      rw [hr_inner]
      simp only [r, toDual_symm_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.inr_apply]
    rw [hr_apply]
    simp [v]
    have hp_decomp :
        (p.1, (0 : ℝ)) + ((0 : EuclideanSpace ℝ (Fin n)), p.2) = p := by
      ext i <;> simp
    nth_rw 1 [← hp_decomp]
    rw [ContinuousLinearMap.map_add]
  refine ⟨v, r, u, ?_, ?_⟩
  · intro p hp
    rw [← hφ_coord p]
    exact hφ_open p hp
  · intro p hp
    rw [← hφ_coord p]
    exact hφ_constraint p hp

theorem smul_sub_add_eq_combo
    {x0 x : EuclideanSpace ℝ (Fin n)} {ε : ℝ} :
    ε • (x0 - x) + x = ε • x0 + (1 - ε) • x := by
  ext i
  simp
  ring

theorem combo_sub_eq_smul_sub
    {x0 x : EuclideanSpace ℝ (Fin n)} {ε : ℝ} :
    (ε • x0 + (1 - ε) • x) - x = ε • (x0 - x) := by
  ext i
  simp
  ring

theorem kktSeparation_separator_r_neg
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x v : EuclideanSpace ℝ (Fin n)} {r u : ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x)
    (hopen :
      ∀ p ∈ kktSeparationOpenSet D f x, inner v p.1 + r * p.2 < u)
    (hconstraint :
      ∀ p ∈ kktSeparationConstraintSet a c x, u <= inner v p.1 + r * p.2) :
    r < 0 := by
  rcases hregular with ⟨_hD, _hf, _hcont, x0, hx0int, hx0strict⟩
  let d : EuclideanSpace ℝ (Fin n) := x0 - x
  let t : ℝ := f x0 - f x + 1
  have hdx : d + x = x0 := by
    simp [d]
  have hmin :
      Optlib.DomainSubgradient.MinimizesOn f
        (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) x :=
    Optlib.DomainSubgradient.minimizesOn_of_zero_mem_domainSubderiv hzero
  have hx0feas :
      x0 ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c := by
    refine ⟨interior_subset hx0int, ?_⟩
    intro k
    exact le_of_lt (hx0strict k)
  have hfx_le : f x <= f x0 := hmin.2 x0 hx0feas
  have ht_pos : 0 < t := by
    simp [t]
    linarith
  have hopen_mem : (d, t) ∈ kktSeparationOpenSet D f x := by
    constructor
    · simpa [hdx] using hx0int
    · simp [t, hdx]
  have hconstraint_mem : (d, 0) ∈ kktSeparationConstraintSet a c x := by
    constructor
    · simpa [hdx] using hx0feas.2
    · simp
  have hlt := hopen (d, t) hopen_mem
  have hle := hconstraint (d, 0) hconstraint_mem
  simp only [Prod.fst, Prod.snd, mul_zero, add_zero] at hlt hle
  have hrt_neg : r * t < 0 := by
    linarith
  by_contra hr_nonneg
  have hr_nonneg : 0 <= r := le_of_not_gt hr_nonneg
  have : 0 <= r * t := mul_nonneg hr_nonneg (le_of_lt ht_pos)
  exact (not_le_of_gt hrt_neg) this

theorem kktSeparation_separator_u_eq_zero
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x v : EuclideanSpace ℝ (Fin n)} {r u : ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hx : x ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c)
    (hopen :
      ∀ p ∈ kktSeparationOpenSet D f x, inner v p.1 + r * p.2 < u)
    (hconstraint :
      ∀ p ∈ kktSeparationConstraintSet a c x, u <= inner v p.1 + r * p.2) :
    u = 0 := by
  rcases hregular with ⟨_hD, hf, _hcont, x0, hx0int, _hx0strict⟩
  have hu_le_zero : u <= 0 := by
    have hmem : ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) ∈
        kktSeparationConstraintSet a c x := by
      constructor
      · simpa using hx.2
      · simp
    have h := hconstraint ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) hmem
    simpa using h
  let d : EuclideanSpace ℝ (Fin n) := x0 - x
  let C : ℝ := f x0 - f x + 1
  let B : ℝ := inner v d + r * C
  have hB_le_u : ∀ m : ℕ, ((1 : ℝ) / (m + 1)) * B <= u := by
    intro m
    let ε : ℝ := (1 : ℝ) / (m + 1)
    have hε_pos : 0 < ε := by
      exact one_div_pos.mpr (by positivity)
    have hε_nonneg : 0 <= ε := le_of_lt hε_pos
    have hε_le_one : ε <= 1 := by
      dsimp [ε]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      norm_num
    let y : EuclideanSpace ℝ (Fin n) := ε • x0 + (1 - ε) • x
    have hy_eq : ε • d + x = y := by
      simp [y, d, smul_sub_add_eq_combo]
    have hyDint : y ∈ interior D := by
      have hconvD : Convex ℝ D := (convexOn_of_convexOnDomain_euclidean hf).1
      have hmem := hconvD.combo_self_interior_mem_interior hx.1 hx0int
        (sub_nonneg.mpr hε_le_one) hε_pos (by ring)
      simpa [y, add_comm] using hmem
    have hyf_le : f y <= ε * f x0 + (1 - ε) * f x := by
      exact hf.2 x0 (interior_subset hx0int) x hx.1
        ε (1 - ε) hε_nonneg (sub_nonneg.mpr hε_le_one) (by ring)
    have hopen_mem : (ε • d, ε * C) ∈ kktSeparationOpenSet D f x := by
      constructor
      · simpa [hy_eq] using hyDint
      · have hy_bound : f (ε • d + x) <= ε * f x0 + (1 - ε) * f x := by
          simpa [hy_eq] using hyf_le
        have hstrict : f (ε • d + x) - f x < ε * C := by
          have hcalc :
              ε * f x0 + (1 - ε) * f x - f x = ε * (f x0 - f x) := by
            ring
          calc
            f (ε • d + x) - f x
                <= ε * f x0 + (1 - ε) * f x - f x :=
                  sub_le_sub_right hy_bound (f x)
            _ = ε * (f x0 - f x) := hcalc
            _ < ε * C := by
              simp [C]
              nlinarith
        exact hstrict
    have hlt := hopen (ε • d, ε * C) hopen_mem
    have hleft :
        inner v (ε • d) + r * (ε * C) = ε * B := by
      simp [B, inner_smul_right, mul_add, mul_assoc]
      ring
    rw [hleft] at hlt
    exact le_of_lt hlt
  have htendsto :
      Filter.Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1)) * B) Filter.atTop (nhds 0) := by
    have hε :
        Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hε.mul tendsto_const_nhds
  have hzero_le_u : 0 <= u := by
    apply le_of_tendsto_of_tendsto' htendsto tendsto_const_nhds hB_le_u
  exact le_antisymm hu_le_zero hzero_le_u

theorem normalized_separator_subgradient_interior
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {x y v : EuclideanSpace ℝ (Fin n)} {r u : ℝ}
    (hy : y ∈ interior D)
    (hr : r < 0)
    (hu : u = 0)
    (hopen :
      ∀ p ∈ kktSeparationOpenSet D f x, inner v p.1 + r * p.2 < u) :
    f x + innerFunctional ((-1 / r) • v) (y - x) <= f y := by
  let A : ℝ := f y - f x
  let I : ℝ := inner v (y - x)
  have hle_zero_seq :
      ∀ m : ℕ, I + r * (A + (1 : ℝ) / (m + 1)) <= 0 := by
    intro m
    have hmem : (y - x, A + (1 : ℝ) / (m + 1)) ∈
        kktSeparationOpenSet D f x := by
      constructor
      · simpa using hy
      · simp [A]
        positivity
    have hlt := hopen (y - x, A + (1 : ℝ) / (m + 1)) hmem
    rw [hu] at hlt
    simpa [I, one_div] using (le_of_lt hlt)
  have htendsto :
      Filter.Tendsto
        (fun m : ℕ => I + r * (A + (1 : ℝ) / (m + 1)))
        Filter.atTop (nhds (I + r * A)) := by
    have hε :
        Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hA :
        Filter.Tendsto (fun m : ℕ => A + (1 : ℝ) / (m + 1)) Filter.atTop
          (nhds (A + 0)) :=
      tendsto_const_nhds.add hε
    have hrA :
        Filter.Tendsto (fun m : ℕ => r * (A + (1 : ℝ) / (m + 1))) Filter.atTop
          (nhds (r * (A + 0))) :=
      tendsto_const_nhds.mul hA
    simpa using tendsto_const_nhds.add hrA
  have hmain : I + r * A <= 0 := by
    apply le_of_tendsto_of_tendsto' htendsto tendsto_const_nhds hle_zero_seq
  have hscale_nonneg : 0 <= -1 / r := by
    exact le_of_lt (div_pos_of_neg_of_neg (by norm_num) hr)
  have hI_le : I <= -r * A := by
    linarith
  have hscaled : (-1 / r) * I <= A := by
    have h := mul_le_mul_of_nonneg_left hI_le hscale_nonneg
    have hcancel : (-1 / r) * (-r * A) = A := by
      field_simp [ne_of_lt hr]
    rw [hcancel] at h
    exact h
  have hinner :
      innerFunctional ((-1 / r) • v) (y - x) <= A := by
    change inner ((-1 / r) • v) (y - x) <= A
    rw [inner_smul_left]
    exact hscaled
  linarith

theorem normalized_separator_mem_normalCone
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x v : EuclideanSpace ℝ (Fin n)} {r u : ℝ}
    (hxP : x ∈ AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c)
    (hr : r < 0)
    (hu : u = 0)
    (hconstraint :
      ∀ p ∈ kktSeparationConstraintSet a c x, u <= inner v p.1 + r * p.2) :
    (fun z => -innerFunctional ((-1 / r) • v) z) ∈
      NormalCone (AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c) x := by
  refine ⟨hxP, ?_, ?_⟩
  · have hlin := innerFunctional_isLinear ((-1 / r) • v)
    constructor
    · intro y z
      change -innerFunctional ((-1 / r) • v) (y + z) =
        -innerFunctional ((-1 / r) • v) y + -innerFunctional ((-1 / r) • v) z
      rw [hlin.1 y z]
      ring
    · intro α z
      change -innerFunctional ((-1 / r) • v) (α • z) =
        α * -innerFunctional ((-1 / r) • v) z
      rw [hlin.2 α z]
      ring
  · intro y hy
    have hmem : (y - x, (0 : ℝ)) ∈ kktSeparationConstraintSet a c x := by
      constructor
      · simpa using hy
      · simp
    have hsep := hconstraint (y - x, (0 : ℝ)) hmem
    rw [hu] at hsep
    simp at hsep
    have hscale_nonneg : 0 <= -1 / r := by
      exact le_of_lt (div_pos_of_neg_of_neg (by norm_num) hr)
    have hg_nonneg :
        0 <= innerFunctional ((-1 / r) • v) (y - x) := by
      change 0 <= inner ((-1 / r) • v) (y - x)
      rw [inner_smul_left]
      exact mul_nonneg hscale_nonneg hsep
    linarith

theorem normalized_separator_domainSubgradient
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x v : EuclideanSpace ℝ (Fin n)} {r u : ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hxD : x ∈ D)
    (hr : r < 0)
    (hu : u = 0)
    (hopen :
      ∀ p ∈ kktSeparationOpenSet D f x, inner v p.1 + r * p.2 < u) :
    innerFunctional ((-1 / r) • v) ∈
      Optlib.DomainSubgradient.DomainSubderiv D f x := by
  rcases hregular with ⟨_hD, hf, _hcont, x0, hx0int, _hx0strict⟩
  refine ⟨hxD, innerFunctional_isLinear ((-1 / r) • v), ?_⟩
  intro y hyD
  by_cases hyint : y ∈ interior D
  · exact normalized_separator_subgradient_interior
      (D := D) (f := f) (x := x) (y := y) (v := v) (r := r) (u := u)
      hyint hr hu hopen
  · let ε : ℕ -> ℝ := fun m => (1 : ℝ) / (m + 1)
    let yseq : ℕ -> EuclideanSpace ℝ (Fin n) :=
      fun m => ε m • x0 + (1 - ε m) • y
    have hineq_seq :
        ∀ m : ℕ,
          f x + innerFunctional ((-1 / r) • v) (yseq m - x) <=
            ε m * f x0 + (1 - ε m) * f y := by
      intro m
      have hε_pos : 0 < ε m := by
        exact one_div_pos.mpr (by positivity)
      have hε_nonneg : 0 <= ε m := le_of_lt hε_pos
      have hε_le_one : ε m <= 1 := by
        dsimp [ε]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
        norm_num
      have hyseq_int : yseq m ∈ interior D := by
        have hconvD : Convex ℝ D := (convexOn_of_convexOnDomain_euclidean hf).1
        have hmem := hconvD.combo_self_interior_mem_interior hyD hx0int
          (sub_nonneg.mpr hε_le_one) hε_pos (by ring)
        simpa [yseq, add_comm] using hmem
      have hsub :=
        normalized_separator_subgradient_interior
          (D := D) (f := f) (x := x) (y := yseq m) (v := v) (r := r) (u := u)
          hyseq_int hr hu hopen
      have hconv :
          f (yseq m) <= ε m * f x0 + (1 - ε m) * f y := by
        exact hf.2 x0 (interior_subset hx0int) y hyD
          (ε m) (1 - ε m) hε_nonneg (sub_nonneg.mpr hε_le_one) (by ring)
      exact le_trans hsub hconv
    have hε_tend :
        Filter.Tendsto ε Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hone_sub_tend :
        Filter.Tendsto (fun m : ℕ => 1 - ε m) Filter.atTop (nhds 1) :=
      by simpa using tendsto_const_nhds.sub hε_tend
    have hyseq_tend :
        Filter.Tendsto yseq Filter.atTop (nhds y) := by
      have h1 :
          Filter.Tendsto (fun m : ℕ => ε m • x0) Filter.atTop
            (nhds ((0 : ℝ) • x0)) :=
        hε_tend.smul tendsto_const_nhds
      have h2 :
          Filter.Tendsto (fun m : ℕ => (1 - ε m) • y) Filter.atTop
            (nhds ((1 : ℝ) • y)) :=
        hone_sub_tend.smul tendsto_const_nhds
      have h := h1.add h2
      simpa [yseq] using h
    have hleft_tend :
        Filter.Tendsto
          (fun m : ℕ => f x + innerFunctional ((-1 / r) • v) (yseq m - x))
          Filter.atTop
          (nhds (f x + innerFunctional ((-1 / r) • v) (y - x))) := by
      have hsub_tend :
          Filter.Tendsto (fun m : ℕ => yseq m - x) Filter.atTop (nhds (y - x)) :=
        hyseq_tend.sub tendsto_const_nhds
      have hinner_tend :
          Filter.Tendsto
            (fun m : ℕ => inner ((-1 / r) • v) (yseq m - x))
            Filter.atTop (nhds (inner ((-1 / r) • v) (y - x))) :=
        Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds hsub_tend
      simpa [innerFunctional] using tendsto_const_nhds.add hinner_tend
    have hright_tend :
        Filter.Tendsto (fun m : ℕ => ε m * f x0 + (1 - ε m) * f y)
          Filter.atTop (nhds (f y)) := by
      have h1 :
          Filter.Tendsto (fun m : ℕ => ε m * f x0) Filter.atTop (nhds (0 * f x0)) :=
        hε_tend.mul tendsto_const_nhds
      have h2 :
          Filter.Tendsto (fun m : ℕ => (1 - ε m) * f y) Filter.atTop
            (nhds (1 * f y)) :=
        hone_sub_tend.mul tendsto_const_nhds
      have h := h1.add h2
      simpa using h
    exact le_of_tendsto_of_tendsto' hleft_tend hright_tend hineq_seq

/-- Subdifferential/normal-cone decomposition needed for the Slater KKT
theorem.

This is the exact convex-analysis sum rule behind the KKT theorem: from the
zero domain subgradient of `f` over `D ∩ P`, recover a subgradient over `D`
plus a normal to `P`.  The proof uses finite-dimensional epigraph separation
and the strict feasible interior point to normalize the separating
functional. -/
theorem domainSubderiv_inter_affineFeasible_decomposition_of_slater
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hx : x ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c)
    (hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        (fun z => -g z) ∈
          NormalCone (AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c) x := by
  rcases exists_kktSeparation_separator
      (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
      hregular hzero with
    ⟨v, r, u, hopen, hconstraint⟩
  have hr : r < 0 :=
    kktSeparation_separator_r_neg
      (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
      (v := v) (r := r) (u := u) hregular hzero hopen hconstraint
  have hu : u = 0 :=
    kktSeparation_separator_u_eq_zero
      (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
      (v := v) (r := r) hregular hx hopen hconstraint
  refine ⟨innerFunctional ((-1 / r) • v), ?_, ?_⟩
  · exact normalized_separator_domainSubgradient
      (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
      (v := v) (r := r) (u := u) hregular hx.1 hr hu hopen
  · exact normalized_separator_mem_normalCone
      (a := a) (c := c) (x := x) (v := v) (r := r) (u := u)
      hx.2 hr hu hconstraint

/-- Domain first-order normal-cone certificate from concrete
finite-dimensional Slater assumptions.

This is the Ruszczynski/separation part of the theorem. -/
theorem hasDomainMinimumNormalConeCertificate_of_euclideanSlater
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c) :
    HasDomainMinimumNormalConeCertificate D f
      (fun k : σ => innerFunctional (a k)) c := by
  intro x hx hmin
  have hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x :=
    Optlib.DomainSubgradient.zero_mem_domainSubderiv_of_minimizesOn hmin
  exact domainSubderiv_inter_affineFeasible_decomposition_of_slater
    (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
    hregular hx hzero

theorem domainSubderiv_inter_affineFeasible_decomposition_of_slater_isEmpty
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)} {c : σ -> ℝ}
    {x : EuclideanSpace ℝ (Fin n)} [IsEmpty σ]
    (hzero :
      (fun _ : EuclideanSpace ℝ (Fin n) => 0) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) f x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        (fun z => -g z) ∈
          NormalCone (AffineIneqFeasible (fun k : σ => innerFunctional (a k)) c) x := by
  have hmin :
      Optlib.DomainSubgradient.MinimizesOn f
        (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) x :=
    Optlib.DomainSubgradient.minimizesOn_of_zero_mem_domainSubderiv hzero
  exact domain_minimum_subgradient_normalCone_of_isEmpty
    (D := D) (f := f) (a := fun k : σ => innerFunctional (a k)) (c := c)
    (x := x) hmin.1 hmin

/-- Finite-dimensional affine KKT theorem with concrete Slater assumptions.

The affine normal-cone multiplier part is proved from Farkas, and the
domain-minimum normal-cone condition is proved above from finite-dimensional
separation under the Slater package. -/
theorem exists_kkt_multipliers_domain_affine_finsetSubtype_of_slater
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) -> ℝ}
    {σ : Finset ℕ} {a : σ -> EuclideanSpace ℝ (Fin n)}
    {c : σ -> ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hregular : EuclideanDomainKKTSlaterRegularity D f σ a c)
    (hx : x ∈ DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c)
    (hmin :
      Optlib.DomainSubgradient.MinimizesOn f
        (DomainAffineFeasible D (fun k : σ => innerFunctional (a k)) c) x) :
    ∃ g,
      g ∈ Optlib.DomainSubgradient.DomainSubderiv D f x ∧
        ∃ lambda : σ -> ℝ,
          AffineKKTMultipliers (fun k : σ => innerFunctional (a k)) c x lambda ∧
            AffineKKTStationarity (fun k : σ => innerFunctional (a k)) g lambda := by
  exact exists_kkt_multipliers_domain_affine_finsetSubtype
    (D := D) (f := f) (σ := σ) (a := a) (c := c) (x := x)
    (hasDomainMinimumNormalConeCertificate_of_euclideanSlater
      (D := D) (f := f) (σ := σ) (a := a) (c := c) hregular)
    hx hmin

end

end KKT
end Optlib
