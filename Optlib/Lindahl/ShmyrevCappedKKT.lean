/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Optlib.Lindahl.Core
import Optlib.Lindahl.ShmyrevCappedSubgradient

/-!
# KKT assembly for the capped Shmyrev/Lindahl theorem

This file contains the finite-dimensional bridge from the general domain-aware
Slater KKT theorem to the concrete capped Shmyrev program.  It also assembles
the final theorem
`Optlib.Lindahl.ShmyrevCapped.optimal_shmyrev_is_lindahl`.

The main theorem uses the model, objective, KKT data, price construction, and
analytic subgradient lemmas from `Optlib.Lindahl.ShmyrevCappedSubgradient`.  The bridge
work here is concentrated in:

* entropy-perspective convexity and subgradient calculus;
* the finite-dimensional Euclidean bridge needed to instantiate the proved
  Slater KKT theorem for the concrete Shmyrev variables.
-/

open BigOperators
open InnerProductSpace
open scoped Topology

namespace Optlib
namespace Lindahl
namespace ShmyrevCapped
namespace KKTBridge

noncomputable section

variable {nAgents nProjects : ℕ}

/-- Number of positive-valuation variables in the Shmyrev program. -/
def edgeCard (I : CappedInstance nAgents nProjects) : ℕ :=
  Fintype.card I.PositiveEdge

/-- Canonical finite coordinate enumeration for positive edges. -/
def edgeEquivFin (I : CappedInstance nAgents nProjects) :
    I.PositiveEdge ≃ Fin (edgeCard I) :=
  Fintype.equivFin I.PositiveEdge

/-- Encode a contribution vector as a Euclidean vector. -/
def toEuclidean (I : CappedInstance nAgents nProjects)
    (b : Contribution I) : EuclideanSpace ℝ (Fin (edgeCard I)) :=
  fun k => b ((edgeEquivFin I).symm k)

/-- Decode a Euclidean vector as a contribution vector. -/
def fromEuclidean (I : CappedInstance nAgents nProjects)
    (x : EuclideanSpace ℝ (Fin (edgeCard I))) : Contribution I :=
  fun e => x (edgeEquivFin I e)

/-- Nonnegative orthant in Euclidean coordinates. -/
def euclideanContributionDomain (I : CappedInstance nAgents nProjects) :
    Set (EuclideanSpace ℝ (Fin (edgeCard I))) :=
  {x | ∀ k, 0 <= x k}

/-- Capped Shmyrev objective after Euclidean coordinate encoding. -/
def euclideanShmyrevObjective (I : CappedInstance nAgents nProjects)
    (x : EuclideanSpace ℝ (Fin (edgeCard I))) : ℝ :=
  shmyrevObjective I (fromEuclidean I x)

theorem contributionNonnegative_fromEuclidean
    (I : CappedInstance nAgents nProjects)
    {x : EuclideanSpace ℝ (Fin (edgeCard I))}
    (hx : x ∈ euclideanContributionDomain I) :
    contributionNonnegative I (fromEuclidean I x) := by
  intro e
  exact hx (edgeEquivFin I e)

theorem euclideanContributionDomain_convexDomain
    (I : CappedInstance nAgents nProjects) :
    Optlib.DomainSubgradient.ConvexDomain (euclideanContributionDomain I) := by
  intro x hx y hy a d ha hd _had
  intro k
  simp [euclideanContributionDomain, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  exact add_nonneg (mul_nonneg ha (hx k)) (mul_nonneg hd (hy k))

theorem fromEuclidean_continuous
    (I : CappedInstance nAgents nProjects) :
    Continuous (fromEuclidean I :
      EuclideanSpace ℝ (Fin (edgeCard I)) -> Contribution I) := by
  unfold fromEuclidean
  exact continuous_pi fun e => continuous_apply (edgeEquivFin I e)

theorem euclideanShmyrevObjective_continuousOn_domain
    (I : CappedInstance nAgents nProjects) :
    ContinuousOn (euclideanShmyrevObjective I) (euclideanContributionDomain I) := by
  unfold euclideanShmyrevObjective
  refine (shmyrev_objective_continuousOn_domain I).comp'
    (fromEuclidean_continuous I).continuousOn ?_
  intro x hx
  exact contributionNonnegative_fromEuclidean I hx

@[simp] theorem fromEuclidean_add
    (I : CappedInstance nAgents nProjects)
    (x y : EuclideanSpace ℝ (Fin (edgeCard I))) :
    fromEuclidean I (x + y) = fromEuclidean I x + fromEuclidean I y := by
  funext e
  simp [fromEuclidean]

@[simp] theorem fromEuclidean_smul
    (I : CappedInstance nAgents nProjects) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin (edgeCard I))) :
    fromEuclidean I (r • x) = r • fromEuclidean I x := by
  funext e
  simp [fromEuclidean, smul_eq_mul]

theorem fromEuclidean_convex_combo
    (I : CappedInstance nAgents nProjects)
    (x y : EuclideanSpace ℝ (Fin (edgeCard I))) (a d : ℝ) :
    fromEuclidean I (a • x + d • y) =
      a • fromEuclidean I x + d • fromEuclidean I y := by
  simp

@[simp] theorem toEuclidean_add
    (I : CappedInstance nAgents nProjects)
    (b c : Contribution I) :
    toEuclidean I (b + c) = toEuclidean I b + toEuclidean I c := by
  funext k
  simp [toEuclidean]

@[simp] theorem toEuclidean_neg
    (I : CappedInstance nAgents nProjects)
    (b : Contribution I) :
    toEuclidean I (-b) = -toEuclidean I b := by
  funext k
  simp [toEuclidean]

@[simp] theorem toEuclidean_sub
    (I : CappedInstance nAgents nProjects)
    (b c : Contribution I) :
    toEuclidean I (b - c) = toEuclidean I b - toEuclidean I c := by
  funext k
  simp [sub_eq_add_neg]

@[simp] theorem toEuclidean_smul
    (I : CappedInstance nAgents nProjects) (r : ℝ)
    (b : Contribution I) :
    toEuclidean I (r • b) = r • toEuclidean I b := by
  funext k
  simp [toEuclidean, smul_eq_mul]

theorem euclideanFunctional_pullback_linear
    (I : CappedInstance nAgents nProjects)
    {G : EuclideanSpace ℝ (Fin (edgeCard I)) -> ℝ}
    (hGlin : Optlib.DomainSubgradient.IsLinearFunctional G) :
    Optlib.DomainSubgradient.IsLinearFunctional
      (fun z : Contribution I => G (toEuclidean I z)) := by
  constructor
  · intro z w
    simp [hGlin.1]
  · intro r z
    simp [hGlin.2]

def contributionGradientOfEuclidean
    (I : CappedInstance nAgents nProjects)
    (G : EuclideanSpace ℝ (Fin (edgeCard I)) -> ℝ) :
    Contribution I :=
  fun e => G (toEuclidean I (basisContribution I e))

theorem euclideanShmyrevObjective_convexOn_domain
    (I : CappedInstance nAgents nProjects) :
    Optlib.DomainSubgradient.ConvexOnDomain
      (euclideanContributionDomain I) (euclideanShmyrevObjective I) := by
  refine ⟨euclideanContributionDomain_convexDomain I, ?_⟩
  intro x hx y hy a d ha hd had
  have hx' : fromEuclidean I x ∈
      {b : Contribution I | contributionNonnegative I b} :=
    contributionNonnegative_fromEuclidean I hx
  have hy' : fromEuclidean I y ∈
      {b : Contribution I | contributionNonnegative I b} :=
    contributionNonnegative_fromEuclidean I hy
  have hconv := (shmyrev_objective_convex I).2
    (fromEuclidean I x) hx' (fromEuclidean I y) hy' a d ha hd had
  unfold euclideanShmyrevObjective
  simpa [fromEuclidean_convex_combo I x y a d] using hconv

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

theorem mem_interior_euclideanContributionDomain_of_pos
    (I : CappedInstance nAgents nProjects)
    {x : EuclideanSpace ℝ (Fin (edgeCard I))}
    (hxpos : ∀ k, 0 < x k) :
    x ∈ interior (euclideanContributionDomain I) := by
  let U : Set (EuclideanSpace ℝ (Fin (edgeCard I))) := {y | ∀ k, 0 < y k}
  have hUopen : IsOpen U := by
    have hU : U = ⋂ k : Fin (edgeCard I),
        {y : EuclideanSpace ℝ (Fin (edgeCard I)) | 0 < y k} := by
      ext y
      simp [U]
    rw [hU]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt continuous_const (continuous_apply k)
  have hsubset : U ⊆ euclideanContributionDomain I := by
    intro y hy k
    exact (hy k).le
  exact interior_maximal hsubset hUopen hxpos

/-- Constraint vectors and right-hand sides in Euclidean coordinates.

The affine functional for a constraint `k` is represented by the vector whose
inner product with `x` is the original contribution-space functional applied to
`fromEuclidean I x`.
-/
def euclideanConstraintVector (I : CappedInstance nAgents nProjects)
    (k : ShmyrevKKTConstraint I) :
    EuclideanSpace ℝ (Fin (edgeCard I)) :=
  fun e => shmyrevKKTConstraintFunctional I k
    (basisContribution I ((edgeEquivFin I).symm e))

def euclideanConstraintRhs (I : CappedInstance nAgents nProjects)
    (k : ShmyrevKKTConstraint I) : ℝ :=
  shmyrevKKTConstraintRhs I k

@[simp] theorem fromEuclidean_toEuclidean
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    fromEuclidean I (toEuclidean I b) = b := by
  funext e
  simp [fromEuclidean, toEuclidean]

@[simp] theorem toEuclidean_fromEuclidean
    (I : CappedInstance nAgents nProjects)
    (x : EuclideanSpace ℝ (Fin (edgeCard I))) :
    toEuclidean I (fromEuclidean I x) = x := by
  funext k
  exact congrArg x ((edgeEquivFin I).right_inv k)

/-- Expansion of an algebraically linear functional in the standard
contribution basis. -/
theorem linearFunctional_eq_sum_basis
    (I : CappedInstance nAgents nProjects) (ell : Contribution I -> ℝ)
    (hell : Optlib.DomainSubgradient.IsLinearFunctional ell)
    (z : Contribution I) :
    ell z = ∑ e : I.PositiveEdge, z e * ell (basisContribution I e) := by
  classical
  let L : Contribution I →ₗ[ℝ] ℝ :=
    { toFun := ell
      map_add' := hell.1
      map_smul' := fun r x => hell.2 r x }
  have hrepr : (∑ e : I.PositiveEdge, z e • basisContribution I e) = z := by
    funext e
    simp [basisContribution]
  calc
    ell z = L z := rfl
    _ = L (∑ e : I.PositiveEdge, z e • basisContribution I e) := by
      rw [hrepr]
    _ = ∑ e : I.PositiveEdge, L (z e • basisContribution I e) := by
      rw [map_sum]
    _ = ∑ e : I.PositiveEdge, z e * ell (basisContribution I e) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [map_smul]
      rfl

theorem euclideanFunctional_pullback_eq_contributionFunctional
    (I : CappedInstance nAgents nProjects)
    {G : EuclideanSpace ℝ (Fin (edgeCard I)) -> ℝ}
    (hGlin : Optlib.DomainSubgradient.IsLinearFunctional G)
    (z : Contribution I) :
    G (toEuclidean I z) =
      contributionFunctional I (contributionGradientOfEuclidean I G) z := by
  have hpull := linearFunctional_eq_sum_basis I
    (fun z : Contribution I => G (toEuclidean I z))
    (euclideanFunctional_pullback_linear I hGlin) z
  calc
    G (toEuclidean I z) =
        ∑ e : I.PositiveEdge,
          z e * G (toEuclidean I (basisContribution I e)) := hpull
    _ = contributionFunctional I (contributionGradientOfEuclidean I G) z := by
        unfold contributionFunctional contributionGradientOfEuclidean
        apply Finset.sum_congr rfl
        intro e _he
        rw [mul_comm]

/-- The Euclidean constraint vector represents the original affine functional. -/
theorem innerFunctional_euclideanConstraintVector
    (I : CappedInstance nAgents nProjects)
    (k : ShmyrevKKTConstraint I)
    (x : EuclideanSpace ℝ (Fin (edgeCard I))) :
    Optlib.KKT.innerFunctional (euclideanConstraintVector I k) x =
      shmyrevKKTConstraintFunctional I k (fromEuclidean I x) := by
  classical
  have hlin := shmyrevKKTConstraintFunctional_linear I k
  have hbasis := linearFunctional_eq_sum_basis I
    (shmyrevKKTConstraintFunctional I k) hlin (fromEuclidean I x)
  calc
    Optlib.KKT.innerFunctional (euclideanConstraintVector I k) x
        = ∑ e : Fin (edgeCard I),
            shmyrevKKTConstraintFunctional I k
              (basisContribution I ((edgeEquivFin I).symm e)) * x e := by
          simp [Optlib.KKT.innerFunctional, euclideanConstraintVector, PiLp.inner_apply]
    _ = ∑ e : I.PositiveEdge,
          x (edgeEquivFin I e) * shmyrevKKTConstraintFunctional I k
            (basisContribution I e) := by
          rw [← (edgeEquivFin I).sum_comp
            (fun e : Fin (edgeCard I) =>
              shmyrevKKTConstraintFunctional I k
                (basisContribution I ((edgeEquivFin I).symm e)) * x e)]
          apply Finset.sum_congr rfl
          intro e _he
          simp [mul_comm]
    _ = shmyrevKKTConstraintFunctional I k (fromEuclidean I x) := by
          simpa [fromEuclidean, mul_comm] using hbasis.symm

/-- Round-trip and linearity obligations for the coordinate bridge. -/
def CoordinateBridgeObligations
    (I : CappedInstance nAgents nProjects) : Prop :=
  (∀ b : Contribution I, fromEuclidean I (toEuclidean I b) = b) ∧
    (∀ x : EuclideanSpace ℝ (Fin (edgeCard I)),
      toEuclidean I (fromEuclidean I x) = x) ∧
    (∀ k x,
      Optlib.KKT.innerFunctional (euclideanConstraintVector I k) x =
        shmyrevKKTConstraintFunctional I k (fromEuclidean I x))

theorem coordinateBridgeObligations
    (I : CappedInstance nAgents nProjects) :
    CoordinateBridgeObligations I := by
  refine ⟨fromEuclidean_toEuclidean I, toEuclidean_fromEuclidean I, ?_⟩
  intro k x
  exact innerFunctional_euclideanConstraintVector I k x

theorem exists_euclidean_strictSlater
    (I : CappedInstance nAgents nProjects) :
    ∃ x0, x0 ∈ interior (euclideanContributionDomain I) ∧
      ∀ k : ShmyrevKKTConstraint I,
        Optlib.KKT.innerFunctional (euclideanConstraintVector I k) x0 <
          euclideanConstraintRhs I k := by
  rcases exists_shmyrev_slater_regular I with ⟨b, hbpos, hbudget, hcap⟩
  refine ⟨toEuclidean I b, ?_, ?_⟩
  · apply mem_interior_euclideanContributionDomain_of_pos
    intro k
    exact hbpos ((edgeEquivFin I).symm k)
  · intro k
    rw [innerFunctional_euclideanConstraintVector I k]
    have hfrom : fromEuclidean I (toEuclidean I b) = b :=
      fromEuclidean_toEuclidean I b
    cases k with
    | budget i =>
        simpa [euclideanConstraintRhs, shmyrevKKTConstraintFunctional,
          shmyrevKKTConstraintRhs, hfrom] using hbudget i
    | cap j =>
        simpa [euclideanConstraintRhs, shmyrevKKTConstraintFunctional,
          shmyrevKKTConstraintRhs, hfrom] using hcap j
    | nonneg e =>
        have hpos := hbpos e
        simpa [euclideanConstraintRhs, shmyrevKKTConstraintFunctional,
          shmyrevKKTConstraintRhs, hfrom] using neg_neg_of_pos hpos

/-- Convexity/continuity/Slater obligations needed by the finite KKT theorem. -/
def EuclideanSlaterKKTObligations
    (I : CappedInstance nAgents nProjects) : Prop :=
  Optlib.DomainSubgradient.ConvexDomain (euclideanContributionDomain I) ∧
    Optlib.DomainSubgradient.ConvexOnDomain
      (euclideanContributionDomain I) (euclideanShmyrevObjective I) ∧
    ContinuousOn (euclideanShmyrevObjective I) (euclideanContributionDomain I) ∧
    ∃ x0, x0 ∈ interior (euclideanContributionDomain I) ∧
      ∀ k : ShmyrevKKTConstraint I,
        Optlib.KKT.innerFunctional (euclideanConstraintVector I k) x0 <
          euclideanConstraintRhs I k

theorem euclideanSlaterKKTObligations
    (I : CappedInstance nAgents nProjects) :
    EuclideanSlaterKKTObligations I := by
  exact ⟨euclideanContributionDomain_convexDomain I,
    euclideanShmyrevObjective_convexOn_domain I,
    euclideanShmyrevObjective_continuousOn_domain I,
    exists_euclidean_strictSlater I⟩

/-- Number of affine constraints in the KKT encoding. -/
def constraintCard (I : CappedInstance nAgents nProjects) : ℕ :=
  Fintype.card (ShmyrevKKTConstraint I)

/-- Canonical finite coordinate enumeration for KKT constraints. -/
def constraintEquivFin (I : CappedInstance nAgents nProjects) :
    ShmyrevKKTConstraint I ≃ Fin (constraintCard I) :=
  Fintype.equivFin (ShmyrevKKTConstraint I)

/-- Natural-number labels used by the finite Slater KKT theorem. -/
def constraintLabels (I : CappedInstance nAgents nProjects) : Finset ℕ :=
  Finset.range (constraintCard I)

def constraintLabelFinEquiv (I : CappedInstance nAgents nProjects) :
    (constraintLabels I) ≃ Fin (constraintCard I) where
  toFun k := ⟨k.1, by
    exact Finset.mem_range.mp k.2⟩
  invFun k := ⟨k.1, by
    exact Finset.mem_range.mpr k.2⟩
  left_inv := by
    intro k
    exact Subtype.ext rfl
  right_inv := by
    intro k
    exact Fin.ext rfl

def constraintOfLabel (I : CappedInstance nAgents nProjects)
    (k : constraintLabels I) : ShmyrevKKTConstraint I :=
  (constraintEquivFin I).symm (constraintLabelFinEquiv I k)

def constraintLabelEquiv (I : CappedInstance nAgents nProjects) :
    constraintLabels I ≃ ShmyrevKKTConstraint I where
  toFun := constraintOfLabel I
  invFun k := (constraintLabelFinEquiv I).symm (constraintEquivFin I k)
  left_inv := by
    intro k
    unfold constraintOfLabel
    simp
  right_inv := by
    intro k
    unfold constraintOfLabel
    simp

def euclideanLabelConstraintVector (I : CappedInstance nAgents nProjects)
    (k : constraintLabels I) :
    EuclideanSpace ℝ (Fin (edgeCard I)) :=
  euclideanConstraintVector I (constraintOfLabel I k)

def euclideanLabelConstraintRhs (I : CappedInstance nAgents nProjects)
    (k : constraintLabels I) : ℝ :=
  euclideanConstraintRhs I (constraintOfLabel I k)

theorem euclideanDomainKKTSlaterRegularity_labelled
    (I : CappedInstance nAgents nProjects) :
    Optlib.KKT.EuclideanDomainKKTSlaterRegularity
      (euclideanContributionDomain I) (euclideanShmyrevObjective I)
      (constraintLabels I) (euclideanLabelConstraintVector I)
      (euclideanLabelConstraintRhs I) := by
  rcases euclideanSlaterKKTObligations I with ⟨hD, hf, hcont, x0, hx0, hstrict⟩
  refine ⟨hD, hf, hcont, x0, hx0, ?_⟩
  intro k
  exact hstrict (constraintOfLabel I k)

theorem toEuclidean_mem_domain_iff
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    toEuclidean I b ∈ euclideanContributionDomain I ↔
      contributionNonnegative I b := by
  constructor
  · intro hb e
    simpa [toEuclidean] using hb (edgeEquivFin I e)
  · intro hb k
    exact hb ((edgeEquivFin I).symm k)

theorem contributionSubgradient_of_euclideanSubgradient
    (I : CappedInstance nAgents nProjects)
    {b : Contribution I}
    {G : EuclideanSpace ℝ (Fin (edgeCard I)) -> ℝ}
    (hG : G ∈ Optlib.DomainSubgradient.DomainSubderiv
      (euclideanContributionDomain I) (euclideanShmyrevObjective I)
      (toEuclidean I b)) :
    contributionFunctional I (contributionGradientOfEuclidean I G) ∈
      Optlib.DomainSubgradient.DomainSubderiv
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevObjective I) b := by
  rcases hG with ⟨hx, hGlin, hineq⟩
  refine ⟨?_, contributionFunctional_linear I _, ?_⟩
  · exact (toEuclidean_mem_domain_iff I b).mp hx
  · intro y hy
    have hyE : toEuclidean I y ∈ euclideanContributionDomain I :=
      (toEuclidean_mem_domain_iff I y).mpr hy
    have h := hineq (toEuclidean I y) hyE
    have hpull := euclideanFunctional_pullback_eq_contributionFunctional
      I hGlin (y - b)
    simpa [euclideanShmyrevObjective, fromEuclidean_toEuclidean,
      ← toEuclidean_sub, hpull] using h

theorem toEuclidean_mem_labelledDomainAffineFeasible_iff
    (I : CappedInstance nAgents nProjects) (b : Contribution I) :
    toEuclidean I b ∈
      Optlib.KKT.DomainAffineFeasible
        (euclideanContributionDomain I)
        (fun k : constraintLabels I =>
          Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
        (euclideanLabelConstraintRhs I) ↔
      shmyrevFeasible I b := by
  constructor
  · intro hb
    rw [shmyrevFeasible_iff_domainKKTFeasible I b]
    refine ⟨?_, ?_⟩
    · exact (toEuclidean_mem_domain_iff I b).mp hb.1
    · intro k
      rcases (constraintLabelEquiv I).surjective k with ⟨label, rfl⟩
      have hlabel := hb.2 label
      simpa [euclideanLabelConstraintVector, euclideanLabelConstraintRhs,
        constraintLabelEquiv, constraintOfLabel, innerFunctional_euclideanConstraintVector,
        fromEuclidean_toEuclidean] using hlabel
  · intro hb
    rw [shmyrevFeasible_iff_domainKKTFeasible I b] at hb
    refine ⟨?_, ?_⟩
    · exact (toEuclidean_mem_domain_iff I b).mpr hb.1
    · intro label
      have h := hb.2 (constraintOfLabel I label)
      simpa [euclideanLabelConstraintVector, euclideanLabelConstraintRhs,
        innerFunctional_euclideanConstraintVector, fromEuclidean_toEuclidean] using h

theorem euclidean_minimizesOn_of_shmyrevOptimal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    Optlib.DomainSubgradient.MinimizesOn
      (euclideanShmyrevObjective I)
      (Optlib.KKT.DomainAffineFeasible
        (euclideanContributionDomain I)
        (fun k : constraintLabels I =>
          Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
        (euclideanLabelConstraintRhs I))
      (toEuclidean I b) := by
  refine ⟨?_, ?_⟩
  · exact (toEuclidean_mem_labelledDomainAffineFeasible_iff I b).mpr hb.1
  · intro y hy
    have hy_to :
        toEuclidean I (fromEuclidean I y) ∈
          Optlib.KKT.DomainAffineFeasible
            (euclideanContributionDomain I)
            (fun k : constraintLabels I =>
              Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
            (euclideanLabelConstraintRhs I) := by
      simpa [toEuclidean_fromEuclidean I y] using hy
    have hy_shmyrev :
        shmyrevFeasible I (fromEuclidean I y) :=
      (toEuclidean_mem_labelledDomainAffineFeasible_iff I
        (fromEuclidean I y)).mp hy_to
    have hmin := hb.2 (fromEuclidean I y) hy_shmyrev
    simpa [euclideanShmyrevObjective, fromEuclidean_toEuclidean] using hmin

theorem exists_euclidean_kkt_data_of_shmyrevOptimal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    ∃ G,
      G ∈ Optlib.DomainSubgradient.DomainSubderiv
        (euclideanContributionDomain I) (euclideanShmyrevObjective I)
        (toEuclidean I b) ∧
        ∃ lambda : constraintLabels I -> ℝ,
          Optlib.KKT.AffineKKTMultipliers
            (fun k : constraintLabels I =>
              Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
            (euclideanLabelConstraintRhs I) (toEuclidean I b) lambda ∧
          Optlib.KKT.AffineKKTStationarity
            (fun k : constraintLabels I =>
              Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
            G lambda := by
  exact Optlib.KKT.exists_kkt_multipliers_domain_affine_finsetSubtype_of_slater
    (D := euclideanContributionDomain I)
    (f := euclideanShmyrevObjective I)
    (σ := constraintLabels I)
    (a := euclideanLabelConstraintVector I)
    (c := euclideanLabelConstraintRhs I)
    (x := toEuclidean I b)
    (euclideanDomainKKTSlaterRegularity_labelled I)
    ((euclidean_minimizesOn_of_shmyrevOptimal I hb).1)
    (euclidean_minimizesOn_of_shmyrevOptimal I hb)

theorem labelledMultiplierFunctional_toEuclidean
    (I : CappedInstance nAgents nProjects)
    (lambda : constraintLabels I -> ℝ) (z : Contribution I) :
    Optlib.KKT.multiplierFunctional
        (fun k : constraintLabels I =>
          Optlib.KKT.innerFunctional (euclideanLabelConstraintVector I k))
        lambda (toEuclidean I z) =
      Optlib.KKT.multiplierFunctional
        (shmyrevKKTConstraintFunctional I)
        (fun k : ShmyrevKKTConstraint I =>
          lambda ((constraintLabelEquiv I).symm k)) z := by
  unfold Optlib.KKT.multiplierFunctional
  rw [← (constraintLabelEquiv I).sum_comp
    (fun k : ShmyrevKKTConstraint I =>
      lambda ((constraintLabelEquiv I).symm k) *
        shmyrevKKTConstraintFunctional I k z)]
  apply Finset.sum_congr rfl
  intro label _hlabel
  have hlabel : (constraintLabelEquiv I).symm ((constraintLabelEquiv I) label) = label :=
    (constraintLabelEquiv I).left_inv label
  rw [hlabel]
  simp [constraintLabelEquiv, constraintOfLabel, euclideanLabelConstraintVector,
    innerFunctional_euclideanConstraintVector, fromEuclidean_toEuclidean]

theorem exists_domain_kkt_data_of_shmyrevOptimal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    ∃ g : Contribution I,
      contributionFunctional I g ∈
        Optlib.DomainSubgradient.DomainSubderiv
          {b : Contribution I | contributionNonnegative I b}
          (shmyrevObjective I) b ∧
        ∃ Lambda : ShmyrevKKTConstraint I -> ℝ,
          Optlib.KKT.AffineKKTMultipliers
            (shmyrevKKTConstraintFunctional I) (shmyrevKKTConstraintRhs I) b Lambda ∧
          Optlib.KKT.AffineKKTStationarity
            (shmyrevKKTConstraintFunctional I) (contributionFunctional I g) Lambda := by
  rcases exists_euclidean_kkt_data_of_shmyrevOptimal I hb with
    ⟨G, hGsub, lambda, hmultLabel, hstatLabel⟩
  let g : Contribution I := contributionGradientOfEuclidean I G
  let Lambda : ShmyrevKKTConstraint I -> ℝ :=
    fun k => lambda ((constraintLabelEquiv I).symm k)
  refine ⟨g, ?_, Lambda, ?_, ?_⟩
  · exact contributionSubgradient_of_euclideanSubgradient I hGsub
  · constructor
    · intro k
      exact hmultLabel.1 ((constraintLabelEquiv I).symm k)
    · intro k
      have h := hmultLabel.2 ((constraintLabelEquiv I).symm k)
      have hk : constraintOfLabel I ((constraintLabelEquiv I).symm k) = k :=
        (constraintLabelEquiv I).right_inv k
      simpa [Lambda, euclideanLabelConstraintVector, euclideanLabelConstraintRhs,
        Optlib.KKT.AffineIneqSlack, innerFunctional_euclideanConstraintVector,
        fromEuclidean_toEuclidean, hk] using h
  · intro z
    have hGlin := hGsub.2.1
    have hpull := euclideanFunctional_pullback_eq_contributionFunctional
      I hGlin z
    have hstat := hstatLabel (toEuclidean I z)
    rw [labelledMultiplierFunctional_toEuclidean I lambda z] at hstat
    simpa [g, Lambda, hpull] using hstat

/-- The entropy-perspective convexity obligation that supports objective
convexity on the nonnegative contribution domain. -/
def EntropyPerspectiveConvexityObligation
    (I : CappedInstance nAgents nProjects) : Prop :=
  ∀ j : Project nProjects,
    ∀ b, contributionNonnegative I b ->
      ∀ c, contributionNonnegative I c ->
        ∀ a d : ℝ, 0 <= a -> 0 <= d -> a + d = 1 ->
          projectEntropyTerm I (a • b + d • c) j <=
            a * projectEntropyTerm I b j + d * projectEntropyTerm I c j

/-- The domain-subgradient-to-paper-subgradient obligation.

After finite KKT gives a domain subgradient of the Euclidean objective, this
is the analytic bridge that recovers the explicit Shmyrev subgradient
conditions used by the price construction.
-/
def ShmyrevSubgradientCharacterizationObligation
    (I : CappedInstance nAgents nProjects) : Prop :=
  ∀ {b : Contribution I} {g : Contribution I},
    contributionNonnegative I b ->
      (contributionFunctional I g) ∈
        Optlib.DomainSubgradient.DomainSubderiv
          {b : Contribution I | contributionNonnegative I b}
          (shmyrevObjective I) b ->
        shmyrevSubgradientAt I b g

/-- Concrete KKT-instantiation obligation for the capped Shmyrev program.

This is the exact remaining bridge between `shmyrevOptimal` and the abstract
KKT data consumed by the already-proved Lindahl-equilibrium derivation.
-/
def ConcreteKKTInstantiationObligation
    (I : CappedInstance nAgents nProjects) : Prop :=
  ∀ {b : Contribution I}, shmyrevOptimal I b ->
    ∃ g : Contribution I,
      shmyrevSubgradientAt I b g ∧
        ∃ Lambda : ShmyrevKKTConstraint I -> ℝ,
          Optlib.KKT.AffineKKTMultipliers
            (shmyrevKKTConstraintFunctional I) (shmyrevKKTConstraintRhs I) b Lambda ∧
          Optlib.KKT.AffineKKTStationarity
            (shmyrevKKTConstraintFunctional I) (contributionFunctional I g) Lambda

theorem concreteKKTInstantiationObligation_of_subgradientCharacterization
    (I : CappedInstance nAgents nProjects)
    (hsubchar : ShmyrevSubgradientCharacterizationObligation I) :
    ConcreteKKTInstantiationObligation I := by
  intro b hb
  rcases exists_domain_kkt_data_of_shmyrevOptimal I hb with
    ⟨g, hgsub, Lambda, hmult, hstat⟩
  refine ⟨g, ?_, Lambda, hmult, hstat⟩
  exact hsubchar hb.1.1 hgsub

/-- Summary package for the non-Lindahl-specific proof obligations used during
development.  The concrete obligations are now discharged below for the capped
Shmyrev program. -/
def RemainingProofObligations
    (I : CappedInstance nAgents nProjects) : Prop :=
  CoordinateBridgeObligations I ∧
    EuclideanSlaterKKTObligations I ∧
    EntropyPerspectiveConvexityObligation I ∧
    ShmyrevSubgradientCharacterizationObligation I ∧
    ConcreteKKTInstantiationObligation I

theorem remainingProofObligations_of_analytic
    (I : CappedInstance nAgents nProjects)
    (hentropy : EntropyPerspectiveConvexityObligation I)
    (hsubchar : ShmyrevSubgradientCharacterizationObligation I) :
    RemainingProofObligations I := by
  exact ⟨coordinateBridgeObligations I, euclideanSlaterKKTObligations I,
    hentropy, hsubchar,
    concreteKKTInstantiationObligation_of_subgradientCharacterization I hsubchar⟩

end

end KKTBridge

variable {nAgents nProjects : ℕ}

theorem exists_abstract_kkt_data_of_optimal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    ∃ g : Contribution I,
      shmyrevSubgradientAt I b g ∧
        ∃ Lambda : ShmyrevKKTConstraint I -> ℝ,
          Optlib.KKT.AffineKKTMultipliers
            (shmyrevKKTConstraintFunctional I) (shmyrevKKTConstraintRhs I) b Lambda ∧
          Optlib.KKT.AffineKKTStationarity
            (shmyrevKKTConstraintFunctional I) (contributionFunctional I g) Lambda := by
  rcases KKTBridge.exists_domain_kkt_data_of_shmyrevOptimal I hb with
    ⟨g, hgsub, Lambda, hmult, hstat⟩
  exact ⟨g, shmyrevSubgradientAt_of_domainSubgradient I hb.1.1 hgsub,
    Lambda, hmult, hstat⟩

theorem exists_kkt_conditions_of_optimal
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    ∃ _ : KKTConditions I b, True := by
  rcases exists_abstract_kkt_data_of_optimal I hb with
    ⟨g, hsub, Lambda, hmult, hstat⟩
  exact ⟨kktConditions_of_abstract I hb.1 hsub hmult hstat, trivial⟩

/-- Formal analogue of `thm:lindahl shmyrev capped`: every optimal solution of
the capped Shmyrev program induces zero-respecting personalized prices forming
a Lindahl equilibrium. -/
theorem optimal_shmyrev_is_lindahl
    (I : CappedInstance nAgents nProjects) {b : Contribution I}
    (hb : shmyrevOptimal I b) :
    ∃ p : Prices I,
      zeroRespecting I (allocationOf I b) p ∧
        LindahlEquilibrium I (allocationOf I b) p := by
  rcases exists_kkt_conditions_of_optimal I hb with ⟨K, _⟩
  refine ⟨priceOfKKT I K, ?_, ?_⟩
  · exact price_zeroRespecting I K
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact allocationOf_feasible_of_shmyrevFeasible I hb.1
    · exact price_nonnegative I K
    · exact price_affordable I hb.1 K
    · exact utilityMaximizing_of_kkt I hb.1 K
    · exact price_profitMaximizing I K

theorem continuous_contributionAt
    (I : CappedInstance nAgents nProjects)
    (i : Agent nAgents) (j : Project nProjects) :
    Continuous (fun b : Contribution I => contributionAt I b i j) := by
  unfold contributionAt
  by_cases h : (i, j) ∈ I.positiveEdges
  · simpa [h] using (continuous_apply ⟨(i, j), h⟩ : Continuous fun b : Contribution I => b ⟨(i, j), h⟩)
  · simpa [h] using (continuous_const : Continuous fun _b : Contribution I => (0 : ℝ))

theorem continuous_projectTotal
    (I : CappedInstance nAgents nProjects) (j : Project nProjects) :
    Continuous (fun b : Contribution I => projectTotal I b j) := by
  unfold projectTotal
  exact continuous_finset_sum _ fun i _ => continuous_contributionAt I i j

theorem continuous_agentSpend
    (I : CappedInstance nAgents nProjects) (i : Agent nAgents) :
    Continuous (fun b : Contribution I => agentSpend I b i) := by
  unfold agentSpend
  exact continuous_finset_sum _ fun j _ => continuous_contributionAt I i j

theorem isClosed_shmyrevFeasibleSet
    (I : CappedInstance nAgents nProjects) :
    IsClosed {b : Contribution I | shmyrevFeasible I b} := by
  have hnonneg : IsClosed {b : Contribution I | contributionNonnegative I b} := by
    simp only [contributionNonnegative, Set.setOf_forall]
    exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
  have hbudget :
      IsClosed {b : Contribution I | ∀ i, agentSpend I b i <= I.budget i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_agentSpend I i) continuous_const
  have hcap :
      IsClosed {b : Contribution I | ∀ j, projectTotal I b j <= I.cap j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j =>
      isClosed_le (continuous_projectTotal I j) continuous_const
  simpa [shmyrevFeasible, Set.setOf_and] using hnonneg.inter (hbudget.inter hcap)

def feasibleBoxUpper (I : CappedInstance nAgents nProjects) : Contribution I :=
  fun e => I.cap (edgeProject e.1)

theorem shmyrevFeasible_subset_box
    (I : CappedInstance nAgents nProjects) :
    {b : Contribution I | shmyrevFeasible I b} ⊆
      Set.Icc (0 : Contribution I) (feasibleBoxUpper I) := by
  intro b hb
  constructor
  · intro e
    exact hb.1 e
  · intro e
    have hcontrib :
        b e = contributionAt I b (edgeAgent e.1) (edgeProject e.1) := by
      rcases e with ⟨⟨i, j⟩, he⟩
      simp [contributionAt, edgeAgent, edgeProject, he]
    calc
      b e = contributionAt I b (edgeAgent e.1) (edgeProject e.1) := hcontrib
      _ <= projectTotal I b (edgeProject e.1) :=
          contributionAt_le_projectTotal I hb.1 (edgeAgent e.1) (edgeProject e.1)
      _ <= I.cap (edgeProject e.1) := hb.2.2 (edgeProject e.1)

theorem isCompact_shmyrevFeasibleSet
    (I : CappedInstance nAgents nProjects) :
    IsCompact {b : Contribution I | shmyrevFeasible I b} := by
  exact IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_shmyrevFeasibleSet I) (shmyrevFeasible_subset_box I)

theorem shmyrevFeasibleSet_nonempty
    (I : CappedInstance nAgents nProjects) :
    ({b : Contribution I | shmyrevFeasible I b} : Set (Contribution I)).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro _e
    exact le_rfl
  · intro i
    unfold agentSpend contributionAt
    simp
    exact I.budget_nonneg i
  · intro j
    unfold projectTotal contributionAt
    simp
    exact (I.cap_pos j).le

theorem exists_shmyrevOptimal
    (I : CappedInstance nAgents nProjects) :
    ∃ b : Contribution I, shmyrevOptimal I b := by
  let s : Set (Contribution I) := {b | shmyrevFeasible I b}
  have hscompact : IsCompact s := isCompact_shmyrevFeasibleSet I
  have hsnonempty : s.Nonempty := shmyrevFeasibleSet_nonempty I
  have hcont : ContinuousOn (shmyrevObjective I) s :=
    (shmyrev_objective_continuousOn_domain I).mono (by
      intro b hb
      exact hb.1)
  rcases hscompact.exists_isMinOn hsnonempty hcont with ⟨b, hb, hmin⟩
  exact ⟨b, hb, fun b' hb' => hmin hb'⟩

/-- Existence of a zero-respecting Lindahl equilibrium follows by compactness
of the capped Shmyrev feasible set and the optimality-to-equilibrium theorem. -/
theorem exists_lindahlEquilibrium
    (I : CappedInstance nAgents nProjects) :
    ∃ x : Allocation I, ∃ p : Prices I,
      zeroRespecting I x p ∧ LindahlEquilibrium I x p := by
  rcases exists_shmyrevOptimal I with ⟨b, hb⟩
  rcases optimal_shmyrev_is_lindahl I hb with ⟨p, hzero, hL⟩
  exact ⟨allocationOf I b, p, hzero, hL⟩

/-- Every capped Lindahl instance admits a weak-core allocation. -/
theorem exists_weakCoreOutcome
    (I : CappedInstance nAgents nProjects) :
    ∃ x : Allocation I, inWeakCore I x := by
  rcases exists_lindahlEquilibrium I with ⟨x, p, _hzero, hL⟩
  exact ⟨x, inWeakCore_of_lindahl I hL⟩

end ShmyrevCapped
end Lindahl
end Optlib
