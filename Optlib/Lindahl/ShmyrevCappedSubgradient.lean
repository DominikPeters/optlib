/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Optlib.Lindahl.ShmyrevCapped

/-!
# Subgradient characterization for the capped Shmyrev objective

This file proves the domain-subgradient characterization of the capped
Shmyrev objective used by the KKT-to-Lindahl-equilibrium argument.
-/

open BigOperators
open scoped Topology

namespace Optlib
namespace Lindahl
namespace ShmyrevCapped

noncomputable section

variable {nAgents nProjects : ℕ}

theorem noPartiallyZeroFundedProject_of_domainSubgradient
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b)
    (hg : (contributionFunctional I g) ∈
      Optlib.DomainSubgradient.DomainSubderiv
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevObjective I) b) :
    noPartiallyZeroFundedProject I b := by
  intro e htotal
  by_contra hnotpos
  have hezero : b e = 0 := by
    exact le_antisymm (not_lt.mp hnotpos) (hb e)
  have hslope :=
    shmyrevObjective_line_slope_tendsto_atBot_of_zeroEdge
      I hb hezero htotal
  have h_atbot :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        t⁻¹ * (shmyrevObjective I (b + t • basisContribution I e) -
          shmyrevObjective I b) < g e :=
    hslope.eventually_lt_atBot (g e)
  have hdomain :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        contributionNonnegative I (b + t • basisContribution I e) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro e'
    by_cases heq : e' = e
    · subst e'
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hezero]
      exact le_of_lt ht
    · rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I heq]
      simp [hb e']
  have h_lower :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        g e <=
          t⁻¹ * (shmyrevObjective I (b + t • basisContribution I e) -
            shmyrevObjective I b) := by
    filter_upwards [hdomain, self_mem_nhdsWithin] with t htdom htpos_mem
    have htpos : 0 < t := htpos_mem
    have hsub := hg.2.2 (b + t • basisContribution I e) htdom
    have hdiff :
        (b + t • basisContribution I e - b) =
          t • basisContribution I e := by
      ext e'
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hlin :
        contributionFunctional I g (t • basisContribution I e) =
          t * contributionFunctional I g (basisContribution I e) :=
      (contributionFunctional_linear I g).2 t (basisContribution I e)
    have hineq :
        shmyrevObjective I b +
            t * contributionFunctional I g (basisContribution I e) <=
          shmyrevObjective I (b + t • basisContribution I e) := by
      simpa [hdiff, hlin] using hsub
    have hbasis := contributionFunctional_basis I g e
    have hcalc :
        contributionFunctional I g (basisContribution I e) <=
          t⁻¹ * (shmyrevObjective I (b + t • basisContribution I e) -
            shmyrevObjective I b) := by
      calc
        contributionFunctional I g (basisContribution I e)
            = t⁻¹ * (t * contributionFunctional I g (basisContribution I e)) := by
                field_simp [ne_of_gt htpos]
        _ <= t⁻¹ * (shmyrevObjective I (b + t • basisContribution I e) -
              shmyrevObjective I b) := by
                apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr htpos.le)
                linarith
    simpa [hbasis] using hcalc
  have hcontra : ∀ᶠ _ in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [h_atbot, h_lower] with _t ht_upper ht_lower
    linarith
  haveI : (𝓝[>] (0 : ℝ)).NeBot :=
    nhdsWithin_Ioi_self_neBot' ⟨(1 : ℝ), by simp⟩
  exact (hcontra.exists).elim (fun _ hfalse => hfalse)

theorem positiveProjectSubgradientFormula_of_domainSubgradient
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b)
    (hg : (contributionFunctional I g) ∈
      Optlib.DomainSubgradient.DomainSubderiv
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevObjective I) b) :
    ∀ e : I.PositiveEdge,
      0 < projectTotal I b (edgeProject e.1) ->
        g e =
          - Real.log (I.edgeValuation e) +
            Real.log (b e / projectTotal I b (edgeProject e.1)) := by
  intro e htotal
  have hnopart := noPartiallyZeroFundedProject_of_domainSubgradient I hb hg
  have hbepos : 0 < b e := hnopart e htotal
  let F : ℝ -> ℝ :=
    fun t => shmyrevObjective I (b + t • basisContribution I e)
  let D : ℝ :=
    - Real.log (I.edgeValuation e) +
      Real.log (b e / projectTotal I b (edgeProject e.1))
  have hderiv : HasDerivAt F D 0 := by
    simpa [F, D] using
      shmyrevObjective_hasDerivAt_positiveEdge_line I hb hbepos htotal
  have hpos_domain :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        contributionNonnegative I (b + t • basisContribution I e) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro e'
    by_cases heq : e' = e
    · subst e'
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb e]
      have htpos : 0 < t := ht
      linarith
    · rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I heq]
      simp [hb e']
  have hneg_domain :
      ∀ᶠ t in 𝓝[<] (0 : ℝ),
        contributionNonnegative I (b + t • basisContribution I e) := by
    have h_event : ∀ᶠ t in 𝓝 (0 : ℝ), -b e < t := by
      exact lt_mem_nhds (by linarith)
    filter_upwards [h_event.filter_mono nhdsWithin_le_nhds]
      with t ht_lower
    intro e'
    by_cases heq : e' = e
    · subst e'
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · rw [Pi.add_apply, Pi.smul_apply, basisContribution_ne I heq]
      simp [hb e']
  have hG :
      contributionFunctional I g (basisContribution I e) = g e :=
    contributionFunctional_basis I g e
  have hle_pos :
      g e <= D := by
    have htend := hderiv.tendsto_slope_zero_right
    apply ge_of_tendsto htend
    filter_upwards [hpos_domain, self_mem_nhdsWithin] with t htdom htpos_mem
    have htpos : 0 < t := htpos_mem
    have hsub := hg.2.2 (b + t • basisContribution I e) htdom
    have hdiff :
        (b + t • basisContribution I e - b) =
          t • basisContribution I e := by
      ext e'
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hlin :
        contributionFunctional I g (t • basisContribution I e) =
          t * contributionFunctional I g (basisContribution I e) :=
      (contributionFunctional_linear I g).2 t (basisContribution I e)
    have hineq :
        F 0 + t * contributionFunctional I g (basisContribution I e) <=
          F (0 + t) := by
      simpa [F, hdiff, hlin] using hsub
    have hcalc :
        contributionFunctional I g (basisContribution I e) <=
          t⁻¹ * (F (0 + t) - F 0) := by
      calc
        contributionFunctional I g (basisContribution I e)
            = t⁻¹ * (t * contributionFunctional I g (basisContribution I e)) := by
                field_simp [ne_of_gt htpos]
        _ <= t⁻¹ * (F (0 + t) - F 0) := by
                apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr htpos.le)
                linarith
    simpa [hG, smul_eq_mul] using hcalc
  have hle_neg :
      D <= g e := by
    have htend := hderiv.tendsto_slope_zero_left
    apply le_of_tendsto htend
    filter_upwards [hneg_domain, self_mem_nhdsWithin] with t htdom htneg_mem
    have htneg : t < 0 := htneg_mem
    have hsub := hg.2.2 (b + t • basisContribution I e) htdom
    have hdiff :
        (b + t • basisContribution I e - b) =
          t • basisContribution I e := by
      ext e'
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hlin :
        contributionFunctional I g (t • basisContribution I e) =
          t * contributionFunctional I g (basisContribution I e) :=
      (contributionFunctional_linear I g).2 t (basisContribution I e)
    have hineq :
        F 0 + t * contributionFunctional I g (basisContribution I e) <=
          F (0 + t) := by
      simpa [F, hdiff, hlin] using hsub
    have hmul :
        t⁻¹ * (F (0 + t) - F 0) <=
          t⁻¹ * (t * contributionFunctional I g (basisContribution I e)) := by
      apply mul_le_mul_of_nonpos_left ?_ (inv_nonpos.mpr htneg.le)
      linarith
    have hcalc :
        t⁻¹ * (F (0 + t) - F 0) <=
          contributionFunctional I g (basisContribution I e) := by
      calc
        t⁻¹ * (F (0 + t) - F 0)
            <= t⁻¹ * (t * contributionFunctional I g (basisContribution I e)) := hmul
        _ = contributionFunctional I g (basisContribution I e) := by
            field_simp [ne_of_lt htneg]
    simpa [hG, smul_eq_mul] using hcalc
  exact le_antisymm hle_pos hle_neg

theorem zeroProjectLogSumExp_of_domainSubgradient
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b)
    (hg : (contributionFunctional I g) ∈
      Optlib.DomainSubgradient.DomainSubderiv
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevObjective I) b) :
    ∀ j : Project nProjects,
      projectTotal I b j = 0 ->
        (∑ i : Agent nAgents,
          if h : (i, j) ∈ I.positiveEdges then
            Real.exp (g ⟨(i, j), h⟩ + Real.log (I.edgeValuation ⟨(i, j), h⟩))
          else 0) <= 1 := by
  intro j hj
  let y : Contribution I := zeroProjectSubgradientTest I b g j
  have hy : contributionNonnegative I y :=
    zeroProjectSubgradientTest_nonnegative I hb j
  have hsub := hg.2.2 y hy
  have hpair :
      contributionFunctional I g (y - b) =
        ∑ e : I.PositiveEdge,
          if edgeProject e.1 = j then
            g e * Real.exp (g e + Real.log (I.edgeValuation e))
          else 0 := by
    simpa [y] using
      contributionFunctional_zeroProjectSubgradientTest_sub
        I hb (g := g) hj
  have hobj :
      shmyrevObjective I y =
        shmyrevObjective I b +
          (∑ e : I.PositiveEdge,
            if edgeProject e.1 = j then
              g e * Real.exp (g e + Real.log (I.edgeValuation e))
            else 0) -
          projectTotal I y j * Real.log (projectTotal I y j) := by
    simpa [y] using
      shmyrevObjective_zeroProjectSubgradientTest_eq
        I hb (g := g) hj
  have hmul_nonpos :
      projectTotal I y j * Real.log (projectTotal I y j) <= 0 := by
    rw [hpair, hobj] at hsub
    linarith
  have htotal_le_one : projectTotal I y j <= 1 :=
    le_one_of_mul_log_nonpos hmul_nonpos
  simpa [y, projectTotal_zeroProjectSubgradientTest] using htotal_le_one

/-- Analytic subgradient characterization still needed for the paper-level
KKT data.

The finite Slater KKT theorem now produces a domain subgradient of
`shmyrevObjective` on the nonnegative orthant.  This theorem is the remaining
real-analysis bridge: it must recover the explicit positive-project formula,
rule out partially zero funded positive projects, and prove the zero-project
log-sum-exp inequality used in the Lindahl price construction.
-/
theorem shmyrevSubgradientAt_of_domainSubgradient
    (I : CappedInstance nAgents nProjects) {b g : Contribution I}
    (hb : contributionNonnegative I b)
    (hg : (contributionFunctional I g) ∈
      Optlib.DomainSubgradient.DomainSubderiv
        {b : Contribution I | contributionNonnegative I b}
        (shmyrevObjective I) b) :
    shmyrevSubgradientAt I b g := by
  exact ⟨noPartiallyZeroFundedProject_of_domainSubgradient I hb hg,
    positiveProjectSubgradientFormula_of_domainSubgradient I hb hg,
    zeroProjectLogSumExp_of_domainSubgradient I hb hg⟩

end
end ShmyrevCapped
end Lindahl
end Optlib
