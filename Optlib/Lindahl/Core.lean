/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Optlib.Lindahl.Basic

/-!
# Pareto optimality and the core for capped Lindahl equilibria

This file formalizes the definitions and basic welfare/core consequences from
the paper section "Pareto-Optimality and the Core".
-/

open BigOperators

namespace Optlib
namespace Lindahl
namespace ShmyrevCapped

noncomputable section

variable {nAgents nProjects : ℕ}

def likedProject (I : CappedInstance nAgents nProjects)
    (i : Agent nAgents) (j : Project nProjects) : Prop :=
  0 < I.valuation i j

def friends (I : CappedInstance nAgents nProjects)
    (i f : Agent nAgents) : Prop :=
  ∃ j : Project nProjects, likedProject I i j ∧ likedProject I f j

def likedCap (I : CappedInstance nAgents nProjects)
    (i : Agent nAgents) : ℝ :=
  by
    classical
    exact ∑ j : Project nProjects, if likedProject I i j then I.cap j else 0

def friendsBudget (I : CappedInstance nAgents nProjects)
    (i : Agent nAgents) : ℝ :=
  by
    classical
    exact ∑ f : Agent nAgents, if friends I i f then I.budget f else 0

/-- Cap-sufficiency from `def:cap-sufficient`: each agent's liked projects have
enough total cap to absorb the total budgets of agents who share a liked
project with them. -/
def capSufficient (I : CappedInstance nAgents nProjects) : Prop :=
  ∀ i : Agent nAgents, friendsBudget I i <= likedCap I i

def capRespecting (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  ∀ j, 0 <= x j ∧ x j <= I.cap j

def coalitionBudget (I : CappedInstance nAgents nProjects)
    (S : Finset (Agent nAgents)) : ℝ :=
  ∑ i in S, I.budget i

def weakCoreBlockingCoalition (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (S : Finset (Agent nAgents)) (z : Allocation I) : Prop :=
  S.Nonempty ∧
    capRespecting I z ∧
    (∑ j : Project nProjects, z j) <= coalitionBudget I S ∧
    ∀ i, i ∈ S -> utility I i x < utility I i z

def coreBlockingCoalition (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (S : Finset (Agent nAgents)) (z : Allocation I) : Prop :=
  S.Nonempty ∧
    capRespecting I z ∧
    (∑ j : Project nProjects, z j) <= coalitionBudget I S ∧
    (∀ i, i ∈ S -> utility I i x <= utility I i z) ∧
    ∃ i, i ∈ S ∧ utility I i x < utility I i z

def inWeakCore (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  ∀ S z, ¬ weakCoreBlockingCoalition I x S z

def inCore (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  ∀ S z, ¬ coreBlockingCoalition I x S z

def ParetoOptimal (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  ∀ y, allocationFeasible I y ->
    (∀ i, utility I i x <= utility I i y) ->
    (∃ i, utility I i x < utility I i y) ->
      False

def WeakParetoOptimal (I : CappedInstance nAgents nProjects)
    (x : Allocation I) : Prop :=
  ∀ y, allocationFeasible I y ->
    (∀ i, utility I i x < utility I i y) ->
      False

def addToProject (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (j : Project nProjects) (δ : ℝ) : Allocation I :=
  fun k => if k = j then x k + δ else x k

@[simp] theorem addToProject_self
    (I : CappedInstance nAgents nProjects)
    (x : Allocation I) (j : Project nProjects) (δ : ℝ) :
    addToProject I x j δ j = x j + δ := by
  simp [addToProject]

@[simp] theorem addToProject_ne
    (I : CappedInstance nAgents nProjects)
    (x : Allocation I) {j k : Project nProjects} (δ : ℝ)
    (hkj : k ≠ j) :
    addToProject I x j δ k = x k := by
  simp [addToProject, hkj]

theorem priceCost_addToProject
    (I : CappedInstance nAgents nProjects) (p : Prices I)
    (i : Agent nAgents) (x : Allocation I) (j : Project nProjects) (δ : ℝ) :
    priceCost I p i (addToProject I x j δ) =
      priceCost I p i x + p i j * δ := by
  classical
  unfold priceCost addToProject
  calc
    (∑ k : Project nProjects, p i k * (if k = j then x k + δ else x k))
        = ∑ k : Project nProjects,
            (p i k * x k + if k = j then p i j * δ else 0) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            by_cases hkj : k = j
            · subst k
              simp
              ring
            · simp [hkj]
    _ = ∑ k : Project nProjects, p i k * x k +
          ∑ k : Project nProjects, (if k = j then p i j * δ else 0) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ k : Project nProjects, p i k * x k + p i j * δ := by
            simp

theorem utility_addToProject
    (I : CappedInstance nAgents nProjects)
    (i : Agent nAgents) (x : Allocation I) (j : Project nProjects) (δ : ℝ) :
    utility I i (addToProject I x j δ) =
      utility I i x + I.valuation i j * δ := by
  classical
  unfold utility addToProject
  calc
    (∑ k : Project nProjects, I.valuation i k * (if k = j then x k + δ else x k))
        = ∑ k : Project nProjects,
            (I.valuation i k * x k + if k = j then I.valuation i j * δ else 0) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            by_cases hkj : k = j
            · subst k
              simp
              ring
            · simp [hkj]
    _ = ∑ k : Project nProjects, I.valuation i k * x k +
          ∑ k : Project nProjects, (if k = j then I.valuation i j * δ else 0) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ k : Project nProjects, I.valuation i k * x k + I.valuation i j * δ := by
            simp

theorem capRespecting_addToProject
    (I : CappedInstance nAgents nProjects) {x : Allocation I}
    (hx : capRespecting I x) {j : Project nProjects} {δ : ℝ}
    (hδ_nonneg : 0 <= δ) (hδ_cap : δ <= I.cap j - x j) :
    capRespecting I (addToProject I x j δ) := by
  intro k
  by_cases hkj : k = j
  · subst k
    simp [addToProject]
    constructor <;> linarith [(hx j).1, (hx j).2]
  · simp [addToProject, hkj, hx k]

theorem capRespecting_of_allocationFeasible
    (I : CappedInstance nAgents nProjects) {x : Allocation I}
    (hx : allocationFeasible I x) :
    capRespecting I x :=
  hx.1

theorem coalitionBudget_univ
    (I : CappedInstance nAgents nProjects) :
    coalitionBudget I Finset.univ = ∑ i : Agent nAgents, I.budget i := by
  simp [coalitionBudget]

theorem sum_priceCost_eq_sum_project_prices
    (I : CappedInstance nAgents nProjects) (p : Prices I)
    (S : Finset (Agent nAgents)) (z : Allocation I) :
    ∑ i in S, priceCost I p i z =
      ∑ j : Project nProjects, (∑ i in S, p i j) * z j := by
  simp [priceCost, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sum_priceCost_univ_le_total
    (I : CappedInstance nAgents nProjects) {x z : Allocation I}
    {p : Prices I}
    (_hp_nonneg : pricesNonnegative I p)
    (hz_nonneg : ∀ j, 0 <= z j)
    (hprofit : profitMaximizing I x p) :
    (∑ i : Agent nAgents, priceCost I p i z) <=
      ∑ j : Project nProjects, z j := by
  rw [sum_priceCost_eq_sum_project_prices I p Finset.univ z]
  refine Finset.sum_le_sum ?_
  intro j _hj
  have hsum : (∑ i in (Finset.univ : Finset (Agent nAgents)), p i j) <= 1 := by
    simpa using (hprofit j).1
  nlinarith [mul_le_mul_of_nonneg_right hsum (hz_nonneg j)]

theorem sum_priceCost_coalition_le_univ
    (I : CappedInstance nAgents nProjects) {z : Allocation I}
    {p : Prices I} (S : Finset (Agent nAgents))
    (hp_nonneg : pricesNonnegative I p)
    (hz_nonneg : ∀ j, 0 <= z j) :
    (∑ i in S, priceCost I p i z) <=
      ∑ i : Agent nAgents, priceCost I p i z := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
  intro i _hi_notin _hi_univ
  unfold priceCost
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp_nonneg i j) (hz_nonneg j)

theorem priceCost_gt_budget_of_strictly_better
    (I : CappedInstance nAgents nProjects) {x z : Allocation I}
    {p : Prices I} (hL : LindahlEquilibrium I x p)
    {i : Agent nAgents}
    (hzcap : capRespecting I z)
    (hbetter : utility I i x < utility I i z) :
    I.budget i < priceCost I p i z := by
  by_contra hnot
  have hcost : priceCost I p i z <= I.budget i := not_lt.mp hnot
  have hmax := hL.2.2.2.1 i z hzcap hcost
  linarith

theorem exists_pos_delta_for_project_increase
    {slack room price : ℝ} (hslack : 0 < slack) (hroom : 0 < room)
    (hprice_nonneg : 0 <= price) :
    ∃ δ : ℝ, 0 < δ ∧ δ <= room ∧ price * δ <= slack := by
  let δ := min (room / 2) (slack / (2 * (price + 1)))
  have hden_pos : 0 < 2 * (price + 1) := by positivity
  refine ⟨δ, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (div_pos hslack hden_pos)
  · exact (min_le_left _ _).trans (by linarith)
  · have hδ_le : δ <= slack / (2 * (price + 1)) := min_le_right _ _
    have hmul_le : price * δ <= price * (slack / (2 * (price + 1))) :=
      mul_le_mul_of_nonneg_left hδ_le hprice_nonneg
    have hprice_le : price / (2 * (price + 1)) <= 1 := by
      have : price <= 2 * (price + 1) := by nlinarith
      exact div_le_one_of_le₀ this hden_pos.le
    have htarget : price * (slack / (2 * (price + 1))) <= slack := by
      calc
        price * (slack / (2 * (price + 1)))
            = (price / (2 * (price + 1))) * slack := by
                field_simp [ne_of_gt hden_pos]
        _ <= 1 * slack := mul_le_mul_of_nonneg_right hprice_le hslack.le
        _ = slack := by ring
    exact hmul_le.trans htarget

theorem liked_project_capped_of_underspending
    (I : CappedInstance nAgents nProjects) {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p) {i : Agent nAgents}
    (hunder : priceCost I p i x < I.budget i) :
    ∀ j : Project nProjects, likedProject I i j -> x j = I.cap j := by
  intro j hliked
  by_contra hnot
  have hx_le_cap : x j <= I.cap j := (hL.1.1 j).2
  have hx_lt_cap : x j < I.cap j := lt_of_le_of_ne hx_le_cap hnot
  let slack := I.budget i - priceCost I p i x
  let room := I.cap j - x j
  have hslack : 0 < slack := by dsimp [slack]; linarith
  have hroom : 0 < room := by dsimp [room]; linarith
  rcases exists_pos_delta_for_project_increase
      hslack hroom (hL.2.1 i j) with ⟨δ, hδpos, hδroom, hδcost⟩
  let y := addToProject I x j δ
  have hycap : capRespecting I y :=
    capRespecting_addToProject I (capRespecting_of_allocationFeasible I hL.1)
      hδpos.le (by simpa [room] using hδroom)
  have hycost : priceCost I p i y <= I.budget i := by
    rw [show y = addToProject I x j δ by rfl, priceCost_addToProject]
    dsimp [slack] at hδcost
    linarith
  have hybetter : utility I i x < utility I i y := by
    rw [show y = addToProject I x j δ by rfl, utility_addToProject]
    have hmul_pos : 0 < I.valuation i j * δ := mul_pos hliked hδpos
    linarith
  have hmax := hL.2.2.2.1 i y hycap hycost
  linarith

theorem exists_project_price_pos_and_y_lt_of_priceCost_lt
    (I : CappedInstance nAgents nProjects) (p : Prices I)
    (i : Agent nAgents) (x y : Allocation I)
    (hp_nonneg : ∀ j, 0 <= p i j)
    (hcost : priceCost I p i y < priceCost I p i x) :
    ∃ j : Project nProjects, 0 < p i j ∧ y j < x j := by
  classical
  by_contra hnone
  have hterm :
      ∀ j : Project nProjects, p i j * x j <= p i j * y j := by
    intro j
    by_cases hp_pos : 0 < p i j
    · have hyx_not : ¬ y j < x j := by
        intro hyx
        exact hnone ⟨j, hp_pos, hyx⟩
      exact mul_le_mul_of_nonneg_left (not_lt.mp hyx_not) (hp_nonneg j)
    · have hp_zero : p i j = 0 := le_antisymm (not_lt.mp hp_pos) (hp_nonneg j)
      simp [hp_zero]
  have hcost_le : priceCost I p i x <= priceCost I p i y := by
    unfold priceCost
    exact Finset.sum_le_sum fun j _ => hterm j
  linarith

theorem inWeakCore_of_lindahl
    (I : CappedInstance nAgents nProjects) {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p) :
    inWeakCore I x := by
  intro S z hblock
  rcases hblock with ⟨hne, hzcap, hzbudget, hbetter⟩
  have hprice_gt :
      coalitionBudget I S < ∑ i in S, priceCost I p i z := by
    unfold coalitionBudget
    refine Finset.sum_lt_sum ?_ ?_
    · intro i hi
      exact le_of_lt
        (priceCost_gt_budget_of_strictly_better I hL hzcap (hbetter i hi))
    · rcases hne with ⟨i, hi⟩
      exact ⟨i, hi,
        priceCost_gt_budget_of_strictly_better I hL hzcap (hbetter i hi)⟩
  have hz_nonneg : ∀ j, 0 <= z j := fun j => (hzcap j).1
  have hcoal_le_univ :=
    sum_priceCost_coalition_le_univ I S hL.2.1 hz_nonneg
  have huniv_le_total :=
    sum_priceCost_univ_le_total I hL.2.1 hz_nonneg hL.2.2.2.2
  linarith

/- The cap-sufficiency implications require the paper's standing assumption
that every agent likes at least one project.  This assumption is kept explicit
because `CappedInstance` itself does not currently store it. -/

theorem priceCost_eq_budget_of_capSufficient
    (I : CappedInstance nAgents nProjects)
    (hcap : capSufficient I)
    (hagent_likes : ∀ i : Agent nAgents, ∃ j : Project nProjects, likedProject I i j)
    {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p)
    (hzr : zeroRespecting I x p) :
    ∀ i, priceCost I p i x = I.budget i := by
  -- This is the paper's Proposition `cap-sufficient implications`, part (i).
  -- It is intentionally stated as a theorem because it is the technical input
  -- for the strong core and Pareto consequences below.
  intro i
  have hle := hL.2.2.1 i
  by_contra hne
  have hlt : priceCost I p i x < I.budget i := lt_of_le_of_ne hle hne
  classical
  have hliked_capped :
      ∀ j : Project nProjects, likedProject I i j -> x j = I.cap j :=
    liked_project_capped_of_underspending I hL hlt
  have hfriend_self : friends I i i := by
    rcases hagent_likes i with ⟨j, hj⟩
    exact ⟨j, hj, hj⟩
  have hnonfriend_price_zero :
      ∀ f j, ¬ friends I i f -> likedProject I i j -> 0 < x j -> p f j = 0 := by
    intro f j hnotfriend hliked hxpos
    have hnotliked_f : ¬ likedProject I f j := by
      intro hf
      exact hnotfriend ⟨j, hliked, hf⟩
    have hval_zero : I.valuation f j = 0 := by
      exact le_antisymm (not_lt.mp hnotliked_f) (I.valuation_nonneg f j)
    exact hzr f j hval_zero hxpos
  have hlikedCap_le_price :
      likedCap I i <=
        ∑ f : Agent nAgents,
          if friends I i f then priceCost I p f x else 0 := by
    dsimp [likedCap]
    calc
      (∑ j : Project nProjects, if likedProject I i j then I.cap j else 0)
          <= ∑ j : Project nProjects,
              ∑ f : Agent nAgents,
                if friends I i f then p f j * x j else 0 := by
              refine Finset.sum_le_sum ?_
              intro j _hj
              by_cases hliked : likedProject I i j
              · have hxcap := hliked_capped j hliked
                have hxpos : 0 < x j := by
                  rw [hxcap]
                  exact I.cap_pos j
                have hsum_price : (∑ f : Agent nAgents, p f j) = 1 :=
                  (hL.2.2.2.2 j).2 hxpos
                have hproject_sum :
                    x j =
                      ∑ f : Agent nAgents,
                        if friends I i f then p f j * x j else 0 := by
                  calc
                    x j = (∑ f : Agent nAgents, p f j) * x j := by
                            rw [hsum_price]
                            ring
                    _ = ∑ f : Agent nAgents, p f j * x j := by
                            rw [Finset.sum_mul]
                    _ = ∑ f : Agent nAgents,
                          if friends I i f then p f j * x j else 0 := by
                            refine Finset.sum_congr rfl ?_
                            intro f _hf
                            by_cases hfriend : friends I i f
                            · simp [hfriend]
                            · have hpzero :=
                                hnonfriend_price_zero f j hfriend hliked hxpos
                              simp [hfriend, hpzero]
                simpa [hliked, hxcap] using le_of_eq hproject_sum
              · have hnonneg :
                    0 <=
                      ∑ f : Agent nAgents,
                        if friends I i f then p f j * x j else 0 := by
                  refine Finset.sum_nonneg ?_
                  intro f _hf
                  by_cases hfriend : friends I i f
                  · simp [hfriend,
                      mul_nonneg (hL.2.1 f j) (hL.1.1 j).1]
                  · simp [hfriend]
                simp [hliked, hnonneg]
      _ = ∑ f : Agent nAgents,
            ∑ j : Project nProjects,
              if friends I i f then p f j * x j else 0 := by
            rw [Finset.sum_comm]
      _ <= ∑ f : Agent nAgents,
            if friends I i f then priceCost I p f x else 0 := by
            refine Finset.sum_le_sum ?_
            intro f _hf
            by_cases hfriend : friends I i f
            · simp [hfriend]
              unfold priceCost
              refine Finset.sum_le_sum ?_
              intro j _hj
              by_cases _hliked : likedProject I i j
              · simp [hfriend]
              · simp [hfriend, mul_nonneg (hL.2.1 f j) (hL.1.1 j).1]
            · simp [hfriend]
  have hprice_lt_budget :
      (∑ f : Agent nAgents,
          if friends I i f then priceCost I p f x else 0) <
        friendsBudget I i := by
    dsimp [friendsBudget]
    refine Finset.sum_lt_sum ?_ ?_
    · intro f _hf
      by_cases hfriend : friends I i f
      · simp [hfriend, hL.2.2.1 f]
      · simp [hfriend]
    · exact ⟨i, Finset.mem_univ i, by simp [hfriend_self, hlt]⟩
  have hcap_i := hcap i
  linarith

theorem total_allocation_eq_total_budget_of_capSufficient
    (I : CappedInstance nAgents nProjects)
    (hcap : capSufficient I)
    (hagent_likes : ∀ i : Agent nAgents, ∃ j : Project nProjects, likedProject I i j)
    {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p)
    (hzr : zeroRespecting I x p) :
    (∑ j : Project nProjects, x j) = ∑ i : Agent nAgents, I.budget i := by
  have hspend := priceCost_eq_budget_of_capSufficient I hcap hagent_likes hL hzr
  calc
    (∑ j : Project nProjects, x j)
        = ∑ j : Project nProjects, (∑ i : Agent nAgents, p i j) * x j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            by_cases hxj : 0 < x j
            · rw [(hL.2.2.2.2 j).2 hxj]
              ring
            · have hx_nonpos : x j <= 0 := not_lt.mp hxj
              have hx_nonneg : 0 <= x j := (hL.1.1 j).1
              have hxzero : x j = 0 := le_antisymm hx_nonpos hx_nonneg
              simp [hxzero]
    _ = ∑ i : Agent nAgents, priceCost I p i x := by
            rw [← sum_priceCost_eq_sum_project_prices I p Finset.univ x]
    _ = ∑ i : Agent nAgents, I.budget i := by
            exact Finset.sum_congr rfl fun i _ => hspend i

theorem priceCost_ge_budget_of_capSufficient_of_utility_ge
    (I : CappedInstance nAgents nProjects)
    (hcap : capSufficient I)
    (hagent_likes : ∀ i : Agent nAgents, ∃ j : Project nProjects, likedProject I i j)
    {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p)
    (hzr : zeroRespecting I x p)
    {i : Agent nAgents} {y : Allocation I}
    (hycap : capRespecting I y)
    (huy : utility I i x <= utility I i y) :
    I.budget i <= priceCost I p i y := by
  by_contra hnot
  have hlt : priceCost I p i y < I.budget i := not_le.mp hnot
  have hmax := hL.2.2.2.1 i y hycap (le_of_lt hlt)
  have hspend := priceCost_eq_budget_of_capSufficient I hcap hagent_likes hL hzr i
  have hle : utility I i y <= utility I i x := hmax
  have hge : utility I i x <= utility I i y := huy
  have heq : utility I i x = utility I i y := le_antisymm hge hle
  have hcost_yx : priceCost I p i y < priceCost I p i x := by
    rw [hspend]
    exact hlt
  rcases exists_project_price_pos_and_y_lt_of_priceCost_lt
      I p i x y (hL.2.1 i) hcost_yx with ⟨j, hp_pos, hy_lt_x⟩
  have hx_pos : 0 < x j := lt_of_le_of_lt (hycap j).1 hy_lt_x
  have hval_pos : likedProject I i j := by
    by_contra hnotpos
    have hval_zero : I.valuation i j = 0 := by
      exact le_antisymm (not_lt.mp hnotpos) (I.valuation_nonneg i j)
    have hp_zero := hzr i j hval_zero hx_pos
    linarith
  let slack := I.budget i - priceCost I p i y
  let room := I.cap j - y j
  have hslack : 0 < slack := by dsimp [slack]; linarith
  have hroom : 0 < room := by
    dsimp [room]
    have hx_le_cap : x j <= I.cap j := (hL.1.1 j).2
    linarith
  rcases exists_pos_delta_for_project_increase
      hslack hroom (hL.2.1 i j) with ⟨δ, hδpos, hδroom, hδcost⟩
  let y' := addToProject I y j δ
  have hy'cap : capRespecting I y' :=
    capRespecting_addToProject I hycap hδpos.le (by simpa [room] using hδroom)
  have hy'cost : priceCost I p i y' <= I.budget i := by
    rw [show y' = addToProject I y j δ by rfl, priceCost_addToProject]
    dsimp [slack] at hδcost
    linarith
  have hy'_better_x : utility I i x < utility I i y' := by
    rw [show y' = addToProject I y j δ by rfl, utility_addToProject]
    rw [heq]
    have hmul_pos : 0 < I.valuation i j * δ := mul_pos hval_pos hδpos
    linarith
  have hmax_y' := hL.2.2.2.1 i y' hy'cap hy'cost
  linarith

theorem inCore_of_lindahl_of_capSufficient
    (I : CappedInstance nAgents nProjects)
    (hcap : capSufficient I)
    (hagent_likes : ∀ i : Agent nAgents, ∃ j : Project nProjects, likedProject I i j)
    {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p)
    (hzr : zeroRespecting I x p) :
    inCore I x := by
  intro S z hblock
  rcases hblock with ⟨_hne, hzcap, hzbudget, hweak, i0, hi0S, hstrict⟩
  have hprice_gt_i0 :
      I.budget i0 < priceCost I p i0 z :=
    priceCost_gt_budget_of_strictly_better I hL hzcap hstrict
  have hprice_gt :
      coalitionBudget I S < ∑ i in S, priceCost I p i z := by
    unfold coalitionBudget
    refine Finset.sum_lt_sum ?_ ?_
    · intro i hi
      exact priceCost_ge_budget_of_capSufficient_of_utility_ge
        I hcap hagent_likes hL hzr hzcap (hweak i hi)
    · exact ⟨i0, hi0S, hprice_gt_i0⟩
  have hz_nonneg : ∀ j, 0 <= z j := fun j => (hzcap j).1
  have hcoal_le_univ :=
    sum_priceCost_coalition_le_univ I S hL.2.1 hz_nonneg
  have huniv_le_total :=
    sum_priceCost_univ_le_total I hL.2.1 hz_nonneg hL.2.2.2.2
  linarith

theorem weakParetoOptimal_of_inWeakCore
    (I : CappedInstance nAgents nProjects) {x : Allocation I}
    [Nonempty (Agent nAgents)]
    (hweakCore : inWeakCore I x) :
    WeakParetoOptimal I x := by
  intro y hyfeas hbetter
  have hblock : weakCoreBlockingCoalition I x Finset.univ y := by
    refine ⟨?_, capRespecting_of_allocationFeasible I hyfeas, ?_, ?_⟩
    · exact Finset.univ_nonempty
    · simpa [coalitionBudget] using hyfeas.2
    · intro i _hi
      exact hbetter i
  exact hweakCore Finset.univ y hblock

theorem paretoOptimal_of_inCore
    (I : CappedInstance nAgents nProjects) {x : Allocation I}
    (hcore : inCore I x) :
    ParetoOptimal I x := by
  intro y hyfeas hweak hstrict
  rcases hstrict with ⟨i0, hstrict0⟩
  have hblock : coreBlockingCoalition I x Finset.univ y := by
    refine ⟨?_, capRespecting_of_allocationFeasible I hyfeas, ?_, ?_, ?_⟩
    · exact ⟨i0, by simp⟩
    · simpa [coalitionBudget] using hyfeas.2
    · intro i _hi
      exact hweak i
    · exact ⟨i0, by simp, hstrict0⟩
  exact hcore Finset.univ y hblock

theorem weakParetoOptimal_of_lindahl
    (I : CappedInstance nAgents nProjects) {x : Allocation I} {p : Prices I}
    [Nonempty (Agent nAgents)]
    (hL : LindahlEquilibrium I x p) :
    WeakParetoOptimal I x :=
  weakParetoOptimal_of_inWeakCore I (inWeakCore_of_lindahl I hL)

theorem paretoOptimal_of_lindahl_of_capSufficient
    (I : CappedInstance nAgents nProjects)
    (hcap : capSufficient I)
    (hagent_likes : ∀ i : Agent nAgents, ∃ j : Project nProjects, likedProject I i j)
    {x : Allocation I} {p : Prices I}
    (hL : LindahlEquilibrium I x p)
    (hzr : zeroRespecting I x p) :
    ParetoOptimal I x :=
  paretoOptimal_of_inCore I
    (inCore_of_lindahl_of_capSufficient I hcap hagent_likes hL hzr)

end
end ShmyrevCapped
end Lindahl
end Optlib
