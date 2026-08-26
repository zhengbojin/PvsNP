/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



/-
形式化：互异素数的平方根在 ℚ 上线性无关。

Mathlib 未直接形式化该结果（仅有个体素数的 `Nat.Prime.irrational_sqrt`），本文件给出证明。

证明方法（迹配对）：设 K = ℚ(√p₁,…,√p_m)。核心事实是（`trace_eq_finrank_mul_minpoly_nextCoeff`）
  - 对 i ≠ j：Tr_{K/ℚ}(√p_i · √p_j) = 0（minpoly 为 X² − p_i p_j，次高项系数为 0）；
  - Tr_{K/ℚ}(p_j) = [K:ℚ]·p_j。
若 Σ c_i √p_i = 0，则 0 = Tr(√p_j · Σ c_i √p_i) = c_j·[K:ℚ]·p_j，故 c_j = 0。
-/

import Mathlib
import PvsNP.Basic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false
set_option linter.unusedFintypeInType false

namespace PvsNP

open Polynomial
open scoped IntermediateField

-- ============================================================================
-- 基础：非平方正整数 d 的平方根的最小多项式为 X² − d
-- ============================================================================

/-- 对非平方正整数 d，minpoly ℚ (√d) = X² − C d。 -/
lemma minpoly_sqrt_natCast_of_not_isSquare (d : ℕ) (hd : ¬IsSquare d) :
    minpoly ℚ (Real.sqrt (d : ℝ)) = X ^ 2 - C (d : ℚ) := by
  let x : ℝ := Real.sqrt (d : ℝ)
  have hmonic : (X ^ 2 - C (d : ℚ)).Monic :=
    monic_X_pow_sub_C (d : ℚ) (by norm_num : (2 : ℕ) ≠ 0)
  have haeval : aeval x (X ^ 2 - C (d : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C]
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  refine (minpoly.unique ℚ x hmonic haeval (fun q hq_monic hq_aeval => ?_)).symm
  have hdeg : (X ^ 2 - C (d : ℚ)).degree ≤ q.degree := by
    rw [degree_eq_natDegree hmonic.ne_zero, degree_eq_natDegree hq_monic.ne_zero]
    rw [natDegree_X_pow_sub_C]
    exact_mod_cast (le_of_not_gt (by
      intro hlt
      have hq_deg : q.natDegree = 0 ∨ q.natDegree = 1 := by omega
      have hIrrat : Irrational x := irrational_sqrt_natCast_iff.mpr hd
      rcases hq_deg with h0 | h1
      · have hq1 : q = 1 := hq_monic.natDegree_eq_zero.mp h0
        rw [hq1] at hq_aeval
        simp at hq_aeval
      · rcases Polynomial.natDegree_eq_one.mp h1 with ⟨a, ha_ne, b, hq_eq⟩
        have ha1 : a = 1 := by
          have hcoeff : q.coeff 1 = 1 := by
            rw [Polynomial.Monic, Polynomial.leadingCoeff] at hq_monic
            simpa [h1] using hq_monic
          rw [← hq_eq] at hcoeff
          simpa using hcoeff
        subst ha1
        have hq_aeval' : aeval x (X + C b) = 0 := by
          rw [← hq_eq] at hq_aeval
          simpa using hq_aeval
        have hx : x = -b := by
          rw [map_add, aeval_X, aeval_C] at hq_aeval'
          simpa [add_eq_zero_iff_eq_neg] using hq_aeval'
        exact hIrrat ⟨-b, by exact_mod_cast hx.symm⟩
    ))
  exact hdeg

-- ============================================================================
-- 辅助：互异素数乘积非平方
-- ============================================================================

/-- 互异素数 p、q 的乘积 p·q 不是平方数。 -/
lemma not_isSquare_mul_of_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : ¬IsSquare (p * q) := by
  rintro ⟨m, hm⟩
  have hp_dvd_m : p ∣ m := by
    apply hp.dvd_of_dvd_pow
    rw [sq]
    rw [← hm]
    exact dvd_mul_right p q
  rcases hp_dvd_m with ⟨k, hk⟩
  have h_q : q = p * k * k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * q = m * m := by rw [hm]
      _ = (p * k) * (p * k) := by rw [hk]
      _ = p * (p * k * k) := by ring
  have hp_dvd_q : p ∣ q := ⟨k * k, by rw [h_q]; ring⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hp_dvd_q)

-- ============================================================================
-- 迹引理
-- ============================================================================

/-- p ∈ ℚ 作为域元素时，其迹 = finrank · p。 -/
lemma trace_algebraMap_eq_finrank_mul {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
    (r : ℚ) :
    Algebra.trace ℚ K ((algebraMap ℚ K) r) = (Module.finrank ℚ K) • r := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff ℚ ((algebraMap ℚ K) r)]
  rw [minpoly.eq_X_sub_C K r]
  rw [nextCoeff_X_sub_C]
  have hbot : ℚ⟮(algebraMap ℚ K) r⟯ = ⊥ := by
    rw [IntermediateField.adjoin_eq_bot_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact IntermediateField.mem_bot.mpr ⟨r, rfl⟩
  have hfinrank : Module.finrank ℚ⟮(algebraMap ℚ K) r⟯ K = Module.finrank ℚ K := by
    rw [hbot]
    have h := Module.finrank_mul_finrank ℚ (⊥ : IntermediateField ℚ K) K
    rw [IntermediateField.finrank_bot] at h
    simpa using h.symm
  rw [hfinrank]
  norm_num [nsmul_eq_mul]

/-- 对互异素数 p、q，Tr_{K/ℚ}(√p·√q) = 0（√p、√q ∈ K）。 -/
lemma trace_sqrt_mul_sqrt_eq_zero {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp_mem : Real.sqrt (p : ℝ) ∈ K) (hq_mem : Real.sqrt (q : ℝ) ∈ K) :
    Algebra.trace ℚ K
      (⟨Real.sqrt (p : ℝ), hp_mem⟩ * ⟨Real.sqrt (q : ℝ), hq_mem⟩) = 0 := by
  let x : K := ⟨Real.sqrt (p : ℝ), hp_mem⟩ * ⟨Real.sqrt (q : ℝ), hq_mem⟩
  rw [trace_eq_finrank_mul_minpoly_nextCoeff ℚ x]
  have hx_val : (x : ℝ) = Real.sqrt ((p * q : ℕ) : ℝ) := by
    change Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) = Real.sqrt ((p * q : ℕ) : ℝ)
    rw [← Real.sqrt_mul (Nat.cast_nonneg p) (q : ℝ)]
    norm_num
  have hminpoly : minpoly ℚ x = X ^ 2 - C (p * q : ℚ) := by
    have h := minpoly.algebraMap_eq (A := ℚ) (B := ↥K) (B' := ℝ) (Subtype.coe_injective) x
    rw [← h]
    change minpoly ℚ ((x : ℝ)) = X ^ 2 - C (p * q : ℚ)
    rw [hx_val]
    simpa [Nat.cast_mul] using
      minpoly_sqrt_natCast_of_not_isSquare (p * q) (not_isSquare_mul_of_primes hp hq hpq)
  rw [hminpoly]
  have hnext : (X ^ 2 - C (p * q : ℚ)).nextCoeff = 0 := by
    rw [nextCoeff, Polynomial.natDegree_X_pow_sub_C]
    norm_num
  rw [hnext]
  simp

-- ============================================================================
-- 主定理（有限版本）
-- ============================================================================

/-- 有限个互异素数的平方根在 ℚ 上线性无关。 -/
theorem primeSqrt_Q_linearIndependent_finite {ι : Type} [Fintype ι]
    (f : ι → ℕ) (hf : ∀ i, Nat.Prime (f i)) (hf_inj : Function.Injective f) :
    LinearIndependent ℚ (fun i : ι => (Real.sqrt (f i : ℝ))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  classical
  let S : Set ℝ := {x | ∃ i : ι, x = Real.sqrt (f i : ℝ)}
  let K : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ S
  have hFD : FiniteDimensional ℚ K := by
    let t : ι → IntermediateField ℚ ℝ := fun i => IntermediateField.adjoin ℚ {Real.sqrt (f i : ℝ)}
    have hi : ∀ i, IsIntegral ℚ (Real.sqrt (f i : ℝ)) := by
      intro i
      refine ⟨X ^ 2 - C (f i : ℚ), monic_X_pow_sub_C (f i : ℚ) (by norm_num : (2 : ℕ) ≠ 0), ?_⟩
      simp [Polynomial.aeval_def, Real.sq_sqrt (Nat.cast_nonneg (f i))]
    have hsup : K = ⨆ i : ι, t i := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        rcases hx with ⟨i, rfl⟩
        exact le_iSup t i (IntermediateField.mem_adjoin_simple_self ℚ (Real.sqrt (f i : ℝ)))
      · apply iSup_le
        intro i
        rw [IntermediateField.adjoin_le_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact IntermediateField.subset_adjoin ℚ S (show Real.sqrt (f i : ℝ) ∈ S from ⟨i, rfl⟩)
    rw [hsup]
    letI : ∀ i, FiniteDimensional ℚ (t i) := fun i => IntermediateField.adjoin.finiteDimensional (hi i)
    exact IntermediateField.finiteDimensional_iSup_of_finite
  haveI : FiniteDimensional ℚ K := hFD
  have h_sqrt_mem : ∀ i, Real.sqrt (f i : ℝ) ∈ K := fun i =>
    IntermediateField.subset_adjoin ℚ S (show Real.sqrt (f i : ℝ) ∈ S from ⟨i, rfl⟩)
  let T := Algebra.trace ℚ K
  -- 迹配对核心：T(√(f j) · Σ g i • √(f i)) = g j · [K:ℚ] · f j
  have h_sum_zero : (∑ i, g i • (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K)) = 0 := by
    apply Subtype.ext
    simpa using hg
  have h_trace : T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ *
      (∑ i, g i • (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K))) = 0 := by
    rw [h_sum_zero]
    simp
  have h_expand : T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ *
      (∑ i, g i • (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K))) =
      ∑ i, g i • T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ *
        (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K)) := by
    rw [Finset.mul_sum]
    rw [map_sum]
    simp only [LinearMap.map_smul, mul_smul_comm]
  rw [h_expand] at h_trace
  have h_sep : (∑ i, g i • T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ *
        (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K))) =
      g j • (Module.finrank ℚ K • (f j : ℚ)) := by
    have hsq : ⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ * (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ : K) =
        (algebraMap ℚ K) (f j : ℚ) := by
      apply Subtype.ext
      change Real.sqrt (f j : ℝ) * Real.sqrt (f j : ℝ) = (f j : ℝ)
      rw [← sq]
      rw [Real.sq_sqrt (Nat.cast_nonneg (f j))]
    have hzero_non_j : ∀ i, i ≠ j → T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ *
        (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K)) = 0 := by
      intro i hij
      have hfij : f i ≠ f j := by
        intro h
        exact hij (hf_inj h)
      rw [trace_sqrt_mul_sqrt_eq_zero (hf j) (hf i) hfij.symm (h_sqrt_mem j) (h_sqrt_mem i)]
    classical
    calc
      (∑ i, g i • T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ * (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K)))
          = g j • T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ * (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ : K))
              + ∑ i ∈ Finset.univ.erase j,
                g i • T (⟨Real.sqrt (f j : ℝ), h_sqrt_mem j⟩ * (⟨Real.sqrt (f i : ℝ), h_sqrt_mem i⟩ : K)) := by
                rw [← Finset.sum_erase_add (s := Finset.univ) (a := j) (h := by simp)]
                rw [add_comm]
      _ = g j • (Module.finrank ℚ K • (f j : ℚ)) + 0 := by
            congr 1
            · rw [hsq]
              rw [trace_algebraMap_eq_finrank_mul (f j : ℚ)]
            · apply Finset.sum_eq_zero
              intro i hi
              have hij : i ≠ j := by simpa using (Finset.mem_erase.mp hi).1
              rw [hzero_non_j i hij]
              simp
      _ = g j • (Module.finrank ℚ K • (f j : ℚ)) := by simp
  rw [h_sep] at h_trace
  have h_gj : g j • (Module.finrank ℚ K • (f j : ℚ)) = 0 := h_trace
  have h_prod_ne : (Module.finrank ℚ K • (f j : ℚ)) ≠ 0 := by
    rw [nsmul_eq_mul]
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
    · exact_mod_cast (Nat.Prime.ne_zero (hf j))
  exact smul_eq_zero.mp h_gj |>.resolve_right h_prod_ne

-- ============================================================================
-- 主定理（无限版本）
-- ============================================================================

/-- 素数平方根族 {√p : p 素数} 在 ℚ 上线性无关。 -/
theorem primeSqrt_Q_linearIndependent :
    LinearIndependent ℚ (fun p : {p : ℕ // Nat.Prime p} => (Real.sqrt (p : ℝ))) := by
  rw [linearIndependent_iff]
  intro l hl
  classical
  ext p
  by_cases hp_mem : p ∈ l.support
  · let s : Finset {p : ℕ // Nat.Prime p} := l.support
    let f : ↥s → ℕ := fun i => i.1.1
    have hf : ∀ i, Nat.Prime (f i) := fun i => i.1.2
    have hf_inj : Function.Injective f := by
      intro i j h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hfin := primeSqrt_Q_linearIndependent_finite f hf hf_inj
    let g : ↥s → ℚ := fun i => l i.1
    have hg : (∑ i : ↥s, g i • (Real.sqrt (f i : ℝ))) = 0 := by
      simp only [g, f]
      change (∑ i ∈ (Finset.univ : Finset ↥s), l i.1 • (Real.sqrt (i.1.1 : ℝ))) = 0
      rw [Finset.univ_eq_attach s]
      rw [Finset.sum_attach s (fun x : {p : ℕ // Nat.Prime p} => l x • Real.sqrt (x.1 : ℝ))]
      simpa [s, Finsupp.sum, Finsupp.linearCombination] using hl
    have hg_zero := (Fintype.linearIndependent_iff.mp hfin) g hg
    have : g ⟨p, hp_mem⟩ = 0 := hg_zero ⟨p, hp_mem⟩
    simpa [g] using this
  · simpa using (Finsupp.mem_support_iff.not.mp hp_mem)

end PvsNP
