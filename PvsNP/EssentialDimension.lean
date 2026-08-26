/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM

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


namespace PvsNP

open CBTM
open IVM
open Set
open F4
open Finset

-- ======================================================================
-- 所有长度为 n 的 F4 字符串集合
-- ======================================================================

def allLists : ℕ → Finset (List F4)
  | 0 => {[]}
  | n+1 => (Finset.univ : Finset F4) ×ˢ (allLists n) |>.image (fun (a, xs) => a :: xs)

theorem mem_allLists_iff_length (n : ℕ) (x : List F4) :
    x ∈ allLists n ↔ x.length = n := by
  induction n generalizing x with
  | zero =>
    simp [allLists]
  | succ n ih =>
    rw [allLists]
    constructor
    · intro h
      rcases Finset.mem_image.1 h with ⟨⟨a, xs⟩, hmem, rfl⟩
      rw [Finset.mem_product] at hmem
      rcases hmem with ⟨ha, hxs⟩
      have hxs_len : xs.length = n := (ih xs).mp hxs
      simp [hxs_len]
    · intro hlen
      cases x with
      | nil => simp at hlen
      | cons a xs =>
        have hxs_len : xs.length = n := by
          simpa [add_comm] using hlen
        apply Finset.mem_image.mpr
        refine ⟨(a, xs), ?_, rfl⟩
        rw [Finset.mem_product]
        exact ⟨Finset.mem_univ _, (ih xs).mpr hxs_len⟩

-- ======================================================================
-- 受限机器的 kappa 恒为零（推广版）
-- ======================================================================

lemma kappa_zero_of_restricted_total (M : CBTM) (x : List F4)
    (h_rest : IsRestricted M) : kappa_M M x = 0 :=
  kappa_zero_of_restricted M x h_rest

-- ======================================================================
-- 最坏情况维度
-- ======================================================================

noncomputable def worstCaseDimension (M : CBTM) (n : ℕ) : ℕ :=
  (allLists n).sup (fun x => kappa_M M x)


theorem worstCaseDimension_zero_of_restricted (M : CBTM) (n : ℕ)
    (h_rest : IsRestricted M) : worstCaseDimension M n = 0 := by
  unfold worstCaseDimension
  refine le_antisymm ?_ (Nat.zero_le _)
  apply Finset.sup_le
  intro x hx
  exact (kappa_zero_of_restricted_total M x h_rest).le

-- ======================================================================
-- 本质维度
-- ======================================================================

noncomputable def essentialDimension (L : Language) (refLen : ℕ) : ℕ := by
  classical
  by_cases h : ∃ M, M ∈ Verifiers L
  · have h_ex : ∃ (k : ℕ), ∃ M, M ∈ Verifiers L ∧ worstCaseDimension M refLen = k := by
      rcases h with ⟨M, hM⟩
      exact ⟨worstCaseDimension M refLen, M, hM, rfl⟩
    exact Nat.find h_ex
  · exact 0

theorem essentialDimension_spec (L : Language) (refLen : ℕ)
    (h_nonempty : ∃ M, M ∈ Verifiers L) :
    ∃ M, M ∈ Verifiers L ∧ worstCaseDimension M refLen = essentialDimension L refLen := by
  classical
  have h_ex : ∃ (k : ℕ), ∃ M, M ∈ Verifiers L ∧ worstCaseDimension M refLen = k := by
    rcases h_nonempty with ⟨M, hM⟩
    exact ⟨worstCaseDimension M refLen, M, hM, rfl⟩
  have h_ess_eq : essentialDimension L refLen = Nat.find h_ex := by
    unfold essentialDimension
    simp only [h_nonempty, dite_true]
  rw [h_ess_eq]
  exact Nat.find_spec h_ex

-- ======================================================================
-- P 类语言的本质维度为零
-- ======================================================================

theorem PClassZeroDimension (L : Language) (hP : IsP L) (refLen : ℕ) :
    essentialDimension L refLen = 0 := by
  rcases hP.exists_restricted with ⟨M, hrest, hp, hacc⟩
  have hM_ver : M ∈ Verifiers L := ⟨hp, hacc⟩
  have h_wcd_zero : worstCaseDimension M refLen = 0 :=
    worstCaseDimension_zero_of_restricted M refLen hrest
  have h_nonempty : ∃ M', M' ∈ Verifiers L := ⟨M, hM_ver⟩
  classical
  have h_ex : ∃ (k : ℕ), ∃ M', M' ∈ Verifiers L ∧ worstCaseDimension M' refLen = k := by
    exact ⟨0, M, hM_ver, h_wcd_zero⟩
  have h_ess_eq : essentialDimension L refLen = Nat.find h_ex := by
    unfold essentialDimension
    simp only [h_nonempty, dite_true]
  have h_find_zero : Nat.find h_ex = 0 := by
    apply le_antisymm
    · apply Nat.find_min' h_ex
      exact ⟨M, hM_ver, h_wcd_zero⟩
    · exact Nat.zero_le _
  rw [h_ess_eq, h_find_zero]

end PvsNP
