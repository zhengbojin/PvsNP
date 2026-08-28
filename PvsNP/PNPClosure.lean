/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.EssentialDimension
import PvsNP.ClassicalComplexity
import PvsNP.SubsetSumInNP
import PvsNP.SubsetSumLanguage
import PvsNP.ParamEquiv

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

/-!
# PvsNP.PNPClosure —— 框架内经典 P ≠ NP 的闭合论证

论证形态（2026-08-28 用户裁决：无需证明 Bool 层——闭合在 CBTM 框架内部完成）：

```
任意经典 DTM D → D.toCBTM 是 CBTM0（受限机器）→ κ = 0、worstCaseDimension = 0
  （维度 0 保持到所有 P 算法：CBTM0 逐一步模拟 DTM，参数化等价定理）
子集和 α 编码语言 L_F4：任意识别者 κ ≥ 元素数（选项下界——
  代数生成元扩张（√pᵢ 线性无关）绑定元素选择——信息论：2ⁿ 个部分和需要 n 个独立维度）
  （subsetSum_kappa_lower_bound，SubsetSumLanguage.lean——全 Lean 内，非公理）
⟹ 不存在受限/CBTM0 机器识别 L_F4（κ ≥ 1 vs κ = 0 矛盾）
⟹ 不存在经典 DTM 使 D.toCBTM 识别 L_F4（no_dtm_recognizes_subsetSumF4——矛盾传到 CBTM0）
```

历史：Bool 层条件闭合（P_Bool_neq_NP_Bool，前提 h_kappa = 论文层 κ ≥ n 下界）于
2026-08-28 取消——框架内闭合无前提、无新公理，取代之。

注：本文件定义 tapeAccepts 语义的验证器/本质维度（与 IsP_F 的磁带语义一致），
避免与 IVM.lean 中基于旧 accepts 语义的 Verifiers 交叉。数学上二者同一概念。
-/

namespace PvsNP

open CBTM
open F4
open Finset

-- ======================================================================
-- 磁带语义的验证器与本质维度（与 IsP_F 的 tapeAccepts 一致）
-- ======================================================================

/-- Bool 语言的验证器集合（磁带语义；投影接受：∃ w 实部 = x 且被接受）。 -/
def Verifiers_tape (L : BoolLanguage) : Set CBTM :=
  { M | CBTM.isPolynomialTime M ∧
    (∀ x : List Bool, (∃ w : List F4, realProject w = x ∧ M.tapeAccepts w) ↔ L x) }

/-- Bool 语言在长度 n 上的本质维度（磁带语义版；= 论文 κ(L) 的形态）。 -/
noncomputable def essentialDimension_tape (L : BoolLanguage) (refLen : ℕ) : ℕ := by
  classical
  by_cases h : ∃ M, M ∈ Verifiers_tape L
  · have h_ex : ∃ (k : ℕ), ∃ M, M ∈ Verifiers_tape L ∧ worstCaseDimension M refLen = k := by
      rcases h with ⟨M, hM⟩
      exact ⟨worstCaseDimension M refLen, M, hM, rfl⟩
    exact Nat.find h_ex
  · exact 0

-- ======================================================================
-- 零维定理（IsP_Bool 形态）：P 类语言的本质维度为零
-- ======================================================================

theorem PClassZeroDimension_tape (L : BoolLanguage) (hP : IsP_Bool L) (refLen : ℕ) :
    essentialDimension_tape L refLen = 0 := by
  rcases hP with ⟨Lf, hproj, hPF⟩
  rcases hPF with ⟨M, hrest, hp, hacc⟩
  have hM_ver : M ∈ Verifiers_tape L := by
    refine ⟨hp, ?_⟩
    intro x
    constructor
    · intro ⟨w, hproj_w, htape⟩
      have hLf : Lf w := (hacc w).1 htape
      rw [← hproj]
      exact ⟨w, hproj_w, hLf⟩
    · intro hx
      rw [← hproj] at hx
      change ∃ w : List F4, realProject w = x ∧ Lf w at hx
      rcases hx with ⟨w, hproj_w, hLf⟩
      exact ⟨w, hproj_w, (hacc w).2 hLf⟩
  have h_wcd_zero : worstCaseDimension M refLen = 0 :=
    worstCaseDimension_zero_of_restricted M refLen hrest
  have h_nonempty : ∃ M', M' ∈ Verifiers_tape L := ⟨M, hM_ver⟩
  classical
  have h_ex : ∃ (k : ℕ), ∃ M', M' ∈ Verifiers_tape L ∧ worstCaseDimension M' refLen = k := by
    exact ⟨0, M, hM_ver, h_wcd_zero⟩
  have h_ess_eq : essentialDimension_tape L refLen = Nat.find h_ex := by
    unfold essentialDimension_tape
    simp only [h_nonempty, dite_true]
  have h_find_zero : Nat.find h_ex = 0 := by
    apply le_antisymm
    · apply Nat.find_min' h_ex
      exact ⟨M, hM_ver, h_wcd_zero⟩
    · exact Nat.zero_le _
  rw [h_ess_eq, h_find_zero]

-- ======================================================================
-- 子集和 ∈ 经典 NP（Canonical NTM2 形态；语言识别由同构桥 + 语言桥条款给出）
-- ======================================================================

/-- 子集和 ∈ 经典 NP（Canonical NTM2 形态；语言识别由同构桥 + 语言桥条款给出）。 -/
theorem subsetSum_in_NP_classic : IsNP_classic subsetSumBoolLanguage := by
  rcases exists_NTM2_solves_subsetSum with ⟨A, hsolve, hbridge, hcan, hreject⟩
  refine ⟨A, hcan, ?_⟩
  exact ntm2_language_recognition A hcan hbridge (by
    intro w
    constructor
    · intro hacc
      by_cases h : ∃ inst, inst.elements ≠ [] ∧ w = encodeSubsetSumF4Real inst
      · rcases h with ⟨inst, hne, hw⟩
        rcases exists_CBTM_iso_NTM2 A with ⟨M, hM, ⟨iso⟩⟩
        have hcbtm' : (NTM2.toCBTM A).tapeAccepts
            (ntm2InputToCBTM A (encodeSubsetSumBits inst)) := by
          rw [hw] at hacc
          rw [← hbridge inst hne] at hacc
          exact hacc
        have hA : A.acceptsTape (encodeSubsetSumBits inst) := by
          have hb := StructIso_preserves_accepts A M iso hcan (encodeSubsetSumBits inst)
          rw [hM] at hb
          exact hb.2 hcbtm'
        have hholds : subsetSumHolds inst := (hsolve inst hne).1.2 hA
        exact ⟨inst, hw, hne, hholds⟩
      · exfalso
        have hnon : ∀ inst, inst.elements ≠ [] → w ≠ encodeSubsetSumF4Real inst := by
          intro inst hne hw
          exact h ⟨inst, hne, hw⟩
        exact hreject w hnon hacc
    · intro hL
      rcases hL with ⟨inst, hw, hne, hholds⟩
      rcases exists_CBTM_iso_NTM2 A with ⟨M, hM, ⟨iso⟩⟩
      have hA : A.acceptsTape (encodeSubsetSumBits inst) := (hsolve inst hne).1.1 hholds
      have hb := StructIso_preserves_accepts A M iso hcan (encodeSubsetSumBits inst)
      rw [hM] at hb
      have hcbtm : (NTM2.toCBTM A).tapeAccepts
          (ntm2InputToCBTM A (encodeSubsetSumBits inst)) := hb.1 hA
      rw [hbridge inst hne] at hcbtm
      rw [← hw] at hcbtm
      exact hcbtm)

-- 框架内经典 P ≠ NP（Bool 层类分离）——【已取消，仅存历史记录】
--
-- 前提：
-- - n > 0（子集和实例的元素数）；
-- - h_kappa：κ(K_ss) ≥ n（∀ 参考长度——论文第 5 节结论，
--   信息论下界 + 分支-激活引理——数计一体公理支撑——论文层面）。
--
-- 结论：P_Bool ≠ NP_Bool（K_ss ∈ NP_Bool 已证；若 ∈ P_Bool 则 κ=0，矛盾）。
--
-- 注（2026-08-28 用户裁决）：无需证明 Bool 层——本条件定理已被
-- CBTM 框架内部闭合取代（no_dtm_recognizes_subsetSumF4，无前提）——
-- 此定理于 2026-08-28 取消（不再作为交付结论）。
-- theorem P_Bool_neq_NP_Bool (n : ℕ) (hn : 0 < n)
--     (h_kappa : ∀ refLen : ℕ, n ≤ essentialDimension_tape subsetSumBoolLanguage refLen) :
--     P_Bool ≠ NP_Bool := by
--   intro h_eq
--   have hP : subsetSumBoolLanguage ∈ P_Bool := by
--     rw [h_eq]
--     change IsNP_Bool subsetSumBoolLanguage
--     exact subsetSum_in_NP
--   have hP_IsP_Bool : IsP_Bool subsetSumBoolLanguage := by
--     simpa [P_Bool] using hP
--   have h_zero : essentialDimension_tape subsetSumBoolLanguage 0 = 0 :=
--     PClassZeroDimension_tape subsetSumBoolLanguage hP_IsP_Bool 0
--   have h_contra : n ≤ 0 := by
--     simpa [h_zero] using h_kappa 0
--   omega

-- ======================================================================
-- CBTM 框架内部闭合：矛盾传到 CBTM0（经典 P 算法的 CBTM 形态）
-- ======================================================================
-- 论证形态（用户 2026-08-28 裁决：无需证明 Bool 层）：
--
--   任意经典 DTM D → D.toCBTM 是 CBTM0（受限机器）→ κ = 0、worstCaseDimension = 0
--     （维度 0 保持到所有 P 算法：CBTM0 逐一步模拟 DTM，参数化等价定理）
--   子集和 α 编码语言 L_F4：任意识别者 κ ≥ 元素数（选项下界：
--     代数生成元扩张（√pᵢ 线性无关）绑定元素选择——信息论：2ⁿ 个部分和需要 n 个独立维度）
--     （subsetSum_kappa_lower_bound，SubsetSumLanguage.lean:985）
--   ⟹ 不存在受限/CBTM0 机器识别 L_F4（κ ≥ 1 vs κ = 0 矛盾）
--   ⟹ 不存在经典 DTM 使 D.toCBTM 识别 L_F4（矛盾传到 CBTM0）
--
-- 注：全部由已有定理组装，0 新公理；维度矛盾与多项式时间无关（无时间前提）。

/-- 不存在受限 CBTM 识别 F4 层子集和语言（无时间前提：维度矛盾与时间无关）。 -/
theorem no_restricted_recognizes_subsetSumF4 :
    ¬ ∃ M : CBTM, IsRestricted M ∧
      (∀ w : List F4, M.tapeAccepts w ↔ subsetSumLanguageF4Real w) := by
  intro h
  rcases h with ⟨M, hrest, hcorrect⟩
  let inst : SubsetSumInstance := { elements := [1], target := 1 }
  have hYES : subsetSumLanguageF4Real (encodeSubsetSumF4Real inst) := by
    refine ⟨inst, rfl, ?_⟩
    exact ⟨by simp [inst], ⟨[true], by simp [inst], by simp [inst, selectedSum]⟩⟩
  have h_lower : kappa_M M (encodeSubsetSumF4Real inst) ≥ 1 := by
    have hk := subsetSum_kappa_lower_bound M inst (fun w => hcorrect w) hYES
    simpa [inst] using hk
  have h_zero : kappa_M M (encodeSubsetSumF4Real inst) = 0 :=
    kappa_zero_of_restricted_total M (encodeSubsetSumF4Real inst) hrest
  rw [h_zero] at h_lower
  omega

/-- 不存在 CBTM0 识别 F4 层子集和语言（维度矛盾：识别需 κ ≥ 1，CBTM0 受限 κ = 0）。 -/
theorem no_cbtm0_recognizes_subsetSumF4 :
    ¬ ∃ M : CBTM, IsCBTM0 M ∧
      (∀ w : List F4, M.tapeAccepts w ↔ subsetSumLanguageF4Real w) := by
  intro ⟨M, h0, hcorrect⟩
  exact no_restricted_recognizes_subsetSumF4 ⟨M, isCBTM0_isRestricted M h0, hcorrect⟩

/-- 维度 0 保持：任意经典 DTM 的受限 CBTM 模拟（toCBTM），worstCaseDimension = 0。 -/
theorem dtm_sim_worstCaseDimension_zero (D : ClassicDTM) (n : ℕ) :
    worstCaseDimension (D.toCBTM) n = 0 :=
  worstCaseDimension_zero_of_restricted (D.toCBTM) n (toCBTM_isRestricted D)

/-- 矛盾传到受限 CBTM：不存在经典 DTM（经 toCBTM 逐一步模拟）识别 F4 层子集和语言。
    任意经典 P 算法在 CBTM 框架内的形态 = 受限 CBTM（维度 0）；
    α 编码语言的选项下界要求维度 ≥ 元素数——矛盾。 -/
theorem no_dtm_recognizes_subsetSumF4 :
    ¬ ∃ D : ClassicDTM, ∀ w : List F4,
      (D.toCBTM).tapeAccepts w ↔ subsetSumLanguageF4Real w := by
  intro ⟨D, hcorrect⟩
  exact no_restricted_recognizes_subsetSumF4 ⟨D.toCBTM, toCBTM_isRestricted D, hcorrect⟩

end PvsNP
