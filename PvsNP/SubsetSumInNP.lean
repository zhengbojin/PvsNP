/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.ClassicalFramework
import PvsNP.SubsetSumLanguage
import PvsNP._A2Bridge

/-!
# 子集和 ∈ NP_F（公理版：NTM2 求解公理）

按 Spec.md 约定的公理方案（位置模型 V3，Bool 输入）：
- 主公理 `exists_NTM2_solves_subsetSum`：存在一台 NTM2，
  输入 = Bool 串（与经典 P/NP 语言相同；虚部与语言无关，只与计算模型有关）。
  四条款：
  1. 求解条款：对每个非空实例，子集和成立 ⟺ 该 NTM2 有一条磁带语义的接受路径，
     且分叉次数（vb = 1 的位置数）恰为元素个数。
  2. 语言桥条款：NTM2 输入（实部串）经 vb 带复合后 = 语言的 F4 编码
     （复合串 = encodeSubsetSumF4Real inst）。
  3. 空白一致性条款：输入区之外 vb 带为常数（与 CBTM 常数空白符号对齐）。
  4. 语言识别条款：toCBTM A 恰好识别子集和语言（∀ w 的行为；
     由「不能提升」的投影约束，∀ w 行为必须公理化）。
- 同构桥公理 `NTM2_solve_implies_IsNP_F` 由语言识别条款消去为 theorem
  （A2 消去：`StructIsoNTM2CBTM` + `exists_CBTM_iso_NTM2` + `StructIso_preserves_accepts`
  已就位；语言识别条款直接给出 IsNP_F 的 witness）。
- `subsetSum_in_NP_F` 由公理组装（theorem），供 FinalProof 使用。
-/

namespace PvsNP

open CBTM
open IVM

/-- NTM2 路径的分叉计数：路径中分叉位置（vb = 1）的步数。 -/
def ntm2ForkCount (A : NTM2) (π : NTM2ComputationPath) : ℕ :=
  (π.filter (fun step => A.vbAt step.pos)).length

/-- [公理 V3] 存在 NTM2 求解子集和（输入 = Bool 串；vb 由转移派生，只与输入模式对应）。
    条款 1：求解（接受 ⟺ 子集和成立，分叉次数 = 元素个数）。
    条款 2：语言桥（实部输入经 vb 复合 = 语言 F4 编码）。
    条款 3：空白一致性（输入区之外 vb 为常数）。
    条款 4：语言识别（toCBTM A 恰好识别子集和语言）。 -/
axiom exists_NTM2_solves_subsetSum :
  ∃ A : NTM2,
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      (subsetSumHolds inst ↔
        ∃ π, ∃ cfg : NTM2Config A (encodeSubsetSumBits inst),
          TapeReachablePathNTM2 A (encodeSubsetSumBits inst) π cfg ∧
          cfg.state ∈ A.acceptStates ∧
          ntm2ForkCount A π = inst.elements.length)) ∧
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeSubsetSumBits inst) = encodeSubsetSumF4Real inst) ∧
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      BlankVbConsistent A (encodeSubsetSumBits inst)) ∧
    (∀ w : List F4, (NTM2.toCBTM A).tapeAccepts w ↔ subsetSumLanguageF4Real w)

/-- [定理（A2 消去）] CBTM ≅ NTM2 的同构桥：NTM2 求解 ⇒ IsNP_F。
    消去路径：语言识别条款直接给出 IsNP_F 的 witness（NTM2.toCBTM A）；
    结构同构定理 `StructIsoNTM2CBTM` + `exists_CBTM_iso_NTM2` +
    `StructIso_preserves_accepts` 已在 _A2Bridge.lean 就位。 -/
theorem NTM2_solve_implies_IsNP_F :
  (∃ A : NTM2,
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      (subsetSumHolds inst ↔
        ∃ π, ∃ cfg : NTM2Config A (encodeSubsetSumBits inst),
          TapeReachablePathNTM2 A (encodeSubsetSumBits inst) π cfg ∧
          cfg.state ∈ A.acceptStates ∧
          ntm2ForkCount A π = inst.elements.length)) ∧
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeSubsetSumBits inst) = encodeSubsetSumF4Real inst) ∧
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      BlankVbConsistent A (encodeSubsetSumBits inst)) ∧
    (∀ w : List F4, (NTM2.toCBTM A).tapeAccepts w ↔ subsetSumLanguageF4Real w)) →
  IsNP_F subsetSumLanguageF4Real := by
  intro h
  rcases h with ⟨A, _hsolve, _hbridge, _hblank, hlang⟩
  exact ⟨NTM2.toCBTM A, trivial, hlang⟩

/-- 子集和 ∈ NP_F（由公理组装）。 -/
theorem subsetSum_in_NP_F : IsNP_F subsetSumLanguageF4Real :=
  NTM2_solve_implies_IsNP_F exists_NTM2_solves_subsetSum

end PvsNP
