/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.ClassicalFramework
import PvsNP.SubsetSumLanguage

/-!
# 子集和 ∈ NP_F（公理版：NTM2 求解公理）

按 Spec.md 约定的公理方案（位置模型 V2）：
- 主公理 `exists_NTM2_solves_subsetSum`：存在一台 NTM2，
  在 n（= 元素个数）次分叉后求解子集和问题（磁带语义 acceptsTape，
  与 CBTM/DTM 对齐；输入 = 直接 F4 编码，虚部 = vb 带，语言桥恒等）。
- 同构桥公理 `NTM2_solve_implies_IsNP_F`：CBTM ≅ NTM2 的同构桥
  （NTM2 求解 ⇒ IsNP_F）；该桥最终版本以结构同构定理
  `StructIsoNTM2CBTM` + `exists_CBTM_iso_NTM2` + 接受保持定理
  （`StructIso_preserves_accepts`）替代。
- `subsetSum_in_NP_F` 由两公理组装（theorem），供 FinalProof 使用。

约定（V1.2/V1.4/V2）：在公理版下不构造具体 CBTM；最终版本以
CBTM ≅ NTM2 的同构 + 具体验证器把两公理消去为 theorem。
-/

namespace PvsNP

open CBTM
open IVM

/-- NTM2 路径的分叉计数：路径中分叉位置（vb = true）的步数。 -/
def ntm2ForkCount (A : NTM2) (π : NTM2ComputationPath) : ℕ :=
  (π.filter (fun step => A.vb step.pos)).length

/-- [公理 V2] 存在 NTM2 在 n（= 元素个数）次分叉后求解子集和：
    对每个非空实例，子集和成立当且仅当该 NTM2 有一条磁带语义的接受路径，
    且该路径的分叉次数恰为元素个数。输入 = encodeSubsetSumF4Real inst
    （虚部 = vb 带，语言桥恒等，无需额外编码转换）。 -/
axiom exists_NTM2_solves_subsetSum :
  ∃ A : NTM2, ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
    (subsetSumHolds inst ↔
      ∃ π, ∃ cfg : NTM2Config A (encodeSubsetSumF4Real inst),
        TapeReachablePathNTM2 A (encodeSubsetSumF4Real inst) π cfg ∧
        cfg.state ∈ A.acceptStates ∧
        ntm2ForkCount A π = inst.elements.length)

/-- [公理 V1.2] CBTM ≅ NTM2 的同构桥：NTM2 求解 ⇒ IsNP_F。
    消去路径：`exists_CBTM_iso_NTM2`（CBTM.lean，定理：每个 NTM2
    同构于某 CBTM，即结构同构定理 `StructIsoNTM2CBTM`）+ 结构同构
    保持接受语言的新定理（`StructIso_preserves_accepts`，待证：
    `StructIsoNTM2CBTM A M → (A.acceptsTape x ↔ M.tapeAccepts (编码 x))`，
    由 h_transition 的逐步对应归纳）。该两定理齐备后本公理消去为 theorem。 -/
axiom NTM2_solve_implies_IsNP_F :
  (∃ A : NTM2, ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
    (subsetSumHolds inst ↔
      ∃ π, ∃ cfg : NTM2Config A (encodeSubsetSumF4Real inst),
        TapeReachablePathNTM2 A (encodeSubsetSumF4Real inst) π cfg ∧
        cfg.state ∈ A.acceptStates ∧
        ntm2ForkCount A π = inst.elements.length)) →
  IsNP_F subsetSumLanguageF4Real

/-- 子集和 ∈ NP_F（由两个公理组装）。 -/
theorem subsetSum_in_NP_F : IsNP_F subsetSumLanguageF4Real :=
  NTM2_solve_implies_IsNP_F exists_NTM2_solves_subsetSum

end PvsNP
