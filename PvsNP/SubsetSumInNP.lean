/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.ClassicalFramework
import PvsNP.ClassicalComplexity
import PvsNP.SubsetSumLanguage
import PvsNP._A2Bridge

/-!
# 子集和 ∈ NP_F（公理版：NTM2 求解公理）

按 Spec.md 约定的公理方案（位置模型 V4，Bool 输入 + 规范 NTM2）：
- 主公理 `exists_NTM2_solves_subsetSum`：存在一台规范 NTM2，
  输入 = Bool 串（与经典 P/NP 语言相同；虚部与语言无关，只与计算模型有关）。
  四条款：
  1. 求解条款：对每个非空实例，子集和成立 ⟺ 该 NTM2 有一条磁带语义的接受路径，
     且分叉次数（vb = 1 的位置数）恰为元素个数。
  2. 语言桥条款：NTM2 输入（实部串）经 vb 带复合后 = 语言的 F4 编码
     （复合串 = encodeSubsetSumF4Real inst）。
  3. 规范条款：NTM2 是规范的（任意可达路径的磁头只在输入区内活动，
     且每格至多读一次 —— 「只能读一遍输入」；空白区 vbAt 取值不影响行为，
     空白一致性不再是前提）。
  4. 语言识别条款：toCBTM A 恰好识别子集和语言（∀ w 的行为；
     由「不能提升」的投影约束，∀ w 行为必须公理化）。
- 同构桥公理 `NTM2_solve_implies_IsNP_F` 由语言识别条款消去为 theorem
  （A2 消去：`StructIsoNTM2CBTM` + `exists_CBTM_iso_NTM2` + `StructIso_preserves_accepts`
  已就位；语言识别条款直接给出 IsNP_F 的 witness）。
- `subsetSum_in_NP_F` 由公理组装（theorem），供 FinalProof 使用。
- `subsetSum_in_NP`：Bool 层（压平）——语言识别定理（实部投影）给出 IsNP_Bool 的 witness。
-/

namespace PvsNP

open CBTM
open IVM

/-- NTM2 路径的分叉计数：路径中分叉位置（vb = 1）的步数。 -/
def ntm2ForkCount (A : NTM2) (π : NTM2ComputationPath) : ℕ :=
  (π.filter (fun step => A.vbAt step.pos)).length

/-- [公理 V4] 存在规范 NTM2 求解子集和（输入 = Bool 串；vb 由转移派生，只与输入模式对应）。
    条款 1：求解（接受 ⟺ 子集和成立，分叉次数 = 元素个数）。
    条款 2：语言桥（实部输入经 vb 复合 = 语言 F4 编码）。
    条款 3：规范（磁头只在输入区内活动，每格至多读一次 —— 机器性质，与输入无关）。
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
    NTM2.Canonical A ∧
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
    NTM2.Canonical A ∧
    (∀ w : List F4, (NTM2.toCBTM A).tapeAccepts w ↔ subsetSumLanguageF4Real w)) →
  IsNP_F subsetSumLanguageF4Real := by
  intro h
  rcases h with ⟨A, _hsolve, _hbridge, _hcan, hlang⟩
  exact ⟨NTM2.toCBTM A, trivial, hlang⟩

/-- 子集和 ∈ NP_F（由公理组装）。 -/
theorem subsetSum_in_NP_F : IsNP_F subsetSumLanguageF4Real :=
  NTM2_solve_implies_IsNP_F exists_NTM2_solves_subsetSum

/-- 子集和 ∈ NP（Bool 层，压平）——由公理组装：
    语言识别定理（实部投影）给出 IsNP_Bool 的 witness（规范 NTM2 A 直接判定实部串）。 -/
theorem subsetSum_in_NP : IsNP_Bool subsetSumBoolLanguage := by
  rcases exists_NTM2_solves_subsetSum with ⟨A, _hsolve, hbridge, hcan, hlang⟩
  refine ⟨A, hcan, ?_⟩
  exact ntm2_language_recognition A hcan hbridge hlang

/-- 子集和 F4 语言 = 复合提升（规范 NTM2 的 vb 带逐格复合；语言桥条款）。
    「NP_f 和 NP 所对应的语言是相同的」：F4 语言 = 实部语言的复合呈现，
    虚部（vb 带）是计算模型层的标记，与语言内容无关。 -/
theorem subsetSumLanguageF4Real_eq_lift (A : NTM2)
    (hbridge : ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeSubsetSumBits inst) = encodeSubsetSumF4Real inst) :
    subsetSumLanguageF4Real = liftLanguage A subsetSumBoolLanguage := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with ⟨inst, hw, hne, hholds⟩
    refine ⟨encodeSubsetSumBits inst, ?_, ?_⟩
    · rw [hbridge inst hne]
      exact hw
    · exact ⟨inst, rfl, hne, hholds⟩
  · intro h
    rcases h with ⟨x, hw, hx⟩
    rcases hx with ⟨inst, hx', hne, hholds⟩
    refine ⟨inst, ?_, hne, hholds⟩
    calc
      w = ntm2InputToCBTM A x := hw
      _ = ntm2InputToCBTM A (encodeSubsetSumBits inst) := by rw [hx']
      _ = encodeSubsetSumF4Real inst := hbridge inst hne

/-- 集合论层面的 NP 方向链条（子集和实例）：
    F4 语言 = 复合提升（语言桥条款）→ 实部投影 = Bool 语言（投影-提升互逆）
    → 投影语言 ∈ NP（规范 NTM2 直接判定）。
    「每一个 NP_f 语言投影得到的语言 ∈ NP」在此实例化。 -/
theorem subsetSum_NP_chain :
    projectLanguage subsetSumLanguageF4Real = subsetSumBoolLanguage ∧
    IsNP_Bool subsetSumBoolLanguage := by
  rcases exists_NTM2_solves_subsetSum with ⟨A, _hsolve, hbridge, _hcan, _hlang⟩
  constructor
  · rw [subsetSumLanguageF4Real_eq_lift A hbridge]
    exact projectLanguage_liftLanguage A subsetSumBoolLanguage
  · exact subsetSum_in_NP

end PvsNP
