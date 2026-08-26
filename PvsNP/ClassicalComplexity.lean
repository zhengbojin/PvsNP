/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.ClassicalFramework
import PvsNP.SubsetSumLanguage
import PvsNP._A2Bridge

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
# PvsNP.ClassicalComplexity

经典 Bool 复杂度类（压平层：实部投影）。

F4 语言的实部投影 → 经典 Bool 语言。虚部与语言无关，只与计算模型有关：
- Bool 语言的 P = 存在受限 CBTM 判定无标记嵌入（虚部全 false，机器永不分支）；
- Bool 语言的 NP = 存在规范 NTM2 直接判定（输入即实部串；分叉 = 计算模型层的标记）。
-/

namespace PvsNP

open CBTM
open IVM

-- ======================================================================
-- 经典 Bool 复杂度类
-- ======================================================================

/-- 经典 Bool 语言。 -/
abbrev BoolLanguage : Type := Set (List Bool)

/-- 无标记嵌入：Bool 串 → F4 串（虚部全 false；受限机器（不分支）的判定输入）。 -/
def embedBool (x : List Bool) : List F4 :=
  x.map (fun b => (b, false))

/-- Bool 语言的 P：存在受限 CBTM，对无标记嵌入判定。 -/
def IsP_Bool (L : BoolLanguage) : Prop :=
  ∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTime M ∧
    (∀ x : List Bool, M.tapeAccepts (embedBool x) ↔ L x)

/-- Bool 语言的 NP：存在规范 NTM2 直接判定（输入即实部串；分叉 = 计算模型层的标记）。 -/
def IsNP_Bool (L : BoolLanguage) : Prop :=
  ∃ A : NTM2, NTM2.Canonical A ∧ (∀ x : List Bool, A.acceptsTape x ↔ L x)

def P_Bool : Set BoolLanguage := { L | IsP_Bool L }
def NP_Bool : Set BoolLanguage := { L | IsNP_Bool L }

/-- 子集和的 Bool 语言（实部串 = encodeSubsetSumBits inst；虚部与语言无关）。 -/
def subsetSumBoolLanguage : BoolLanguage := fun x =>
  ∃ inst, x = encodeSubsetSumBits inst ∧ inst.elements ≠ [] ∧ subsetSumHolds inst

-- ======================================================================
-- 实部投影（压平的核心映射：逐格取实部）
-- ======================================================================

/-- 实部投影：F4 串 → Bool 串（逐格取实部）。 -/
def realProject (w : List F4) : List Bool :=
  w.map F4.re

/-- 复合串的实部投影 = 原输入（逐格取实部；rfl 级）。 -/
lemma realProject_ntm2InputToCBTM (A : NTM2) (x : List Bool) :
    realProject (ntm2InputToCBTM A x) = x := by
  unfold realProject ntm2InputToCBTM
  apply List.ext_getElem
  · simp [List.length_mapIdx]
  · intro i h₁ h₂
    rw [List.getElem_map]
    rw [List.getElem_mapIdx]

/-- 编码的实部投影 = Bool 编码（定义展开）。 -/
lemma realProject_encodeSubsetSumF4Real (inst : SubsetSumInstance) :
    realProject (encodeSubsetSumF4Real inst) = encodeSubsetSumBits inst := by
  rfl

-- ======================================================================
-- 语言层的投影与提升（集合论映射：F4 语言 ↔ Bool 语言）
-- ======================================================================

/-- 语言投影：F4 语言 → Bool 语言（实部投影；虚部与语言无关，只与计算模型有关）。 -/
def projectLanguage (L : FLanguage) : BoolLanguage := fun x =>
  ∃ w, realProject w = x ∧ L w

/-- 复合提升：Bool 语言 → F4 语言（按规范 NTM2 的 vb 带逐格复合；
    虚部 = 位置函数，与输入内容无关 —— 「标记移到计算模型层」）。 -/
def liftLanguage (A : NTM2) (K : BoolLanguage) : FLanguage := fun w =>
  ∃ x, w = ntm2InputToCBTM A x ∧ K x

/-- 无标记提升：Bool 语言 → F4 语言（虚部全 false；受限机器（不分支）的语言呈现）。 -/
def embedUpLanguage (K : BoolLanguage) : FLanguage := fun w =>
  ∃ x, w = embedBool x ∧ K x

/-- 投影-提升互逆：复合语言的实部投影 = 原 Bool 语言（逐格取实部）。 -/
lemma projectLanguage_liftLanguage (A : NTM2) (K : BoolLanguage) :
    projectLanguage (liftLanguage A K) = K := by
  funext x
  apply propext
  constructor
  · intro h
    rcases h with ⟨w, hproj, hw⟩
    rcases hw with ⟨x', hw', hK⟩
    rw [hw'] at hproj
    have hx' : x' = x := by
      simpa [realProject_ntm2InputToCBTM A x'] using hproj
    subst x'
    exact hK
  · intro hx
    refine ⟨ntm2InputToCBTM A x, ?_, ?_⟩
    · exact realProject_ntm2InputToCBTM A x
    · exact ⟨x, rfl, hx⟩

/-- P_F 语言的 Bool 呈现 ∈ P（受限机器判定的语言在嵌入输入上 = 同一机器；
    「P_f 和 P 所对应的语言是相同的」的方向一）。 -/
theorem P_F_projection_in_P (L : FLanguage) (hP : IsP_F L) :
    IsP_Bool (fun x => L (embedBool x)) := by
  rcases hP with ⟨M, hrest, hpoly, hcorrect⟩
  refine ⟨M, hrest, hpoly, ?_⟩
  intro x
  exact hcorrect (embedBool x)

-- ======================================================================
-- 实部语言识别（Bool 层）：NTM2 的语言 = 复合语言的实部投影
-- ======================================================================

/-- 实部语言识别定理（压平的集合论论证）：
    规范 NTM2 A 直接判定的 Bool 语言 = 复合语言（toCBTM A 识别的 F4 语言）的实部投影。
    由 语言桥条款（复合串 = 编码）+ 复合层语言识别条款（toCBTM 识别 F4 语言）
    + 同构桥（格局逐格相同，规范 NTM2 时）+ 实部投影（逐格取实部）推出。 -/
theorem ntm2_language_recognition (A : NTM2) (hcan : NTM2.Canonical A)
    (hbridge : ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeSubsetSumBits inst) = encodeSubsetSumF4Real inst)
    (hlang : ∀ w : List F4, (NTM2.toCBTM A).tapeAccepts w ↔ subsetSumLanguageF4Real w) :
    ∀ x : List Bool, A.acceptsTape x ↔ subsetSumBoolLanguage x := by
  rcases exists_CBTM_iso_NTM2 A with ⟨M, hM, ⟨iso⟩⟩
  intro x
  constructor
  · intro hacc
    have hcbtm : M.tapeAccepts (ntm2InputToCBTM A x) :=
      (StructIso_preserves_accepts A M iso hcan x).1 hacc
    have hL : subsetSumLanguageF4Real (ntm2InputToCBTM A x) := by
      rw [hM] at hcbtm
      exact (hlang (ntm2InputToCBTM A x)).1 hcbtm
    rcases hL with ⟨inst, henc, hne, hholds⟩
    refine ⟨inst, ?_, hne, hholds⟩
    rw [← realProject_ntm2InputToCBTM A x]
    rw [henc]
    exact realProject_encodeSubsetSumF4Real inst
  · intro ⟨inst, hx, hne, hholds⟩
    have henc' : ntm2InputToCBTM A x = encodeSubsetSumF4Real inst := by
      rw [hx]
      exact hbridge inst hne
    have hL : subsetSumLanguageF4Real (ntm2InputToCBTM A x) := by
      rw [henc']
      exact ⟨inst, rfl, hne, hholds⟩
    have hcbtm : (NTM2.toCBTM A).tapeAccepts (ntm2InputToCBTM A x) :=
      (hlang (ntm2InputToCBTM A x)).2 hL
    have hcbtm' : M.tapeAccepts (ntm2InputToCBTM A x) := by
      rw [hM]
      exact hcbtm
    exact (StructIso_preserves_accepts A M iso hcan x).2 hcbtm'

end PvsNP
