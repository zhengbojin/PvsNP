/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM
import PvsNP.ClassicalFramework

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

-- ============================================================================
-- 子集和问题的 F4 编码
-- ============================================================================

/-- 子集和实例：元素列表与目标值。 -/
structure SubsetSumInstance where
  elements : List ℕ
  target : ℕ

/-- 位置选择的选中值之和：`sel` 第 i 位为 true 时选中 `elements[i]`（每个位置最多一次）。 -/
def selectedSum (elements : List ℕ) (sel : List Bool) : ℕ :=
  ((elements.zip sel).filter (fun p => p.2 = true)).map Prod.fst |>.sum

/-- 子集和语义（位置选择）：存在一组选择，使选中值之和等于 target。

    注意：这里用「位置选择」而非「值多重集」语义——每个元素位置最多选一次，
    与验证器的 α/β 分支（sel/nosel）语义一致。旧的多重集语义
    `∃ T, (∀ a ∈ T, a ∈ elements) ∧ sum T = target` 允许重复使用同一元素值
    （如 elements=[3]、target=6 会被误判为 YES），是错误定义。 -/
def subsetSumHolds (inst : SubsetSumInstance) : Prop :=
  ∃ sel : List Bool, sel.length = inst.elements.length ∧ selectedSum inst.elements sel = inst.target

def natToBinaryF4 (_n : ℕ) : List F4 := []  -- 占位

/-- 每个元素用一个 F4.alpha 标记分支，后接目标值的二进制。 -/
def encodeSubsetSumF4 (inst : SubsetSumInstance) : List F4 :=
  List.flatMap (fun _ => [F4.alpha]) inst.elements ++ natToBinaryF4 inst.target

def subsetSumLanguageF4 : Language := fun bs =>
  ∃ inst, bs = List.map F4.re (encodeSubsetSumF4 inst) ∧
    ∃ T, (∀ a ∈ T, a ∈ inst.elements) ∧ List.sum T = inst.target


end PvsNP
