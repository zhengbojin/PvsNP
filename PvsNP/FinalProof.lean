/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM
import PvsNP.EssentialDimension
import PvsNP.Barriers
import PvsNP.LowerBound
import PvsNP.ClassicalFramework
import PvsNP.SubsetSumLanguage
import PvsNP.PrimeSqrtLinearIndep
import PvsNP.SubsetSumInNP

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
# 最终证明：P ≠ NP（F4/CBTM 框架，及其集合论层面的传递）

证明路线（对应论文 measure.C.0.7.tex 第 5-6 节）：

1. 子集和语言 `subsetSumLanguageF4Real`（带固定虚部的 F4 编码）属于 `NP_F`
   —— 经典结果「子集和是 NP 完全问题」（`subsetSum_in_NP_F`）。
2. 点态下界（论文 thm:subset-sum-lower 的核心）：对任意正确验证器 M 与任意
   YES 实例 inst，`kappa_M M (encode inst) ≥ 元素个数`（`subsetSum_kappa_lower_bound`）。
   依据：每个元素编码为一个虚部 = 1 的分支标记，而 ReachablePath 语义强制
   每条接受路径逐符号消费整个输入，故每条路径至少触发「元素个数」次非确定性
   分支，分支-激活引理将其转化为同等数量的生成元激活。
3. 故子集和 ∉ P_F（`subsetSum_not_in_P_F`）：restricted 验证器的 kappa 恒为 0，
   与点态下界 κ ≥ 1 矛盾。
4. 反证：若 P_F = NP_F，由 1 知子集和 ∈ P_F，与 3 矛盾。故 P_F ≠ NP_F。

关于「经典 P ≠ NP」的语义定位（本证明的关键区分，见论文第 7 节）：

- **F4/CBTM 框架内**：`P_F ≠ NP_F` 可证（本文件）。这一证明依赖 CBTM 内建的
  「不可公度性」语义——虚部标记使非确定性分支在代数上不可归约，从而 κ 可定义
  且可累积。
- **集合论（ZFC）层面**：`P_F ≠ NP_F` 通过「参数化等价定理」
  （`P_cb = P`、`NP_cb = NP`，见 models.C.0.6.tex）传递为经典的 `P ≠ NP`。
  这一传递尚未在本项目形式化（需先形式化经典 DTM 的 P/NP 类与等价定理）。
- **经典 DTM 操作语义内部**：`P ≠ NP` 不可证——经典 DTM 缺乏「不可公度性作为
  操作语义内在属性」的概念资源（不可公度性元定理），故本质维度 κ 在经典模型中
  不可定义，本证明所需的代数分离论证无法在经典语境内被复制。
-/

namespace PvsNP

open CBTM
open IVM

-- P_F、NP_F、FLanguage、IsP_F、IsNP_F 定义于 PvsNP.ClassicalFramework（经典 CBTM 磁带语义）；
-- subsetSum_kappa_lower_bound、subsetSum_not_in_P_F 定义于 PvsNP.SubsetSumLanguage（真实编码）；
-- subsetSum_in_NP_F 定理化于 PvsNP.SubsetSumInNP（公理 A1 + 同构桥定理）。

/-- CBTM（F4）框架内的分离：子集和 ∈ NP_F 但 ∉ P_F，故 P_F ≠ NP_F。
    反证法：若 P_F = NP_F，由 subsetSum_in_NP_F 得子集和 ∈ P_F，
    与 subsetSum_not_in_P_F' 矛盾。 -/
theorem P_F_neq_NP_F : P_F ≠ NP_F := by
  intro h_eq
  have hSS_in_NP : subsetSumLanguageF4Real ∈ NP_F := subsetSum_in_NP_F
  have hSS_in_P : subsetSumLanguageF4Real ∈ P_F := by
    rw [← h_eq] at hSS_in_NP
    exact hSS_in_NP
  exact subsetSum_not_in_P_F' hSS_in_P

/-- CBTM（F4）框架内的分离结论（别名）。 -/
theorem P_cb_neq_NP_cb : P_F ≠ NP_F := P_F_neq_NP_F

-- 综合定理（含障碍无关）
theorem P_neq_NP_with_barriers :
    P_F ≠ NP_F ∧
    (∀ O : Oracle, FessentialDimension (languageWithOracle subsetSumLanguageF4Real O) 100 =
      FessentialDimension subsetSumLanguageF4Real 100) ∧
    (∀ A : AlgebraicOracle, FessentialDimension
      (languageWithAlgebraicOracle subsetSumLanguageF4Real A) 100 =
      FessentialDimension subsetSumLanguageF4Real 100) := by
  constructor
  · exact P_F_neq_NP_F
  · constructor
    · intro O; exact relativizationInvariance subsetSumLanguageF4Real 100 O
    · intro A; exact algebrizationInvariance subsetSumLanguageF4Real 100 A

end PvsNP
