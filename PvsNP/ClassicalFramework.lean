/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM
import PvsNP.EssentialDimension

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
# PvsNP.ClassicalFramework

经典计算模型（DTM/NTM）作为 CBTM 的遗忘投影。
遗忘函子 forget : CBTM → ClassicalNTM 剥离虚部语义，
使经典模型无法访问虚部信息，从而绕过相对化障碍。
-/

namespace PvsNP

open CBTM

-- ======================================================================
-- 投影：F₄ → Bool （剥离虚部信息）
-- ======================================================================

/-- 符号投影：one 和 alpha → true，zero 和 beta → false（即实部与虚部异或）。 -/
def projectSymbol (s : F4) : Bool := s.1 != s.2

@[simp] theorem projectSymbol_zero : projectSymbol F4.zero = false := rfl
@[simp] theorem projectSymbol_one : projectSymbol F4.one = true := rfl
@[simp] theorem projectSymbol_alpha : projectSymbol F4.alpha = true := rfl
@[simp] theorem projectSymbol_beta : projectSymbol F4.beta = false := rfl

/-- 列表投影。 -/
def projectList : List F4 → List Bool := List.map projectSymbol

-- ======================================================================
-- 经典 NTM（使用 ℕ 状态，Bool 字母表）

-- ======================================================================
-- 不可恢复性：没有经典 DTM 能恢复虚部信息
-- ======================================================================

/-- 不存在经典 DTM 能恢复被遗忘的虚部信息。 -/
theorem no_forget_recovery_dtm :
    ¬ (∃ (_D : ClassicDTM) (recover : List Bool → List F4),
      ∀ (x : List F4), recover (projectList x) = x) := by
  intro h
  rcases h with ⟨_D, recover, h⟩
  let x1 : List F4 := [F4.alpha]
  let x2 : List F4 := [F4.one]
  have h_proj_eq : projectList x1 = projectList x2 := by
    simp [projectList, x1, x2]
  have h_rec_x1 : recover (projectList x1) = x1 := h x1
  have h_rec_x2 : recover (projectList x2) = x2 := h x2
  rw [h_proj_eq] at h_rec_x1
  have h_eq : x1 = x2 := by
    calc
      x1 = recover (projectList x2) := by symm; exact h_rec_x1
      _ = x2 := h_rec_x2
  have h_ne : x1 ≠ x2 := by
    intro h_eq'
    have : F4.alpha = F4.one := by
      simpa [x1, x2] using congrArg (·.head?) h_eq'
    exact Bool.noConfusion (congrArg Prod.fst this)
  exact h_ne h_eq

-- ======================================================================
-- F4 复杂度类（重新定义在经典 CBTM 上；公理版，不依赖验证器编译链）
-- ======================================================================

/-- F4 语言：带虚部的串集合。虚部是输入的一部分，验证器不可选择。 -/
abbrev FLanguage : Type := Set (List F4)

/-- F4 语言的验证器集合（直接接受 F4 串，虚部固定；磁带语义）。 -/
def FVerifiers (L : FLanguage) : Set CBTM :=
  { M | CBTM.isPolynomialTime M ∧ (∀ w : List F4, M.tapeAccepts w ↔ L w) }

/-- F4 语言在长度 n 上的本质维度。 -/
noncomputable def FessentialDimension (L : FLanguage) (n : ℕ) : ℕ := by
  classical
  by_cases h : ∃ M, M ∈ FVerifiers L
  · have h_ex : ∃ (k : ℕ), ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = k := by
      rcases h with ⟨M, hM⟩
      exact ⟨worstCaseDimension M n, M, hM, rfl⟩
    exact Nat.find h_ex
  · exact 0

theorem FessentialDimension_spec (L : FLanguage) (n : ℕ)
    (h_nonempty : ∃ M, M ∈ FVerifiers L) :
    ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = FessentialDimension L n := by
  classical
  have h_ex : ∃ (k : ℕ), ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = k := by
    rcases h_nonempty with ⟨M, hM⟩
    exact ⟨worstCaseDimension M n, M, hM, rfl⟩
  have h_ess_eq : FessentialDimension L n = Nat.find h_ex := by
    unfold FessentialDimension
    simp only [h_nonempty, dite_true]
  rw [h_ess_eq]
  exact Nat.find_spec h_ex

/-- F4 语言的多项式时间确定性类（restricted CBTM 判定，磁带语义）。 -/
def IsP_F (L : FLanguage) : Prop :=
  ∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTime M ∧ (∀ w, M.tapeAccepts w ↔ L w)

/-- F4 语言的多项式时间非确定性类（磁带语义）。 -/
def IsNP_F (L : FLanguage) : Prop :=
  ∃ M, CBTM.isPolynomialTime M ∧ (∀ w, M.tapeAccepts w ↔ L w)

def P_F : Set FLanguage := { L | IsP_F L }
def NP_F : Set FLanguage := { L | IsNP_F L }

end PvsNP
