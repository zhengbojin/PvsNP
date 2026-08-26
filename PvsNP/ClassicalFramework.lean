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

/-- 经典非确定性图灵机。 -/
structure ClassicalNTM : Type where
  states      : Finset ℕ
  alphabet    : Finset Bool
  transition  : ℕ → Bool → Finset (ℕ × Bool × Dir)
  startState  : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  h_start : startState ∈ states
  h_accept : acceptStates ⊆ states
  h_reject : rejectStates ⊆ states
  h_disjoint : acceptStates ∩ rejectStates = ∅

-- ======================================================================
-- 遗忘函子：CBTM → ClassicalNTM
-- ======================================================================

/-- 将 CBTM 遗忘为经典 NTM。字母表投影到 Bool，转移投影为 Finset。 -/
def forget (M : CBTM) : ClassicalNTM :=
  {
    states      := M.states
    alphabet    := Finset.image projectSymbol M.alphabet
    transition  := fun q b =>
      let relevantSymbols : Finset F4 :=
        Finset.filter (fun s => projectSymbol s = b ∧ s ∈ M.alphabet) Finset.univ
      Finset.biUnion relevantSymbols (fun s =>
        (M.transition (q, s)).image (fun r =>
          (r.nextState, projectSymbol r.writeSym, r.moveDir)))
    startState  := M.startState
    acceptStates := M.acceptStates
    rejectStates := M.rejectStates
    h_start     := M.h_start_in_states
    h_accept    := M.h_accept_subset
    h_reject    := M.h_reject_subset
    h_disjoint  := M.h_accept_reject_disjoint
  }

namespace ClassicalNTM

/-- 经典 NTM 的接受定义：存在 CBTM 和 F4 输入，使得 forget M = N 且 M 接受。 -/
def accepts (N : ClassicalNTM) (y : List Bool) : Prop :=
  ∃ (M : CBTM) (x : List F4), forget M = N ∧ projectList x = y ∧ M.accepts x

end ClassicalNTM

-- ======================================================================
-- 经典 NTM 的自然接受语义（直接计算语义，区别于 forget 基语义）
-- ======================================================================

namespace ClassicalNTM

/-- 经典 NTM 的转移步。 -/
structure TransitionStep where
  fromState : ℕ
  readSym : Bool
  result : ℕ × Bool × Dir

/-- 经典 NTM 的计算路径。 -/
abbrev ComputationPath := List TransitionStep

namespace ComputationPath

/-- 路径末端状态（空路径为初始状态）。 -/
def endState (N : ClassicalNTM) (π : ComputationPath) : ℕ :=
  π.foldl (fun _ step => step.result.1) N.startState

end ComputationPath

/-- 经典 NTM 的可达路径：读符号恰为输入，每一步为合法转移。 -/
inductive ReachablePath (N : ClassicalNTM) : List Bool → ComputationPath → Prop
  | nil : ReachablePath N [] []
  | cons : ∀ (xs : List Bool) (a : Bool) (π₀ : ComputationPath) (step : TransitionStep),
      ReachablePath N xs π₀ →
      step.fromState = ComputationPath.endState N π₀ →
      step.readSym = a →
      step.result ∈ N.transition (ComputationPath.endState N π₀) a →
      ReachablePath N (xs ++ [a]) (π₀ ++ [step])

/-- 经典 NTM 的自然接受：存在读取整个输入且结束于接受态的可达路径。 -/
def accepts_nat (N : ClassicalNTM) (x : List Bool) : Prop :=
  ∃ π, ReachablePath N x π ∧ ComputationPath.endState N π ∈ N.acceptStates

end ClassicalNTM

-- ======================================================================
-- ClassicalNTM → NTM2（在良构假设 IsBinary 下）
-- ======================================================================

namespace ClassicalNTM

/-- 使 ClassicalNTM 可直接转化为 NTM2 的良构性条件。
    NTM2 额外要求：全字母表、≤2 分支、vb 一致标记、投影约束、
    唯一接受/拒绝态、转移结果落在状态集内。 -/
structure IsBinary (N : ClassicalNTM) where
  vb : Bool → Bool
  h_alphabet_full : N.alphabet = {false, true}
  h_card : ∀ q s, s ∈ N.alphabet → (N.transition q s).card = 1 ∨ (N.transition q s).card = 2
  h_vb : ∀ q s, s ∈ N.alphabet → (vb s = true ↔ (N.transition q s).card = 2)
  h_proj : ∀ q s, s ∈ N.alphabet → vb s = false → ∀ r ∈ N.transition q s, vb r.2.1 = false
  h_accept_single : N.acceptStates.card = 1
  h_reject_single : N.rejectStates.card = 1
  h_state_mem : ∀ q s, s ∈ N.alphabet → ∀ r ∈ N.transition q s, r.1 ∈ N.states

/-- 经典 NTM 步 → NTM2 步（结构一致，直接重包装）。 -/
def ntm2StepOf (s : TransitionStep) : NTM2TransitionStep :=
  { fromState := s.fromState, readSym := s.readSym, result := s.result }

/-- 经典 NTM 路径 → NTM2 路径。 -/
def ntm2PathOf (π : ComputationPath) : NTM2ComputationPath :=
  π.map ntm2StepOf

/-- NTM2 步 → 经典 NTM 步。 -/
def classicalStepOf (s : NTM2TransitionStep) : TransitionStep :=
  { fromState := s.fromState, readSym := s.readSym, result := s.result }

/-- NTM2 路径 → 经典 NTM 路径。 -/
def classicalPathOf (π : NTM2ComputationPath) : ComputationPath :=
  π.map classicalStepOf

/-- 在 IsBinary 良构假设下，ClassicalNTM 直接重包装为 NTM2。
    由于 ClassicalNTM 已满足 NTM2 的全部良构条件，此构造本质上是对字段的重新打包。 -/
def toNTM2 (N : ClassicalNTM) (hN : N.IsBinary) : NTM2 :=
{
  states := N.states
  startState := N.startState
  acceptStates := N.acceptStates
  rejectStates := N.rejectStates
  alphabet := N.alphabet
  transition := N.transition
  blankSym := false
  h_blank_in_alphabet := by
    rw [hN.h_alphabet_full]
    decide
  h_start_in_states := N.h_start
  h_accept_subset := N.h_accept
  h_reject_subset := N.h_reject
  h_accept_reject_disjoint := N.h_disjoint
  h_transition_card := hN.h_card
  vb := hN.vb
  h_vb_consistent := hN.h_vb
  h_accept_singleton := hN.h_accept_single
  h_reject_singleton := hN.h_reject_single
  h_alphabet_all := hN.h_alphabet_full
  h_transition_state_mem := hN.h_state_mem
  h_projection_constraint := hN.h_proj
}

@[simp] theorem toNTM2_states (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).states = N.states := rfl
@[simp] theorem toNTM2_startState (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).startState = N.startState := rfl
@[simp] theorem toNTM2_acceptStates (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).acceptStates = N.acceptStates := rfl
@[simp] theorem toNTM2_rejectStates (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).rejectStates = N.rejectStates := rfl
@[simp] theorem toNTM2_alphabet (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).alphabet = N.alphabet := rfl
@[simp] theorem toNTM2_transition (N : ClassicalNTM) (hN : N.IsBinary) :
    (toNTM2 N hN).transition = N.transition := rfl

/-- toNTM2 路径映射保持末端状态。 -/
lemma toNTM2Path_endState (N : ClassicalNTM) (hN : N.IsBinary) (π : ComputationPath) :
    NTM2ComputationPath.endState (toNTM2 N hN) (ntm2PathOf π) =
      ComputationPath.endState N π := by
  unfold ComputationPath.endState NTM2ComputationPath.endState ntm2PathOf
  rw [foldl_map_endState ntm2StepOf (fun s : NTM2TransitionStep => s.result.1)
    (fun s : TransitionStep => s.result.1) (toNTM2 N hN).startState π (by intro a; simp [ntm2StepOf])]
  rw [toNTM2_startState]

/-- toNTM2 反向路径映射保持末端状态。 -/
lemma toClassicalPath_endState (N : ClassicalNTM) (hN : N.IsBinary) (π : NTM2ComputationPath) :
    ComputationPath.endState N (classicalPathOf π) =
      NTM2ComputationPath.endState (toNTM2 N hN) π := by
  unfold ComputationPath.endState NTM2ComputationPath.endState classicalPathOf
  rw [foldl_map_endState classicalStepOf (fun s : TransitionStep => s.result.1)
    (fun s : NTM2TransitionStep => s.result.1) N.startState π (by intro a; simp [classicalStepOf])]
  rw [toNTM2_startState]

/-- toNTM2 保持可达性（正向）。 -/
lemma toNTM2_reachable_fwd (N : ClassicalNTM) (hN : N.IsBinary) {x : List Bool}
    {π : ComputationPath} (h : ReachablePath N x π) :
    ReachablePathNTM2 (toNTM2 N hN) x (ntm2PathOf π) := by
  induction h with
  | nil => simpa [ntm2PathOf] using (ReachablePathNTM2.nil : ReachablePathNTM2 (toNTM2 N hN) [] [])
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      simp [ntm2PathOf, ntm2StepOf]
      refine ReachablePathNTM2.cons xs a (ntm2PathOf π₀) (ntm2StepOf step) ih ?_ ?_ ?_
      · simp [ntm2StepOf]
        rw [toNTM2Path_endState N hN π₀]
        exact h_from
      · simp [ntm2StepOf]
        exact h_read
      · simp [ntm2StepOf]
        rw [toNTM2Path_endState N hN π₀]
        exact h_trans

/-- toNTM2 保持可达性（反向）。 -/
lemma toNTM2_reachable_bwd (N : ClassicalNTM) (hN : N.IsBinary) {x : List Bool}
    {π : NTM2ComputationPath} (h : ReachablePathNTM2 (toNTM2 N hN) x π) :
    ReachablePath N x (classicalPathOf π) := by
  induction h with
  | nil => simpa [classicalPathOf] using (ReachablePath.nil : ReachablePath N [] [])
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      simp [classicalPathOf, classicalStepOf]
      refine ReachablePath.cons xs a (classicalPathOf π₀) (classicalStepOf step) ih ?_ ?_ ?_
      · simp [classicalStepOf]
        rw [toClassicalPath_endState N hN π₀]
        exact h_from
      · simp [classicalStepOf]
        exact h_read
      · simp [classicalStepOf]
        rw [toClassicalPath_endState N hN π₀]
        exact h_trans

/-- toNTM2 保持接受性：NTM2.accepts (toNTM2 N hN) x ⟷ accepts_nat N x。 -/
theorem toNTM2_accepts_nat_iff (N : ClassicalNTM) (hN : N.IsBinary) (x : List Bool) :
    NTM2.accepts (toNTM2 N hN) x ↔ accepts_nat N x := by
  constructor
  · intro h
    rcases h with ⟨π, hr, hacc⟩
    refine ⟨classicalPathOf π, toNTM2_reachable_bwd N hN hr, ?_⟩
    rw [toClassicalPath_endState N hN π]
    exact hacc
  · intro h
    rcases h with ⟨π, hr, hacc⟩
    refine ⟨ntm2PathOf π, toNTM2_reachable_fwd N hN hr, ?_⟩
    rw [toNTM2Path_endState N hN π]
    exact hacc

end ClassicalNTM

-- ======================================================================
-- 遗忘保持接受行为
-- ======================================================================

/-- 遗忘保持接受行为。 -/
theorem forget_preserves_acceptance (M : CBTM) (x : List F4) (h : M.accepts x) :
    (forget M).accepts (projectList x) := by
  unfold ClassicalNTM.accepts
  exact ⟨M, x, rfl, rfl, h⟩

/-- 遗忘保持语法结构。 -/
theorem forget_syntax_preserving (M : CBTM) :
    (forget M).states = M.states ∧ (forget M).startState = M.startState := by
  simp [forget]

-- ======================================================================
-- 经典 NP 定义
-- ======================================================================

/-- 经典 NP：存在多项式 p 和经典 NTM V 验证。 -/
def classicalNPDefinition (L : Language) : Prop :=
  ∃ (p : ℕ → ℕ) (V : ClassicalNTM),
    ∀ x, L x ↔ ∃ (w : List Bool), w.length ≤ p (List.length x) ∧ V.accepts (x ++ w)

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
