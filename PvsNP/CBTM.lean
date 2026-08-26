/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mathlib
import PvsNP.Basic

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

open NTM2
open ClassicDTM

-- F₄ 的实例需置于所有依赖它的结构之前
instance : DecidableEq F4 := inferInstanceAs (DecidableEq (Bool × Bool))
instance : Fintype F4 := inferInstanceAs (Fintype (Bool × Bool))

-- ===========================================================================
-- 基本辅助函数
-- ===========================================================================

/-- 将布尔值映射到实部 F₄ 符号。 -/
def boolToF4 (b : Bool) : F4 := (b, false)

/-- 将虚部为 false 的 F₄ 符号映射回布尔值。 -/
def f4ToBool (s : F4) : Bool := s.1

/-- boolToF4 的虚部恒为 false。 -/
@[simp] theorem boolToF4_im_false (b : Bool) : F4.im (boolToF4 b) = false := rfl

/-- f4ToBool 与 boolToF4 互逆（在实部符号上）。 -/
theorem f4ToBool_boolToF4 (b : Bool) : f4ToBool (boolToF4 b) = b := rfl

@[simp] theorem boolToF4_false : boolToF4 false = F4.zero := rfl
@[simp] theorem boolToF4_true : boolToF4 true = F4.one := rfl

-- ===========================================================================
-- §1. CBTM 转移结果
-- ===========================================================================

structure CBTMTransResult : Type where
  nextState : ℕ
  writeSym  : F4
  moveDir   : Dir
  deriving DecidableEq

-- ===========================================================================
-- §2. CBTM 结构体
-- ===========================================================================

structure CBTM : Type where
  states      : Finset ℕ
  startState  : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  alphabet    : Finset F4
  /-- 转移依赖磁头位置：(q, 读符号, 磁头位置) → 结果集。 -/
  transition  : ℕ × F4 × ℤ → Finset CBTMTransResult
  blankSym    : F4
  h_blank_in_alphabet : blankSym ∈ alphabet
  h_start_in_states   : startState ∈ states
  h_accept_subset     : acceptStates ⊆ states
  h_reject_subset     : rejectStates ⊆ states
  h_accept_reject_disjoint : acceptStates ∩ rejectStates = ∅
  /-- 严格分支公理：虚部 false → 1 个结果；虚部 true → 恰好 2 个结果（与位置无关）。 -/
  h_branch_axiom : ∀ q s i, s ∈ alphabet →
    if F4.im s then (transition (q, s, i)).card = 2 else (transition (q, s, i)).card = 1
  /-- 投影约束：虚部 false 的读符号 → 写回符号虚部也为 false。 -/
  h_projection_constraint : ∀ q s i, s ∈ alphabet → F4.im s = false →
    (transition (q, s, i)).card = 1 ∧
    ∀ r ∈ (transition (q, s, i)), F4.im r.writeSym = false
  /-- 良构性：转移结果状态属于状态集。 -/
  isValid : ∀ q s i, s ∈ alphabet → ∀ r ∈ (transition (q, s, i)), r.nextState ∈ states
  /-- 字母表外的读符号无转移。 -/
  h_transition_outside : ∀ q s i, s ∉ alphabet → transition (q, s, i) = ∅

-- ===========================================================================
-- §2.5 CBTM 计算语义
-- ===========================================================================

/-- CBTM 转移步：读符号与选定的转移结果。 -/
structure TransitionStep : Type where
  fromState : ℕ
  readSym   : F4
  result    : CBTMTransResult

instance : Inhabited TransitionStep :=
  ⟨{ fromState := 0, readSym := F4.zero, result := ⟨0, F4.zero, Dir.S⟩ }⟩

/-- CBTM 计算路径 = 转移步列表。 -/
abbrev ComputationPath := List TransitionStep

namespace ComputationPath

/-- 路径末端状态（空路径为初始状态）。 -/
def endState (M : CBTM) (π : ComputationPath) : ℕ :=
  π.foldl (fun _ step => step.result.nextState) M.startState

end ComputationPath

/-- CBTM 的可达路径：读符号序列恰为输入，每一步都是合法转移（含磁头位置追踪）。 -/
inductive ReachablePath (M : CBTM) : List F4 → ℤ → ComputationPath → Prop
  | nil : ReachablePath M [] 0 []
  | cons : ∀ (xs : List F4) (a : F4) (pos : ℤ) (π₀ : ComputationPath) (step : TransitionStep),
      ReachablePath M xs pos π₀ →
      step.fromState = ComputationPath.endState M π₀ →
      step.readSym = a →
      step.result ∈ M.transition (ComputationPath.endState M π₀, a, pos) →
      ReachablePath M (xs ++ [a]) (pos + step.result.moveDir.toInt) (π₀ ++ [step])

namespace ReachablePath

/-- 路径是否在接受状态结束。 -/
def isAccepting (M : CBTM) (π : ComputationPath) : Bool :=
  decide (ComputationPath.endState M π ∈ M.acceptStates)

end ReachablePath

/-- CBTM 接受一个 F4 串。 -/
def CBTM.accepts (M : CBTM) (x : List F4) : Prop :=
  ∃ π, ∃ pos, ReachablePath M x pos π ∧ ReachablePath.isAccepting M π = true

-- ===========================================================================
-- §2.6 复杂度类辅助谓词
-- ===========================================================================

/-- 路径上虚部为 true 的符号个数（决策点计数）。 -/
def imTrueCount (l : List F4) : ℕ :=
  (l.filter (fun s => F4.im s)).length

/-- 受限 CBTM：字母表仅含实部符号，转移确定（无分支）。 -/
structure CBTM.IsRestricted (M : CBTM) : Prop where
  h_alphabet_subset : M.alphabet ⊆ {F4.zero, F4.one}
  h_alphabet_im_false : ∀ s, s ∈ M.alphabet → F4.im s = false
  h_card_one : ∀ q s i, s ∈ M.alphabet → (M.transition (q, s, i)).card = 1
  h_blank_in_alphabet : M.blankSym ∈ M.alphabet

/-- 占位：CBTM 的多项式时间性质（运行时间尚未形式化）。 -/
def CBTM.isPolynomialTime (_M : CBTM) : Prop := True

-- ===========================================================================
-- 辅助：基数 1 的有限集恰有唯一元素
-- ===========================================================================

lemma card_eq_one_unique_mem {α : Type*} (s : Finset α) (h : s.card = 1) :
    ∃! a : α, a ∈ s := by
  classical
  rcases Finset.card_eq_one.mp h with ⟨a, ha⟩
  subst ha
  exact ⟨a, by simp, by intro b hb; simpa using hb⟩

-- ===========================================================================
-- §3. 受限 CBTM（CBTM0）
-- ===========================================================================

structure IsCBTM0 (M : CBTM) : Prop where
  alphabet_eq : M.alphabet = {F4.zero, F4.one}
  card_one : ∀ q s i, s ∈ M.alphabet → (M.transition (q, s, i)).card = 1
  pos_indep : ∀ q s i j, s ∈ M.alphabet → M.transition (q, s, i) = M.transition (q, s, j)

-- ===========================================================================
-- §4. 完全 CBTM
-- ===========================================================================

def IsFull (M : CBTM) : Prop :=
  M.alphabet = {F4.zero, F4.one, F4.alpha, F4.beta}

-- ===========================================================================
-- 转换：ClassicDTM → CBTM0
-- ===========================================================================

/-- ClassicDTM 转移函数的 F4 投影：在 {zero, one} 上给出单元素转移集，其余为空（位置无关）。 -/
def ClassicDTM.toCBTMTrans (M : ClassicDTM) : ℕ × F4 × ℤ → Finset CBTMTransResult :=
  fun (q, s, _i) =>
    if s ∈ ({F4.zero, F4.one} : Finset F4) then
      {CBTMTransResult.mk (M.transition (q, f4ToBool s)).nextState
         (boolToF4 (M.transition (q, f4ToBool s)).writeSym)
         (M.transition (q, f4ToBool s)).move}
    else
      ∅

@[simp] theorem ClassicDTM.toCBTMTrans_zero (M : ClassicDTM) (q : ℕ) (i : ℤ) :
    ClassicDTM.toCBTMTrans M (q, F4.zero, i) =
      {CBTMTransResult.mk (M.transition (q, false)).nextState
         (boolToF4 (M.transition (q, false)).writeSym)
         (M.transition (q, false)).move} := by
  simp only [ClassicDTM.toCBTMTrans]
  rw [if_pos (by simp)]
  rfl

@[simp] theorem ClassicDTM.toCBTMTrans_one (M : ClassicDTM) (q : ℕ) (i : ℤ) :
    ClassicDTM.toCBTMTrans M (q, F4.one, i) =
      {CBTMTransResult.mk (M.transition (q, true)).nextState
         (boolToF4 (M.transition (q, true)).writeSym)
         (M.transition (q, true)).move} := by
  simp only [ClassicDTM.toCBTMTrans]
  rw [if_pos (by simp)]
  rfl

def ClassicDTM.toCBTM (M : ClassicDTM) : CBTM :=
  {
    states      := M.states
    startState  := M.startState
    acceptStates := M.acceptStates
    rejectStates := M.rejectStates
    alphabet    := {F4.zero, F4.one}
    transition  := ClassicDTM.toCBTMTrans M
    blankSym    := F4.zero
    h_blank_in_alphabet := by simp
    h_start_in_states   := M.h_start_in_states
    h_accept_subset     := M.h_accept_subset
    h_reject_subset     := M.h_reject_subset
    h_accept_reject_disjoint := M.h_accept_reject_disjoint
    h_branch_axiom := by
      intro q s i hs
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl <;> simp
    h_projection_constraint := by
      intro q s i hs h_im
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl <;> simp
    isValid := by
      intro q s i hs r hr
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl
      · rw [ClassicDTM.toCBTMTrans_zero M q i] at hr
        rw [Finset.mem_singleton] at hr
        subst hr
        simpa using (M.isValid q false)
      · rw [ClassicDTM.toCBTMTrans_one M q i] at hr
        rw [Finset.mem_singleton] at hr
        subst hr
        simpa using (M.isValid q true)
    h_transition_outside := by
      intro q s i hs_not
      simp only [ClassicDTM.toCBTMTrans]
      exact if_neg hs_not
  }

-- ===========================================================================
-- 转换：CBTM0 → ClassicDTM
-- ===========================================================================

lemma boolToF4_mem_alphabet_of_isCBTM0 {N : CBTM} (h0 : IsCBTM0 N) (b : Bool) :
    boolToF4 b ∈ N.alphabet := by
  rw [h0.alphabet_eq]
  cases b <;> decide

/-- CBTM0 的转移函数投影回经典 DTM（唯一转移的非计算选择；位置无关，取 0 占位）。 -/
noncomputable def CBTM.toClassicDTMTrans (N : CBTM) (h0 : IsCBTM0 N) :
    ℕ × Bool → ClassicDTMTransitionResult :=
  fun (q, b) =>
    let s : F4 := boolToF4 b
    let r : CBTMTransResult :=
      (card_eq_one_unique_mem (N.transition (q, s, 0))
        (h0.card_one q s 0 (boolToF4_mem_alphabet_of_isCBTM0 h0 b))).choose
    ClassicDTMTransitionResult.mk r.nextState (f4ToBool r.writeSym) r.moveDir

lemma toClassicDTMTrans_nextState_mem (N : CBTM) (h0 : IsCBTM0 N) (q : ℕ) (b : Bool) :
    (CBTM.toClassicDTMTrans N h0 (q, b)).nextState ∈ N.states := by
  simp only [CBTM.toClassicDTMTrans]
  let s : F4 := boolToF4 b
  have hs : s ∈ N.alphabet := boolToF4_mem_alphabet_of_isCBTM0 h0 b
  have h_unique : ∃! r : CBTMTransResult, r ∈ N.transition (q, s, 0) :=
    card_eq_one_unique_mem (N.transition (q, s, 0)) (h0.card_one q s 0 hs)
  exact N.isValid q s 0 hs h_unique.choose h_unique.choose_spec.1

noncomputable def CBTM.toClassicDTM (N : CBTM) (h0 : IsCBTM0 N) : ClassicDTM :=
  {
    states      := N.states
    startState  := N.startState
    acceptStates := N.acceptStates
    rejectStates := N.rejectStates
    alphabet    := {false, true}
    transition  := CBTM.toClassicDTMTrans N h0
    blankSym    := false
    h_start_in_states   := N.h_start_in_states
    h_accept_subset     := N.h_accept_subset
    h_reject_subset     := N.h_reject_subset
    h_accept_reject_disjoint := N.h_accept_reject_disjoint
    isValid := by
      intro q b
      exact toClassicDTMTrans_nextState_mem N h0 q b
    h_alphabet_all := by simp
  }

-- ===========================================================================
-- 结构同构关系
-- ===========================================================================

structure StructIsoClassicDTM (M : ClassicDTM) (N : CBTM) : Type where
  h_restricted : IsCBTM0 N
  h_states_eq : M.states = N.states
  φ_symbol : Equiv Bool { s : F4 // s ∈ N.alphabet }
  h_start : M.startState = N.startState
  h_accept : N.acceptStates = M.acceptStates
  h_reject : N.rejectStates = M.rejectStates
  h_transition : ∀ (q : ℕ) (s : Bool) (i : ℤ),
    let res := M.transition (q, s)
    let r : CBTMTransResult := {
      nextState := res.nextState
      writeSym := (φ_symbol res.writeSym).val
      moveDir := res.move
    }
    N.transition (q, (φ_symbol s).val, i) = {r}

-- ===========================================================================
-- 辅助引理（同构构造用）
-- ===========================================================================

/-- 虚部为 false 的 F4 符号，boolToF4 与 f4ToBool 互逆。 -/
lemma boolToF4_f4ToBool_of_im_false (s : F4) (h : F4.im s = false) :
    boolToF4 (f4ToBool s) = s := by
  rcases s with ⟨r, i⟩
  cases i
  · cases r <;> rfl
  · cases h

/-- 基数 1 的有限集等于其唯一元素（choose 所取）的单元素集。 -/
lemma eq_singleton_choose_of_card_eq_one {α : Type*} (s : Finset α) (h : s.card = 1) :
    s = {(card_eq_one_unique_mem s h).choose} := by
  classical
  rcases Finset.card_eq_one.mp h with ⟨a, ha⟩
  subst ha
  have hmem : a ∈ ({a} : Finset α) := by simp
  have hchoose : (card_eq_one_unique_mem ({a} : Finset α) h).choose = a :=
    (card_eq_one_unique_mem ({a} : Finset α) h).choose_spec.2 a hmem |>.symm
  rw [hchoose]

-- ===========================================================================
-- 同构定理：ClassicDTM ↔ CBTM0
-- ===========================================================================

theorem exists_CBTM0_iso_ClassicDTM (M : ClassicDTM) :
    ∃ (N : CBTM), Nonempty (StructIsoClassicDTM M N) := by
  let N := M.toCBTM
  have h0 : IsCBTM0 N := by
    refine ⟨rfl, ?_, ?_⟩
    · intro q s i hs
      have hcases : s = F4.zero ∨ s = F4.one := by
        dsimp [N] at hs
        simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl <;> unfold N <;> simp [ClassicDTM.toCBTM]
    · intro q s i j hs
      dsimp [N]
      rfl
  let φ_symbol : Equiv Bool { s : F4 // s ∈ N.alphabet } := {
    toFun := fun b => ⟨boolToF4 b, boolToF4_mem_alphabet_of_isCBTM0 h0 b⟩
    invFun := fun s => f4ToBool s.1
    left_inv := by intro b; rfl
    right_inv := by
      intro s
      rcases s with ⟨val, prop⟩
      have hval : val = F4.zero ∨ val = F4.one := by
        rw [h0.alphabet_eq] at prop
        simpa [Finset.mem_insert, Finset.mem_singleton] using prop
      rcases hval with rfl | rfl <;> apply Subtype.ext <;> rfl
  }
  refine ⟨N, ⟨{
    h_restricted := h0
    h_states_eq := rfl
    φ_symbol := φ_symbol
    h_start := rfl
    h_accept := rfl
    h_reject := rfl
    h_transition := by
      intro q s
      have hφ_val (b : Bool) : (φ_symbol b).val = boolToF4 b := rfl
      cases s <;> simp [hφ_val] <;> dsimp [N, ClassicDTM.toCBTM] <;> simp
  }⟩⟩

theorem exists_ClassicDTM_iso_CBTM0 (N : CBTM) (h0 : IsCBTM0 N) :
    ∃ (M : ClassicDTM), Nonempty (StructIsoClassicDTM M N) := by
  let M := N.toClassicDTM h0
  let φ_symbol : Equiv Bool { s : F4 // s ∈ N.alphabet } := {
    toFun := fun b => ⟨boolToF4 b, boolToF4_mem_alphabet_of_isCBTM0 h0 b⟩
    invFun := fun s => f4ToBool s.1
    left_inv := by intro b; rfl
    right_inv := by
      intro s
      rcases s with ⟨val, prop⟩
      have hval : val = F4.zero ∨ val = F4.one := by
        rw [h0.alphabet_eq] at prop
        simpa [Finset.mem_insert, Finset.mem_singleton] using prop
      rcases hval with rfl | rfl <;> apply Subtype.ext <;> rfl
  }
  refine ⟨M, ⟨{
    h_restricted := h0
    h_states_eq := rfl
    φ_symbol := φ_symbol
    h_start := rfl
    h_accept := rfl
    h_reject := rfl
    h_transition := by
      intro q s i
      have hφ_val (b : Bool) : (φ_symbol b).val = boolToF4 b := rfl
      let r' : CBTMTransResult :=
        (card_eq_one_unique_mem (N.transition (q, boolToF4 s, 0))
          (h0.card_one q (boolToF4 s) 0 (boolToF4_mem_alphabet_of_isCBTM0 h0 s))).choose
      have hcard : (N.transition (q, boolToF4 s, 0)).card = 1 :=
        h0.card_one q (boolToF4 s) 0 (boolToF4_mem_alphabet_of_isCBTM0 h0 s)
      have hr' : r' ∈ N.transition (q, boolToF4 s, 0) :=
        (card_eq_one_unique_mem (N.transition (q, boolToF4 s, 0)) hcard).choose_spec.1
      have h_write_im : F4.im r'.writeSym = false :=
        (N.h_projection_constraint q (boolToF4 s) 0
          (boolToF4_mem_alphabet_of_isCBTM0 h0 s) (boolToF4_im_false s)).2 r' hr'
      have h_trans : M.transition (q, s) =
          ClassicDTMTransitionResult.mk r'.nextState (f4ToBool r'.writeSym) r'.moveDir := by
        change CBTM.toClassicDTMTrans N h0 (q, s) =
          ClassicDTMTransitionResult.mk r'.nextState (f4ToBool r'.writeSym) r'.moveDir
        unfold CBTM.toClassicDTMTrans
        dsimp
      simp only [hφ_val, h_trans]
      have h_pos_indep : N.transition (q, boolToF4 s, i) = N.transition (q, boolToF4 s, 0) :=
        h0.pos_indep q (boolToF4 s) i 0 (boolToF4_mem_alphabet_of_isCBTM0 h0 s)
      rw [h_pos_indep]
      rw [eq_singleton_choose_of_card_eq_one (N.transition (q, boolToF4 s, 0)) hcard]
      rw [boolToF4_f4ToBool_of_im_false r'.writeSym h_write_im]
  }⟩⟩

-- ===========================================================================
-- NTM2 ↔ CBTM：一一映射（虚部 = 虚拟带 vb，格局完全相同）
-- ===========================================================================

/-- NTM2 转移结果 → CBTM 转移结果：写符号 = (写实部, vb[写回位置])，虚部自动 = 虚拟带。 -/
def ntm2ResultToCBTM (vb : ℤ → Bool) (i : ℤ) (r : ℕ × Bool × Dir) : CBTMTransResult :=
  CBTMTransResult.mk r.1 (r.2.1, vb (i + r.2.2.toInt)) r.2.2

/-- 恒等嵌入在写实部上是单射（虚部由 vb 决定，不影响单射性）。 -/
lemma ntm2ResultToCBTM_injective (vb : ℤ → Bool) (i : ℤ) :
    Function.Injective (ntm2ResultToCBTM vb i) := by
  intro r1 r2 h
  rcases r1 with ⟨n1, w1, d1⟩
  rcases r2 with ⟨n2, w2, d2⟩
  have hn : n1 = n2 := congrArg CBTMTransResult.nextState h
  have hw : w1 = w2 := congrArg (fun x : CBTMTransResult => x.writeSym.1) h
  have hd : d1 = d2 := congrArg CBTMTransResult.moveDir h
  subst n1
  subst w1
  subst d1
  rfl

/-- NTM2 → CBTM 的转移函数：读 (b, im) 位置 i。
    虚部一致（im = vb i）时用 A 的转移（写符号虚部 = vb[写回位置]）；
    不一致时给固定结果（非法计算占位，不影响语言）。 -/
def NTM2.toCBTMTrans (A : NTM2) : ℕ × F4 × ℤ → Finset CBTMTransResult :=
  fun (q, s, i) =>
    if hc : s.1 ∈ A.alphabet ∧ F4.im s = A.vb i then
      (A.transition (q, s.1, i)).image (ntm2ResultToCBTM A.vb i)
    else if F4.im s then
      {CBTMTransResult.mk A.startState F4.zero Dir.S, CBTMTransResult.mk A.startState F4.one Dir.S}
    else
      {CBTMTransResult.mk A.startState F4.zero Dir.S}

/-- NTM2 的读符号实部恒在字母表内。 -/
lemma mem_alphabet_NTM2 (A : NTM2) (b : Bool) : b ∈ A.alphabet := by
  rw [A.h_alphabet_all]
  cases b <;> decide

/-- 虚部一致时的转移展开。 -/
lemma toCBTMTrans_eq_of_consistent (A : NTM2) (q : ℕ) (s : F4) (i : ℤ)
    (hvb : F4.im s = A.vb i) :
    NTM2.toCBTMTrans A (q, s, i) =
      (A.transition (q, s.1, i)).image (ntm2ResultToCBTM A.vb i) := by
  simp [NTM2.toCBTMTrans, mem_alphabet_NTM2 A s.1, hvb]
/-- NTM2 → CBTM：结构相同（一一映射，格局完全相同；虚部 = 虚拟带 vb）。 -/
def NTM2.toCBTM (A : NTM2) : CBTM :=
{
  states      := A.states
  startState  := A.startState
  acceptStates := A.acceptStates
  rejectStates := A.rejectStates
  alphabet    := {F4.zero, F4.one, F4.alpha, F4.beta}
  transition  := NTM2.toCBTMTrans A
  blankSym    := (A.blankSym, A.vb 0)
  h_blank_in_alphabet := by
    rcases A.blankSym <;> rcases h : A.vb 0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta, h]
  h_start_in_states   := A.h_start_in_states
  h_accept_subset     := A.h_accept_subset
  h_reject_subset     := A.h_reject_subset
  h_accept_reject_disjoint := A.h_accept_reject_disjoint
  h_branch_axiom := by
    intro q s i hs
    unfold NTM2.toCBTMTrans
    dsimp
    by_cases hvb : F4.im s = A.vb i
    · have hcard := A.h_branch_axiom q s.1 i (mem_alphabet_NTM2 A s.1)
      have hc0 : s.1 ∈ A.alphabet ∧ F4.im s = A.vb i := ⟨mem_alphabet_NTM2 A s.1, hvb⟩
      simp [hc0]
      rw [Finset.card_image_of_injective (A.transition (q, s.1, i)) (ntm2ResultToCBTM_injective A.vb i)]
      by_cases him : F4.im s = true
      · have hvb1 : A.vb i = true := by
          rw [← hvb]
          exact him
        simp [him, hvb1] at hcard ⊢
        exact hcard
      · have hvb0 : A.vb i = false := by
          rw [← hvb]
          cases h : F4.im s <;> simp [h] at him ⊢
        simp [him, hvb0] at hcard ⊢
        exact hcard
    · have hc1 : ¬ (s.1 ∈ A.alphabet ∧ F4.im s = A.vb i) := by
        intro h
        exact hvb h.2
      simp [hc1]
      by_cases him : F4.im s
      · simp [him]
        have hne : CBTMTransResult.mk A.startState F4.zero Dir.S ≠
            CBTMTransResult.mk A.startState F4.one Dir.S := by
          intro h
          have hw : F4.zero = F4.one := by
            simpa using (congrArg (fun x : CBTMTransResult => x.writeSym) h)
          simp [F4.zero, F4.one] at hw
        simp [hne]
      · simp [him]
  h_projection_constraint := by
    intro q s i hs him
    unfold NTM2.toCBTMTrans
    dsimp
    by_cases hvb : F4.im s = A.vb i
    · have hcard := A.h_branch_axiom q s.1 i (mem_alphabet_NTM2 A s.1)
      have hc0 : s.1 ∈ A.alphabet ∧ F4.im s = A.vb i := ⟨mem_alphabet_NTM2 A s.1, hvb⟩
      have hvb0 : A.vb i = false := by
        rw [← hvb]
        exact him
      constructor
      · simp [hc0]
        rw [Finset.card_image_of_injective (A.transition (q, s.1, i)) (ntm2ResultToCBTM_injective A.vb i)]
        simp [him, hvb0] at hcard ⊢
        exact hcard
      · intro r hr
        have hr' : r ∈ (A.transition (q, s.1, i)).image (ntm2ResultToCBTM A.vb i) := by
          simpa [hc0] using hr
        rcases Finset.mem_image.mp hr' with ⟨r0, hr0, hf⟩
        rw [← hf]
        exact A.h_projection_constraint q s.1 i (mem_alphabet_NTM2 A s.1) hvb0 r0 hr0
    · have hc1 : ¬ (s.1 ∈ A.alphabet ∧ F4.im s = A.vb i) := by
        intro h
        exact hvb h.2
      simp [hc1]
      by_cases him2 : F4.im s
      · exfalso
        rw [him2] at him
        simp at him
      · constructor
        · simp [him2]
        · intro r hr
          simp [him2] at hr
          rcases hr with rfl | rfl <;> simp [F4.zero, F4.one]
  isValid := by
    intro q s i hs r hr
    unfold NTM2.toCBTMTrans at hr
    dsimp at hr
    by_cases hvb : F4.im s = A.vb i
    · have hc0 : s.1 ∈ A.alphabet ∧ F4.im s = A.vb i := ⟨mem_alphabet_NTM2 A s.1, hvb⟩
      have hr' : r ∈ (A.transition (q, s.1, i)).image (ntm2ResultToCBTM A.vb i) := by
        simpa [hc0] using hr
      rcases Finset.mem_image.mp hr' with ⟨r0, hr0, hf⟩
      rw [← hf]
      exact A.h_transition_state_mem q s.1 i (mem_alphabet_NTM2 A s.1) r0 hr0
    · have hc1 : ¬ (s.1 ∈ A.alphabet ∧ F4.im s = A.vb i) := by
        intro h
        exact hvb h.2
      simp [hc1] at hr
      by_cases him : F4.im s
      · simp [him] at hr
        rcases hr with rfl | rfl <;> exact A.h_start_in_states
      · simp [him] at hr
        rcases hr with rfl
        exact A.h_start_in_states
  h_transition_outside := by
    intro q s i hs_not
    exfalso
    rcases s with ⟨r, im⟩ <;> cases r <;> cases im <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta] at hs_not
}

@[simp] theorem toCBTM_states (A : NTM2) : (NTM2.toCBTM A).states = A.states := rfl
@[simp] theorem toCBTM_startState (A : NTM2) : (NTM2.toCBTM A).startState = A.startState := rfl
@[simp] theorem toCBTM_acceptStates (A : NTM2) : (NTM2.toCBTM A).acceptStates = A.acceptStates := rfl
@[simp] theorem toCBTM_rejectStates (A : NTM2) : (NTM2.toCBTM A).rejectStates = A.rejectStates := rfl
@[simp] theorem toCBTM_transition (A : NTM2) : (NTM2.toCBTM A).transition = NTM2.toCBTMTrans A := rfl
@[simp] theorem toCBTM_blankSym (A : NTM2) : (NTM2.toCBTM A).blankSym = (A.blankSym, A.vb 0) := rfl

-- ===========================================================================
-- CBTM → NTM2（反向：虚部由外部 vb 带提供）




end PvsNP
