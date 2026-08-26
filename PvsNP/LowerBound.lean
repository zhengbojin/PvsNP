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

-- ============================================================================
-- 经典 NTM 占位及同构公理（ClassicalNTM 定义见 PvsNP.ClassicalFramework）
-- ============================================================================

/-- 子集和验证器的转移函数（二分支）。
    注：`natToBinaryF4` 目前为空占位，`encodeSubsetSumF4` 退化为 `replicate n alpha`，
    故 `subsetSumLanguageF4` 实际退化为「全 false 布尔串」。
    本转移即接受该语言的二分支有限状态机：
    读 false 保持（2 分支），读 true 拒绝（1 分支）。 -/
def subsetSumTransition (q : ℕ) (s : Bool) : Finset (ℕ × Bool × Dir) :=
  if s then
    {(2, true, Dir.S)}
  else if q = 2 ∨ q = 3 then
    {(2, false, Dir.S), (3, false, Dir.S)}
  else
    {(0, false, Dir.S), (1, false, Dir.S)}

/-- 读 false 恒为 2 分支。 -/
lemma subsetSumTransition_card_false (q : ℕ) : (subsetSumTransition q false).card = 2 := by
  unfold subsetSumTransition
  by_cases hq : q = 2 ∨ q = 3 <;> simp [hq]

/-- 读 true 恒为 1 分支。 -/
lemma subsetSumTransition_card_true (q : ℕ) : (subsetSumTransition q true).card = 1 := by
  unfold subsetSumTransition
  simp

/-- 读 true 的写符号恒为 true。 -/
lemma subsetSumTransition_true_write (q : ℕ) {r : ℕ × Bool × Dir}
    (hr : r ∈ subsetSumTransition q true) : r.2.1 = true := by
  unfold subsetSumTransition at hr
  simp at hr
  rcases hr with rfl
  rfl

/-- 转移结果的状态恒在 {0,1,2,3} 内。 -/
lemma subsetSumTransition_state_mem (q : ℕ) (s : Bool) {r : ℕ × Bool × Dir}
    (hr : r ∈ subsetSumTransition q s) : r.1 ∈ ({0,1,2,3} : Finset ℕ) := by
  unfold subsetSumTransition at hr
  cases s
  · by_cases hq : q = 2 ∨ q = 3 <;> simp [hq] at hr ⊢
    · rcases hr with rfl | rfl <;> decide
    · rcases hr with rfl | rfl <;> decide
  · simp at hr
    rcases hr with rfl <;> decide

/-- 经典非确定性子集和验证器（二分支，接受「全 false 串」）。 -/
def classicalSubsetSumNTM : ClassicalNTM :=
  {
    states      := {0,1,2,3}
    alphabet    := {false, true}
    transition  := subsetSumTransition
    startState  := 0
    acceptStates := {0}
    rejectStates := {2}
    h_start     := by simp
    h_accept    := by simp
    h_reject    := by simp
    h_disjoint  := by simp
  }

/-- `classicalSubsetSumNTM` 满足 `IsBinary`（可直接 `toNTM2`）。 -/
def classicalSubsetSumNTM_isBinary : ClassicalNTM.IsBinary classicalSubsetSumNTM :=
{
  vb := fun s => !s
  h_alphabet_full := by simp [classicalSubsetSumNTM]
  h_card := by
    intro q s hs
    cases s
    · right; exact subsetSumTransition_card_false q
    · left; exact subsetSumTransition_card_true q
  h_vb := by
    intro q s hs
    simp only [classicalSubsetSumNTM]
    cases s
    · simp [subsetSumTransition_card_false q]
    · simp [subsetSumTransition_card_true q]
  h_proj := by
    intro q s hs hvb r hr
    cases s
    · simp at hvb
    · have hw : r.2.1 = true := subsetSumTransition_true_write q hr
      rw [hw]
      simp
  h_accept_single := by simp [classicalSubsetSumNTM]
  h_reject_single := by simp [classicalSubsetSumNTM]
  h_state_mem := by
    intro q s hs r hr
    exact subsetSumTransition_state_mem q s hr
}

-- ============================================================================
-- 编码退化：natToBinaryF4 为空占位，subsetSumLanguageF4 退化为「全 false 串」
-- ============================================================================

lemma flatMap_const_singleton {α β : Type} (a : β) (l : List α) :
    List.flatMap (fun _ => [a]) l = List.replicate l.length a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap, ih, List.replicate_succ]

lemma map_replicate_re_alpha (n : ℕ) :
    List.map F4.re (List.replicate n F4.alpha) = List.replicate n false := by
  rw [List.map_replicate]
  simp [F4.alpha]

lemma encodeSubsetSumF4_re (inst : SubsetSumInstance) :
    List.map F4.re (encodeSubsetSumF4 inst) = List.replicate inst.elements.length false := by
  unfold encodeSubsetSumF4
  simp [natToBinaryF4, flatMap_const_singleton, map_replicate_re_alpha]

lemma encodeSubsetSumF4_eq_replicate (inst : SubsetSumInstance) :
    encodeSubsetSumF4 inst = List.replicate inst.elements.length F4.alpha := by
  unfold encodeSubsetSumF4
  simp [natToBinaryF4, flatMap_const_singleton]

lemma eq_replicate_of_all {α : Type} {a : α} {l : List α} (h : ∀ x ∈ l, x = a) :
    l = List.replicate l.length a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = a := h x (by simp)
    have hxs : ∀ y ∈ xs, y = a := by
      intro y hy; exact h y (by simp [hy])
    rw [hx]
    congr 1
    exact ih hxs

lemma subsetSumLanguageF4_all_false {bs : List Bool} :
    subsetSumLanguageF4 bs → ∀ b ∈ bs, b = false := by
  intro h
  rcases h with ⟨inst, hbs, T, hT_sub, hT_sum⟩
  rw [hbs, encodeSubsetSumF4_re]
  intro b hb
  exact (List.mem_replicate.mp hb).2

lemma all_false_subsetSumLanguageF4 {bs : List Bool} (hall : ∀ b ∈ bs, b = false) :
    subsetSumLanguageF4 bs := by
  let inst : SubsetSumInstance :=
    { elements := List.replicate bs.length 1, target := if bs.length = 0 then 0 else 1 }
  refine ⟨inst, ?_, ?_⟩
  · rw [encodeSubsetSumF4_re]
    simp [inst]
    exact eq_replicate_of_all hall
  · by_cases h : bs.length = 0
    · refine ⟨[], ?_, ?_⟩
      · intro a ha; simp at ha
      · simp [inst, h]
    · refine ⟨[1], ?_, ?_⟩
      · intro a ha
        simp [inst, List.mem_replicate, h] at ha ⊢
        omega
      · simp [inst, h]

lemma subsetSumLanguageF4_iff_all_false (bs : List Bool) :
    subsetSumLanguageF4 bs ↔ ∀ b ∈ bs, b = false := by
  constructor
  · exact subsetSumLanguageF4_all_false
  · exact all_false_subsetSumLanguageF4

-- ============================================================================
-- 状态机语义：classicalSubsetSumNTM 接受「全 false 串」
-- ============================================================================

lemma classicalEndState_append (N : ClassicalNTM) (π : ClassicalNTM.ComputationPath)
    (step : ClassicalNTM.TransitionStep) :
    ClassicalNTM.ComputationPath.endState N (π ++ [step]) = step.result.1 := by
  unfold ClassicalNTM.ComputationPath.endState
  rw [List.foldl_append]
  simp [List.foldl]

lemma reachable_endState_in_states {bs : List Bool} {π : ClassicalNTM.ComputationPath}
    (h : ClassicalNTM.ReachablePath classicalSubsetSumNTM bs π) :
    ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π ∈ ({0,1,2,3} : Finset ℕ) := by
  induction h with
  | nil => simp [ClassicalNTM.ComputationPath.endState, classicalSubsetSumNTM]
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      rw [classicalEndState_append]
      exact subsetSumTransition_state_mem
        (ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π₀) a h_trans

lemma subsetSumTransition_result_mem01_iff (q : ℕ) (a : Bool) {r : ℕ × Bool × Dir}
    (hr : r ∈ subsetSumTransition q a) (hq : q ∈ ({0,1,2,3} : Finset ℕ)) :
    r.1 ∈ ({0,1} : Finset ℕ) ↔ (q ∈ ({0,1} : Finset ℕ) ∧ a = false) := by
  simp at hq
  rcases hq with hq | hq | hq | hq
  · subst q; cases a <;> unfold subsetSumTransition at hr <;> simp at hr ⊢
    · rcases hr with rfl | rfl <;> decide
    · rcases hr with rfl <;> decide
  · subst q; cases a <;> unfold subsetSumTransition at hr <;> simp at hr ⊢
    · rcases hr with rfl | rfl <;> decide
    · rcases hr with rfl <;> decide
  · subst q; cases a <;> unfold subsetSumTransition at hr <;> simp at hr ⊢
    · rcases hr with rfl | rfl <;> decide
    · rcases hr with rfl <;> decide
  · subst q; cases a <;> unfold subsetSumTransition at hr <;> simp at hr ⊢
    · rcases hr with rfl | rfl <;> decide
    · rcases hr with rfl <;> decide

lemma reachable_all_false_iff_endState_01 {bs : List Bool} {π : ClassicalNTM.ComputationPath}
    (h : ClassicalNTM.ReachablePath classicalSubsetSumNTM bs π) :
    (∀ b ∈ bs, b = false) ↔
      ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π ∈ ({0,1} : Finset ℕ) := by
  induction h with
  | nil => simp [ClassicalNTM.ComputationPath.endState, classicalSubsetSumNTM]
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      rw [classicalEndState_append]
      rw [List.forall_mem_append, List.forall_mem_singleton]
      rw [ih]
      have hq : ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π₀ ∈ ({0,1,2,3} : Finset ℕ) :=
        reachable_endState_in_states h_ind
      have htrans' : step.result ∈ subsetSumTransition
          (ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π₀) a := by
        simpa [classicalSubsetSumNTM] using h_trans
      have hstep : step.result.1 ∈ ({0,1} : Finset ℕ) ↔
          (ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π₀ ∈ ({0,1} : Finset ℕ) ∧ a = false) :=
        subsetSumTransition_result_mem01_iff
          (ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π₀) a htrans' hq
      rw [hstep]

lemma accepts_nat_all_false_of {bs : List Bool} :
    ClassicalNTM.accepts_nat classicalSubsetSumNTM bs → ∀ b ∈ bs, b = false := by
  intro h
  rcases h with ⟨π, hr, hacc⟩
  have h01 : ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π ∈ ({0,1} : Finset ℕ) := by
    have heq : ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π = 0 := by
      simpa [classicalSubsetSumNTM] using hacc
    rw [heq]
    decide
  exact (reachable_all_false_iff_endState_01 hr).mpr h01

lemma accepts_nat_of_all_false {bs : List Bool} (hall : ∀ b ∈ bs, b = false) :
    ClassicalNTM.accepts_nat classicalSubsetSumNTM bs := by
  induction bs using List.reverseRecOn with
  | nil => exact ⟨[], ClassicalNTM.ReachablePath.nil, by simp [ClassicalNTM.ComputationPath.endState, classicalSubsetSumNTM]⟩
  | append_singleton bs' b ih =>
      have hb : b = false := hall b (by simp)
      have hbs' : ∀ x ∈ bs', x = false := by
        intro x hx; exact hall x (by simp [hx])
      rcases ih hbs' with ⟨π', hr', hacc'⟩
      have hend' : ClassicalNTM.ComputationPath.endState classicalSubsetSumNTM π' = 0 := by
        simpa [classicalSubsetSumNTM] using hacc'
      let step : ClassicalNTM.TransitionStep := { fromState := 0, readSym := false, result := (0, false, Dir.S) }
      refine ⟨π' ++ [step], ?_, ?_⟩
      · refine ClassicalNTM.ReachablePath.cons bs' b π' step hr' ?_ ?_ ?_
        · simp [step, hend']
        · simp [step, hb]
        · rw [hend', hb]
          change (0, false, Dir.S) ∈ subsetSumTransition 0 false
          simp [subsetSumTransition]
      · rw [classicalEndState_append]
        simp [step, classicalSubsetSumNTM]

lemma accepts_nat_iff_all_false (bs : List Bool) :
    ClassicalNTM.accepts_nat classicalSubsetSumNTM bs ↔ ∀ b ∈ bs, b = false := by
  constructor
  · exact accepts_nat_all_false_of
  · exact accepts_nat_of_all_false

lemma accepts_nat_iff_subsetSumLanguageF4 (bs : List Bool) :
    ClassicalNTM.accepts_nat classicalSubsetSumNTM bs ↔ subsetSumLanguageF4 bs := by
  rw [accepts_nat_iff_all_false]
  exact (subsetSumLanguageF4_iff_all_false bs).symm

-- 同构定理：将经典 NTM（IsBinary）转化为等价的 CBTM（真构造，不再是公理）

/-- 经典 NTM → CBTM：`toNTM2` 后接 `NTM2.toCBTM`。 -/
def ntm_to_cbtm (N : ClassicalNTM) (hN : ClassicalNTM.IsBinary N) : CBTM :=
  NTM2.toCBTM (ClassicalNTM.toNTM2 N hN)

/-- 多项式时间保持（isPolynomialTime 当前为 True 占位，故平凡成立）。 -/
theorem ntm_to_cbtm_poly_time (N : ClassicalNTM) (hN : ClassicalNTM.IsBinary N) :
    CBTM.isPolynomialTime (ntm_to_cbtm N hN) := by
  trivial

/-- 接受性保持（自然语义下，真定理）：accepts_bool (ntm_to_cbtm N) bs ↔ accepts_nat N bs。 -/
theorem ntm_to_cbtm_correct (N : ClassicalNTM) (hN : ClassicalNTM.IsBinary N) (bs : List Bool) :
    accepts_bool (ntm_to_cbtm N hN) bs ↔ ClassicalNTM.accepts_nat N bs := by
  rw [ntm_to_cbtm, accepts_bool_NTM2_toCBTM_iff]
  exact ClassicalNTM.toNTM2_accepts_nat_iff N hN bs

/-- NTM2 接受 x ⟹ toCBTM A 接受 vb 编码 toCBTMInput A x。 -/
lemma NTM2_toCBTM_accepts_toCBTMInput (A : NTM2) (x : List Bool) :
    NTM2.accepts A x → (NTM2.toCBTM A).accepts (NTM2.toCBTMInput A x) := by
  intro h
  rcases h with ⟨π, hr, hacc⟩
  refine ⟨ntm2PathToCBTM A π, reachable_NTM2_to_CBTM A hr, ?_⟩
  unfold ReachablePath.isAccepting
  rw [ntm2PathToCBTM_endState A π, toCBTM_acceptStates]
  exact (Bool.decide_iff _).mpr hacc

/-- classicalSubsetSumNTM 的 vb 使 false 为 2 分支（vb false = true）。 -/
lemma toNTM2_classical_vb_false :
    (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary).vb false = true := by
  simp [ClassicalNTM.toNTM2, classicalSubsetSumNTM_isBinary]

/-- 对 classicalSubsetSumNTM，toCBTMInput 的 vb 编码恰等于 encodeSubsetSumF4。 -/
lemma toCBTMInput_eq_encodeSubsetSumF4 (inst : SubsetSumInstance) :
    NTM2.toCBTMInput (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary)
      (List.map F4.re (encodeSubsetSumF4 inst)) = encodeSubsetSumF4 inst := by
  rw [encodeSubsetSumF4_re, encodeSubsetSumF4_eq_replicate]
  unfold NTM2.toCBTMInput
  rw [List.map_replicate]
  have hvb := toNTM2_classical_vb_false
  simp [f4OfVb, hvb, F4.alpha]

/-- 同构保持直接 F4 接受：classicalSubsetSumNTM 在布尔编码上接受，
    则 canonicalSubsetSumVerifier 在标准 F4 编码上也接受（真定理）。 -/
theorem canonicalSubsetSumVerifier_accepts_yes_f4 (inst : SubsetSumInstance)
    (h : ClassicalNTM.accepts_nat classicalSubsetSumNTM (List.map F4.re (encodeSubsetSumF4 inst))) :
    (ntm_to_cbtm classicalSubsetSumNTM classicalSubsetSumNTM_isBinary).accepts (encodeSubsetSumF4 inst) := by
  rw [ntm_to_cbtm]
  have h_ntm2 : NTM2.accepts (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary)
      (List.map F4.re (encodeSubsetSumF4 inst)) :=
    (ClassicalNTM.toNTM2_accepts_nat_iff classicalSubsetSumNTM classicalSubsetSumNTM_isBinary _).mpr h
  have h_acc : (NTM2.toCBTM (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary)).accepts
      (NTM2.toCBTMInput (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary)
        (List.map F4.re (encodeSubsetSumF4 inst))) :=
    NTM2_toCBTM_accepts_toCBTMInput (ClassicalNTM.toNTM2 classicalSubsetSumNTM classicalSubsetSumNTM_isBinary)
      (List.map F4.re (encodeSubsetSumF4 inst)) h_ntm2
  rw [toCBTMInput_eq_encodeSubsetSumF4 inst] at h_acc
  exact h_acc

-- ============================================================================
-- 规范验证器
-- ============================================================================

noncomputable def canonicalSubsetSumVerifier : CBTM :=
  ntm_to_cbtm classicalSubsetSumNTM classicalSubsetSumNTM_isBinary

lemma canonical_accepts_yes_instance (inst : SubsetSumInstance)
    (hYES : subsetSumLanguageF4 (List.map F4.re (encodeSubsetSumF4 inst))) :
    canonicalSubsetSumVerifier.accepts (encodeSubsetSumF4 inst) := by
  -- 从 hYES 得到存在子集和等于目标，从而经典 NTM 接受（需经典 NTM 的正确性证明）
  have h_ntm_accepts : ClassicalNTM.accepts_nat classicalSubsetSumNTM
      (List.map F4.re (encodeSubsetSumF4 inst)) :=
    (accepts_nat_iff_subsetSumLanguageF4 (List.map F4.re (encodeSubsetSumF4 inst))).mpr hYES
  exact canonicalSubsetSumVerifier_accepts_yes_f4 inst h_ntm_accepts

lemma canonical_correct :
    (∀ bs, accepts_bool canonicalSubsetSumVerifier bs ↔ subsetSumLanguageF4 bs) := by
  intro bs
  change accepts_bool (ntm_to_cbtm classicalSubsetSumNTM classicalSubsetSumNTM_isBinary) bs ↔
    subsetSumLanguageF4 bs
  rw [ntm_to_cbtm_correct classicalSubsetSumNTM classicalSubsetSumNTM_isBinary bs]
  exact accepts_nat_iff_subsetSumLanguageF4 bs

def IsCanonicalForSubsetSum (M : CBTM) : Prop :=
  (∀ inst, subsetSumLanguageF4 (List.map F4.re (encodeSubsetSumF4 inst)) →
           M.accepts (encodeSubsetSumF4 inst)) ∧
  (∀ bs, accepts_bool M bs ↔ subsetSumLanguageF4 bs)

theorem canonicalSubsetSumVerifier_isCanonical :
    IsCanonicalForSubsetSum canonicalSubsetSumVerifier :=
  ⟨canonical_accepts_yes_instance, canonical_correct⟩

-- ============================================================================
-- 子集和属于 NP
-- ============================================================================


end PvsNP
