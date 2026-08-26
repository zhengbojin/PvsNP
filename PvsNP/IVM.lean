/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mathlib
import PvsNP.Basic
import PvsNP.CBTM

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

open Set
open F4
open List

-- ======================================================================
-- 语言与实部投影
-- ======================================================================

/-- 语言是布尔串的集合。 -/
def Language : Type := Set (List Bool)

/-- 将 F4 列表投影为其实部组成的布尔列表。 -/
def List.toBoolList (w : List F4) : List Bool :=
  w.map F4.re

/-- CBTM 在布尔输入上的接受关系：存在一个实部等于该布尔串的 F4 串被机器接受。 -/
def accepts_bool (M : CBTM) (x : List Bool) : Prop :=
  ∃ w : List F4, List.toBoolList w = x ∧ M.accepts w

-- ======================================================================
-- NTM2 ↔ CBTM 的接受性等价
-- ======================================================================

/-- NTM2 输入在 CBTM 中的 F4 编码。 -/
def NTM2.toCBTMInput (A : NTM2) (x : List Bool) : List F4 :=
  x.map (fun b => f4OfVb A.vb b)

@[simp] theorem NTM2_toCBTMInput_toBoolList (A : NTM2) (x : List Bool) :
    List.toBoolList (NTM2.toCBTMInput A x) = x := by
  unfold NTM2.toCBTMInput List.toBoolList
  rw [List.map_map]
  have hcomp : F4.re ∘ (fun b : Bool => f4OfVb A.vb b) = fun b : Bool => b := by
    funext b
    simp [f4OfVb]
  rw [hcomp, List.map_id']

/-- CBTM 步 → NTM2 步。 -/
def cbtmStepToNTM2 (A : NTM2) (step : TransitionStep) : NTM2TransitionStep :=
  { fromState := step.fromState
    readSym := F4.re step.readSym
    result := (step.result.nextState, F4.re step.result.writeSym, step.result.moveDir) }

/-- NTM2 步 → CBTM 步。 -/
def ntm2StepToCBTM (A : NTM2) (step : NTM2TransitionStep) : TransitionStep :=
  { fromState := step.fromState
    readSym := f4OfVb A.vb step.readSym
    result := ⟨step.result.1, f4OfVb A.vb step.result.2.1, step.result.2.2⟩ }

/-- CBTM 路径 → NTM2 路径。 -/
def cbtmPathToNTM2 (A : NTM2) (π : ComputationPath) : NTM2ComputationPath :=
  π.map (cbtmStepToNTM2 A)

/-- NTM2 路径 → CBTM 路径。 -/
def ntm2PathToCBTM (A : NTM2) (π : NTM2ComputationPath) : ComputationPath :=
  π.map (ntm2StepToCBTM A)

/-- NTM2→CBTM 路径对应下末端状态不变。 -/
lemma ntm2PathToCBTM_endState (A : NTM2) (π : NTM2ComputationPath) :
    ComputationPath.endState (NTM2.toCBTM A) (ntm2PathToCBTM A π) =
      NTM2ComputationPath.endState A π := by
  unfold ComputationPath.endState NTM2ComputationPath.endState ntm2PathToCBTM
  rw [foldl_map_endState (ntm2StepToCBTM A) (fun s : TransitionStep => s.result.nextState)
    (fun s : NTM2TransitionStep => s.result.1) (NTM2.toCBTM A).startState π
    (by intro a; simp [ntm2StepToCBTM])]
  rw [toCBTM_startState]

/-- CBTM→NTM2 路径对应下末端状态不变。 -/
lemma cbtmPathToNTM2_endState (A : NTM2) (π : ComputationPath) :
    NTM2ComputationPath.endState A (cbtmPathToNTM2 A π) =
      ComputationPath.endState (NTM2.toCBTM A) π := by
  unfold ComputationPath.endState NTM2ComputationPath.endState cbtmPathToNTM2
  rw [foldl_map_endState (cbtmStepToNTM2 A) (fun s : NTM2TransitionStep => s.result.1)
    (fun s : TransitionStep => s.result.nextState) A.startState π
    (by intro a; simp [cbtmStepToNTM2])]
  rw [toCBTM_startState]

/-- NTM2 步的转移结果在 CBTM 中的像。 -/
lemma ntm2StepToCBTM_result_mem {A : NTM2} {q : ℕ} {a : Bool} {step : NTM2TransitionStep}
    (hstep : step.result ∈ A.transition q a) :
    (ntm2StepToCBTM A step).result ∈ (A.transition q a).image
        (fun r : ℕ × Bool × Dir => CBTMTransResult.mk r.1 (f4OfVb A.vb r.2.1) r.2.2) := by
  unfold ntm2StepToCBTM
  exact Finset.mem_image_of_mem
    (fun r : ℕ × Bool × Dir => CBTMTransResult.mk r.1 (f4OfVb A.vb r.2.1) r.2.2) hstep

/-- CBTM 步（在 toCBTM A 的可达步上）对应回 NTM2 转移。 -/
lemma cbtmStepToNTM2_result_mem {A : NTM2} {q : ℕ} {a : F4} {step : TransitionStep}
    (hstep : step.result ∈ (A.transition q (F4.re a)).image
        (fun r : ℕ × Bool × Dir => CBTMTransResult.mk r.1 (f4OfVb A.vb r.2.1) r.2.2)) :
    (cbtmStepToNTM2 A step).result ∈ A.transition q (F4.re a) := by
  rcases Finset.mem_image.mp hstep with ⟨r, hr, hr_eq⟩
  have hres : (cbtmStepToNTM2 A step).result = r := by
    simp [cbtmStepToNTM2]
    rw [← hr_eq]
    simp [f4OfVb]
  rw [hres]
  exact hr

/-- NTM2 → CBTM 保持可达性。 -/
lemma reachable_NTM2_to_CBTM (A : NTM2) {x : List Bool} {π : NTM2ComputationPath}
    (h : ReachablePathNTM2 A x π) :
    ReachablePath (NTM2.toCBTM A) (NTM2.toCBTMInput A x) (ntm2PathToCBTM A π) := by
  induction h with
  | nil => simpa [NTM2.toCBTMInput, ntm2PathToCBTM] using ReachablePath.nil
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      simp [NTM2.toCBTMInput, ntm2PathToCBTM]
      refine ReachablePath.cons (List.map (fun b => f4OfVb A.vb b) xs) (f4OfVb A.vb a)
        (ntm2PathToCBTM A π₀) (ntm2StepToCBTM A step) ih ?_ ?_ ?_
      · simp [ntm2StepToCBTM]
        rw [ntm2PathToCBTM_endState A π₀]
        exact h_from
      · simp [ntm2StepToCBTM]
        rw [h_read]
      · have hresult : (ntm2StepToCBTM A step).result ∈
            (A.transition (NTM2ComputationPath.endState A π₀) a).image
              (fun r : ℕ × Bool × Dir => CBTMTransResult.mk r.1 (f4OfVb A.vb r.2.1) r.2.2) :=
          ntm2StepToCBTM_result_mem h_trans
        rw [ntm2PathToCBTM_endState A π₀]
        rw [toCBTM_transition]
        rw [toCBTMTrans_eq_of_mem A (NTM2ComputationPath.endState A π₀) (f4OfVb A.vb a)
          (by exact (mem_NTM2AlphabetOf_iff A.vb (f4OfVb A.vb a)).2 rfl)]
        simpa [f4OfVb] using hresult

/-- CBTM → NTM2 保持可达性。 -/
lemma reachable_CBTM_to_NTM2 (A : NTM2) {w : List F4} {π' : ComputationPath}
    (h : ReachablePath (NTM2.toCBTM A) w π') :
    ReachablePathNTM2 A (List.toBoolList w) (cbtmPathToNTM2 A π') := by
  induction h with
  | nil => simpa [cbtmPathToNTM2, List.toBoolList] using ReachablePathNTM2.nil
  | cons xs a π₀ step h_ind h_from h_read h_trans ih =>
      simp [cbtmPathToNTM2, List.toBoolList]
      refine ReachablePathNTM2.cons (List.toBoolList xs) (F4.re a)
        (cbtmPathToNTM2 A π₀) (cbtmStepToNTM2 A step) ih ?_ ?_ ?_
      · simp [cbtmStepToNTM2]
        rw [cbtmPathToNTM2_endState A π₀]
        exact h_from
      · simp [cbtmStepToNTM2]
        rw [h_read]
      · have ha : a ∈ NTM2AlphabetOf A.vb := by
          have ha_alphabet : a ∈ (NTM2.toCBTM A).alphabet := by
            by_contra ha_not
            have h_empty : (NTM2.toCBTM A).transition
                (ComputationPath.endState (NTM2.toCBTM A) π₀, a) = ∅ :=
              (NTM2.toCBTM A).h_transition_outside
                (ComputationPath.endState (NTM2.toCBTM A) π₀) a ha_not
            rw [h_empty] at h_trans
            simp at h_trans
          simpa [toCBTM_alphabet] using ha_alphabet
        have htrans : step.result ∈
            (A.transition (ComputationPath.endState (NTM2.toCBTM A) π₀) (F4.re a)).image
              (fun r : ℕ × Bool × Dir => CBTMTransResult.mk r.1 (f4OfVb A.vb r.2.1) r.2.2) := by
          have ht : step.result ∈ NTM2.toCBTMTrans A
              (ComputationPath.endState (NTM2.toCBTM A) π₀, a) := by
            simpa [toCBTM_transition] using h_trans
          rw [toCBTMTrans_eq_of_mem A (ComputationPath.endState (NTM2.toCBTM A) π₀) a ha] at ht
          simpa using ht
        have hres : (cbtmStepToNTM2 A step).result ∈
            A.transition (ComputationPath.endState (NTM2.toCBTM A) π₀) (F4.re a) :=
          cbtmStepToNTM2_result_mem htrans
        rw [cbtmPathToNTM2_endState A π₀]
        exact hres

/-- NTM2 → CBTM 保持接受性：accepts_bool (toCBTM A) x ⟷ NTM2.accepts A x。 -/
theorem accepts_bool_NTM2_toCBTM_iff (A : NTM2) (x : List Bool) :
    accepts_bool (NTM2.toCBTM A) x ↔ NTM2.accepts A x := by
  constructor
  · intro h
    rcases h with ⟨w, hw, ⟨π', hr', ha'⟩⟩
    have hr : ReachablePathNTM2 A (List.toBoolList w) (cbtmPathToNTM2 A π') :=
      reachable_CBTM_to_NTM2 A hr'
    have hend : NTM2ComputationPath.endState A (cbtmPathToNTM2 A π') =
        ComputationPath.endState (NTM2.toCBTM A) π' :=
      cbtmPathToNTM2_endState A π'
    have hacc : NTM2ComputationPath.endState A (cbtmPathToNTM2 A π') ∈ A.acceptStates := by
      rw [hend]
      unfold ReachablePath.isAccepting at ha'
      simpa [toCBTM_acceptStates] using ((Bool.decide_iff _).mp ha')
    rw [← hw]
    exact ⟨cbtmPathToNTM2 A π', hr, hacc⟩
  · intro h
    rcases h with ⟨π, hr, hacc⟩
    refine ⟨NTM2.toCBTMInput A x, NTM2_toCBTMInput_toBoolList A x, ?_⟩
    refine ⟨ntm2PathToCBTM A π, reachable_NTM2_to_CBTM A hr, ?_⟩
    · unfold ReachablePath.isAccepting
      rw [ntm2PathToCBTM_endState A π, toCBTM_acceptStates]
      exact (Bool.decide_iff _).mpr hacc

/-- 多项式时间确定性语言类 P。 -/
structure IsP (L : Language) : Prop where
  exists_restricted : ∃ (M : CBTM), CBTM.IsRestricted M ∧ CBTM.isPolynomialTime M ∧
    (∀ x : List Bool, accepts_bool M x ↔ L x)

/-- 多项式时间非确定性语言类 NP。 -/
structure IsNP (L : Language) : Prop where
  exists_verifier : ∃ (M : CBTM), CBTM.isPolynomialTime M ∧
    (∀ x : List Bool, accepts_bool M x ↔ L x)

/-- 验证器集合。 -/
def Verifiers (L : Language) : Set CBTM :=
  { M | CBTM.isPolynomialTime M ∧ (∀ x : List Bool, accepts_bool M x ↔ L x) }

-- ======================================================================
-- 激活的生成元索引（用于 CBTM 的 kappa_M）
-- ======================================================================

/-- 辅助函数：递归扫描路径，记录虚部为 true 的步骤索引。 -/
def activatedGenIndicesOnPathAux : ComputationPath → ℕ → List ℕ
  | [], _ => []
  | step :: rest, idx =>
    if F4.im step.readSym then
      idx :: activatedGenIndicesOnPathAux rest (idx + 1)
    else
      activatedGenIndicesOnPathAux rest (idx + 1)

/-- 路径上激活的生成元索引列表（从 1 开始编号）。 -/
def activatedGenIndicesOnPath (π : ComputationPath) : List ℕ :=
  activatedGenIndicesOnPathAux π 1

/-- 路径上激活的生成元索引集合。 -/
def activatedGenSetOnPath (π : ComputationPath) : Finset ℕ :=
  (activatedGenIndicesOnPath π).toFinset

-- ======================================================================
-- kappa_M 及其性质（用于 CBTM）


-- ======================================================================
-- 核心引理：受限输入 → 路径读符号虚部全假
-- ======================================================================

/-- 若输入列表虚部全假，则任何可达路径上所有读符号虚部均为假。 -/
lemma reachable_steps_im_false_aux {M : CBTM} {xs : List F4} {π : ComputationPath}
    (hr : ReachablePath M xs π) :
    (∀ s ∈ xs, F4.im s = false) → ∀ step ∈ π, F4.im step.readSym = false := by
  induction hr with
  | nil =>
    intro h_im step hstep
    simp at hstep
  | cons xs' a π₀ step' h_ind h_from h_read h_trans ih =>
    intro h_im
    have hxs'_im : ∀ s ∈ xs', F4.im s = false := by
      intro s hs
      apply h_im s
      exact (List.mem_append.mpr (Or.inl hs))
    have ha_im : F4.im a = false := h_im a (by simp)
    have ih_steps : ∀ step ∈ π₀, F4.im step.readSym = false := ih hxs'_im
    intro step hstep
    rcases List.mem_append.mp hstep with (h | h)
    · exact ih_steps step h
    · rcases List.mem_singleton.mp h with rfl
      rw [h_read]
      exact ha_im

-- ======================================================================
-- 生成元（全局共用）与 IVM 虚拟机结构
-- ======================================================================

/-- 生成元：第 i 个素数平方根 √p_i。 -/
structure Generator where
  idx : ℕ    -- idx ≥ 1，对应第 idx 个素数平方根
  deriving DecidableEq, Repr

/-- 第 idx 个素数（p₁=2, p₂=3, p₃=5, ...）。 -/
def Generator.prime (g : Generator) : ℕ := g.idx

-- ======================================================================
-- CBTM 格局定义（独立于 CBTM 结构体）
-- ======================================================================

/-- CBTM 的格局：状态、纸带（Bool × Bool = F4）、带头位置。 -/
structure CBTMConfig (M : CBTM) (input : List F4) where
  state : ℕ
  tape : ℤ → F4
  headPos : ℤ

/-- 初始磁带：输入写在 [0, n)，其余为空白符号。 -/
def initialTapeOf (input : List F4) (blank : F4) : ℤ → F4 :=
  fun i => if h : 0 ≤ i ∧ i.toNat < input.length then input.get ⟨i.toNat, h.2⟩ else blank

/-- configAt 的步进函数（顶层化以便展开证明）。 -/
def configAtGo (M : CBTM) (input : List F4) (steps : List TransitionStep)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (remaining : ℕ) : CBTMConfig M input :=
  match steps, remaining with
  | [], _ =>
    { state := state,
      tape := tape,
      headPos := pos }
  | _ :: _, 0 =>
    { state := state,
      tape := tape,
      headPos := pos }
  | step :: rest, k+1 =>
    let newState := step.result.nextState
    let newTape := fun i => if i = pos then step.result.writeSym else tape i
    let newPos := pos + step.result.moveDir.toInt
    configAtGo M input rest newState newTape newPos k

/-- 从可达路径中获取第 t 步后的格局（t 从 0 开始计数，t=0 为初始格局）。 -/
def CBTM.configAt (M : CBTM) (input : List F4) (π : ComputationPath) (t : ℕ) : CBTMConfig M input :=
  configAtGo M input π M.startState (initialTapeOf input M.blankSym) 0 t

-- ======================================================================
-- 磁带语义：transition 前件第二项 = 当前磁带格子的编码
-- ======================================================================

/-- 格局中位置 i 处的 F4 符号。 -/
def CBTMConfig.tapeAt {M : CBTM} {input : List F4} (cfg : CBTMConfig M input) (i : ℤ) : F4 :=
  cfg.tape i

/-- 初始格局：输入写在 [0, n)，带头在 0，状态为初始状态。 -/
def initialConfig (M : CBTM) (input : List F4) : CBTMConfig M input :=
  { state := M.startState,
    tape := initialTapeOf input M.blankSym,
    headPos := 0 }

/-- 一步格局：写 writeSym 到带头位置，移动带头，更新状态。 -/
def stepConfig {M : CBTM} {input : List F4} (cfg : CBTMConfig M input) (r : CBTMTransResult) : CBTMConfig M input :=
  { state := r.nextState,
    tape := fun i => if i = cfg.headPos then r.writeSym else cfg.tape i,
    headPos := cfg.headPos + r.moveDir.toInt }

/-- 磁带语义的可达路径：每步读 headPos 处的磁带格子，写 writeSym，移动 moveDir。 -/
inductive TapeReachablePath (M : CBTM) (input : List F4) :
    ComputationPath → CBTMConfig M input → Prop
  | nil : TapeReachablePath M input [] (initialConfig M input)
  | cons : ∀ (π₀ : ComputationPath) (step : TransitionStep) (cfg : CBTMConfig M input),
      TapeReachablePath M input π₀ cfg →
      step.fromState = cfg.state →
      step.readSym = cfg.tapeAt cfg.headPos →
      step.result ∈ M.transition (cfg.state, cfg.tapeAt cfg.headPos) →
      TapeReachablePath M input (π₀ ++ [step]) (stepConfig cfg step.result)

/-- 磁带语义的接受：存在一条磁带可达路径，其末端状态在接受态。 -/
def CBTM.tapeAccepts (M : CBTM) (input : List F4) : Prop :=
  ∃ π : ComputationPath, ∃ cfg : CBTMConfig M input,
    TapeReachablePath M input π cfg ∧ cfg.state ∈ M.acceptStates
-- ======================================================================

/-- 单次验证的维度：最小接受路径上的激活生成元数（磁带语义）。 -/
noncomputable def kappa_M (M : CBTM) (x : List F4) : ℕ := by
  classical
  by_cases h : ∃ π, ∃ cfg : CBTMConfig M x,
      TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates
  · let P : ℕ → Prop := fun n =>
      ∃ π, ∃ cfg : CBTMConfig M x, TapeReachablePath M x π cfg ∧
        cfg.state ∈ M.acceptStates ∧ (activatedGenSetOnPath π).card = n
    have h_ex : ∃ n, P n := by
      rcases h with ⟨π, cfg, hr, ha⟩
      exact ⟨(activatedGenSetOnPath π).card, π, cfg, hr, ha, rfl⟩
    exact Nat.find h_ex
  · exact 0

lemma kappa_M_eq_zero_of_no_accept (M : CBTM) (x : List F4)
    (h : ¬∃ π, ∃ cfg : CBTMConfig M x,
      TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates) : kappa_M M x = 0 := by
  unfold kappa_M
  classical
  exact dif_neg h

lemma kappa_M_spec (M : CBTM) (x : List F4)
    (h_exists : ∃ π, ∃ cfg : CBTMConfig M x,
      TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates) :
    ∃ (π : ComputationPath), ∃ (cfg : CBTMConfig M x),
      TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates ∧
      (activatedGenSetOnPath π).card = kappa_M M x := by
  unfold kappa_M
  classical
  rw [dif_pos h_exists]
  let P : ℕ → Prop := fun n =>
    ∃ π, ∃ cfg : CBTMConfig M x, TapeReachablePath M x π cfg ∧
      cfg.state ∈ M.acceptStates ∧ (activatedGenSetOnPath π).card = n
  have h_ex : ∃ n, P n := by
    rcases h_exists with ⟨π, cfg, hr, ha⟩
    exact ⟨(activatedGenSetOnPath π).card, π, cfg, hr, ha, rfl⟩
  have h_spec := Nat.find_spec h_ex
  rcases h_spec with ⟨π, cfg, hr, ha, hcard⟩
  exact ⟨π, cfg, hr, ha, hcard⟩

lemma kappa_M_le_activatedGenSet (M : CBTM) (x : List F4) (π : ComputationPath)
    (cfg : CBTMConfig M x) (hreach : TapeReachablePath M x π cfg)
    (hacc : cfg.state ∈ M.acceptStates) :
    kappa_M M x ≤ (activatedGenSetOnPath π).card := by
  unfold kappa_M
  classical
  by_cases h_exists : ∃ π', ∃ cfg' : CBTMConfig M x,
      TapeReachablePath M x π' cfg' ∧ cfg'.state ∈ M.acceptStates
  · rw [dif_pos h_exists]
    let P : ℕ → Prop := fun n =>
      ∃ π', ∃ cfg' : CBTMConfig M x, TapeReachablePath M x π' cfg' ∧
        cfg'.state ∈ M.acceptStates ∧ (activatedGenSetOnPath π').card = n
    have h_ex : ∃ n, P n := by
      rcases h_exists with ⟨π₀, cfg₀, hr₀, ha₀⟩
      exact ⟨(activatedGenSetOnPath π₀).card, π₀, cfg₀, hr₀, ha₀, rfl⟩
    have mem : P ((activatedGenSetOnPath π).card) := ⟨π, cfg, hreach, hacc, rfl⟩
    exact Nat.find_min' h_ex mem
  · exfalso; exact h_exists ⟨π, cfg, hreach, hacc⟩

-- ======================================================================
-- 辅助引理：路径上所有读符号虚部为假 → 激活集合为空
-- ======================================================================

lemma activatedGenIndicesOnPathAux_eq_nil_of_im_false (π : ComputationPath) (start : ℕ)
    (h : ∀ step ∈ π, F4.im step.readSym = false) : activatedGenIndicesOnPathAux π start = [] := by
  induction π generalizing start with
  | nil => rfl
  | cons step tail ih =>
    have hstep : F4.im step.readSym = false := h step (by simp)
    have htail : ∀ s ∈ tail, F4.im s.readSym = false := by
      intro s hs; apply h s; exact List.mem_cons_of_mem _ hs
    unfold activatedGenIndicesOnPathAux
    simp [hstep, ih (start+1) htail]

lemma activatedGenIndicesOnPath_eq_nil_of_im_false (π : ComputationPath)
    (h : ∀ step ∈ π, F4.im step.readSym = false) : activatedGenIndicesOnPath π = [] := by
  unfold activatedGenIndicesOnPath
  exact activatedGenIndicesOnPathAux_eq_nil_of_im_false π 1 h

lemma activatedGenSetOnPath_empty_of_im_false (π : ComputationPath)
    (h : ∀ step ∈ π, F4.im step.readSym = false) : activatedGenSetOnPath π = ∅ := by
  simp [activatedGenSetOnPath, activatedGenIndicesOnPath_eq_nil_of_im_false π h]


-- ======================================================================
-- 受限 CBTM 的 kappa 恒为零
-- ======================================================================

/-- 磁带可达路径的每步读符号均在字母表内（result ∈ transition 非空 ⇒ 读符号 ∈ 字母表）。 -/
lemma tapeReachablePath_read_in_alphabet {M : CBTM} {x : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M x} (h : TapeReachablePath M x π cfg) :
    ∀ step ∈ π, step.readSym ∈ M.alphabet := by
  induction h with
  | nil => simp
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
    intro s hs
    rcases List.mem_append.mp hs with (hm | hm)
    · exact ih s hm
    · rcases List.mem_singleton.mp hm with rfl
      by_contra hnot
      have hempty : M.transition (cfg'.state, cfg'.tapeAt cfg'.headPos) = ∅ :=
        M.h_transition_outside (cfg'.state) (cfg'.tapeAt cfg'.headPos)
          (by simpa [h_read] using hnot)
      rw [hempty] at h_trans
      simp at h_trans

/-- 磁带语义：受限机器的路径读符号虚部全假（读符号 ∈ 字母表 ⊆ 实部符号）。 -/
lemma tapeReachable_steps_im_false {M : CBTM} {x : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M x} (h_rest : CBTM.IsRestricted M)
    (h : TapeReachablePath M x π cfg) :
    ∀ step ∈ π, F4.im step.readSym = false := by
  rcases h_rest with ⟨_, h_alphabet_im_false, _, _⟩
  intro step hstep
  exact h_alphabet_im_false step.readSym (tapeReachablePath_read_in_alphabet h step hstep)

theorem kappa_zero_of_restricted (M : CBTM) (x : List F4)
    (h_rest : CBTM.IsRestricted M) : kappa_M M x = 0 := by
  by_cases h_acc : ∃ π, ∃ cfg : CBTMConfig M x,
      TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates
  · rcases h_acc with ⟨π, cfg, hr, ha⟩
    have h_steps_im : ∀ step ∈ π, F4.im step.readSym = false :=
      tapeReachable_steps_im_false h_rest hr
    have h_empty : activatedGenSetOnPath π = ∅ :=
      activatedGenSetOnPath_empty_of_im_false π h_steps_im
    have hcard0 : (activatedGenSetOnPath π).card = 0 := by simp [h_empty]
    have h_le : kappa_M M x ≤ (activatedGenSetOnPath π).card :=
      kappa_M_le_activatedGenSet M x π cfg hr ha
    rw [hcard0] at h_le
    have h_nonneg : 0 ≤ kappa_M M x := Nat.zero_le _
    exact Nat.le_antisymm h_le h_nonneg
  · exact kappa_M_eq_zero_of_no_accept M x h_acc
-- ======================================================================
-- IVM 结构
-- ======================================================================

/-- IVM：包裹一个 CBTM 实例的虚拟机。 -/
structure IVM where
  machine : CBTM
  input   : List F4

/-- 第 t 步的 IVM 格局（依赖于具体路径 π）。 -/
def IVM.configAt (M : IVM) (π : ComputationPath) (t : ℕ) : CBTMConfig M.machine M.input :=
  CBTM.configAt M.machine M.input π t

/-- IVM 的磁带接受：内在 CBTM 的磁带语义接受。 -/
def IVM.tapeAccepts (M : IVM) : Prop :=
  CBTM.tapeAccepts M.machine M.input

-- ======================================================================
-- 分支次数定义
-- ======================================================================

/-- 路径中的分支次数（读符号虚部为 true 的步数）。 -/
def branchCount (π : ComputationPath) : ℕ :=
  (π.filter (fun step => F4.im step.readSym)).length

lemma branchCount_append (π : ComputationPath) (step : TransitionStep) :
    branchCount (π ++ [step]) = branchCount π + (if F4.im step.readSym then 1 else 0) := by
  unfold branchCount
  rw [List.filter_append, List.length_append]
  by_cases h : F4.im step.readSym
  · simp [h]
  · simp [h]

-- ======================================================================
-- 全局生成元集合（仅依赖分支次数 n）
-- ======================================================================

/-- 第 k 个分支的生成元索引（k 从 0 开始，索引为 k+1）。 -/
def genIdxOfBranch (k : ℕ) : ℕ := k + 1

/-- 第 k 个分支步骤对应的生成元（全局唯一，k 从 0 开始）。 -/
def genOfBranch (k : ℕ) : Generator :=
  Generator.mk (idx := genIdxOfBranch k)

lemma genOfBranch_inj (k₁ k₂ : ℕ) (h : genOfBranch k₁ = genOfBranch k₂) : k₁ = k₂ := by
  unfold genOfBranch genIdxOfBranch at h
  have h' : (Generator.mk (idx := k₁ + 1)).idx = (Generator.mk (idx := k₂ + 1)).idx := by rw [h]
  simp at h'
  omega

/-- 给定分支次数 n，对应的激活生成元集合（索引 1..n）。 -/
def activatedGensForBranchCount (n : ℕ) : Finset Generator :=
  (Finset.range n).image genOfBranch

@[simp] lemma card_activatedGensForBranchCount (n : ℕ) :
    (activatedGensForBranchCount n).card = n := by
  unfold activatedGensForBranchCount
  rw [Finset.card_image_of_injective _ (fun x y h => genOfBranch_inj x y h)]
  simp

lemma activatedGensForBranchCount_succ (n : ℕ) :
    activatedGensForBranchCount (n + 1) =
    activatedGensForBranchCount n ∪ {genOfBranch n} := by
  ext g
  constructor
  · intro hg
    rcases Finset.mem_image.mp hg with ⟨k, hk, rfl⟩
    have hk_le : k ≤ n := by
      have : k < n + 1 := Finset.mem_range.1 hk
      omega
    by_cases hk_lt : k < n
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.2 hk_lt, rfl⟩
    · have hk_eq : k = n := by omega
      subst k
      apply Finset.mem_union_right
      simp
  · intro hg
    rcases Finset.mem_union.mp hg with (hg | hg)
    · rcases Finset.mem_image.mp hg with ⟨k, hk, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_range.2 ?_, rfl⟩
      have : k < n := Finset.mem_range.1 hk
      omega
    · rcases Finset.mem_singleton.mp hg with rfl
      apply Finset.mem_image.mpr
      refine ⟨n, Finset.mem_range.2 ?_, rfl⟩
      omega

-- ======================================================================
-- IVM 中激活生成元集合：直接使用全局集合
-- ======================================================================

/-- 激活生成元集合：由路径的分支次数决定。 -/
def IVM.activatedGensOnPath (_M : IVM) (π : ComputationPath) : Finset Generator :=
  activatedGensForBranchCount (branchCount π)

-- ======================================================================
-- 关键引理：activatedGensOnPath 的递推关系（右附加一步）
-- ======================================================================

lemma activatedGensOnPath_append (M : IVM) (π : ComputationPath) (step : TransitionStep) :
    M.activatedGensOnPath (π ++ [step]) =
    M.activatedGensOnPath π ∪
    (if F4.im step.readSym then {genOfBranch (branchCount π)} else ∅) := by
  unfold IVM.activatedGensOnPath
  rw [branchCount_append]
  by_cases hbr : F4.im step.readSym
  · simp [hbr, activatedGensForBranchCount_succ]
  · simp [hbr]

-- ======================================================================
-- 基数等式：|activatedGensOnPath π| = branchCount π
-- ======================================================================

theorem IVM.activatedGenSet_card_eq_branchCount (M : IVM) (π : ComputationPath) :
    (M.activatedGensOnPath π).card = branchCount π := by
  unfold IVM.activatedGensOnPath
  simp

-- ======================================================================
-- IVM.kappa_M 的定义（基于激活生成元的最小基数）
-- ======================================================================

noncomputable def IVM.kappa_M (M : IVM) : ℕ := by
  classical
  by_cases h : ∃ π, ReachablePath M.machine M.input π ∧ ReachablePath.isAccepting M.machine π = true
  · let P : ℕ → Prop := fun n =>
      ∃ π, ReachablePath M.machine M.input π ∧ ReachablePath.isAccepting M.machine π = true ∧
        (M.activatedGensOnPath π).card = n
    have h_ex : ∃ n, P n := by
      rcases h with ⟨π, hr, ha⟩
      exact ⟨(M.activatedGensOnPath π).card, π, hr, ha, rfl⟩
    exact Nat.find h_ex
  · exact 0

-- ======================================================================
-- IVM 接受：语义展开器保持 CBTM 的接受判定
-- ======================================================================

/-- IVM 接受：内在 CBTM 存在一条接受路径（接受判定由 CBTM 完成，IVM 只是解释）。 -/
def IVM.accepts (M : IVM) : Prop :=
  ∃ π : ComputationPath, ReachablePath M.machine M.input π ∧
    ReachablePath.isAccepting M.machine π = true

-- ======================================================================
-- 单机 κ：所有接受路径中决策点（生成元）数目的最大值（路径最坏情形）
-- ======================================================================

/-- 单机 κ：所有接受路径中决策点（生成元）数目的最大值（路径最坏情形）。

    现有版本下（Finset 取代多重集，禁止无意义分支；每条接受路径消费整个输入）
    本机 κ 与单路径 κ 重合，但语义上仍取最大，以体现「路径最坏情形」。 -/
noncomputable def IVM.kappa (M : IVM) : ℕ :=
  sSup { n : ℕ | ∃ π : ComputationPath, ReachablePath M.machine M.input π ∧
    ReachablePath.isAccepting M.machine π = true ∧ branchCount π = n }

end PvsNP
