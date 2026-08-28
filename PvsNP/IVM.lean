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
      step.result ∈ M.transition (cfg.state, cfg.tapeAt cfg.headPos, cfg.headPos) →
      TapeReachablePath M input (π₀ ++ [step]) (stepConfig cfg step.result)

/-- 磁带语义的接受：存在一条磁带可达路径，其末端状态在接受态。 -/
def CBTM.tapeAccepts (M : CBTM) (input : List F4) : Prop :=
  ∃ π : ComputationPath, ∃ cfg : CBTMConfig M input,
    TapeReachablePath M input π cfg ∧ cfg.state ∈ M.acceptStates

/-- CBTM 的多项式时间（实化定义）：存在多项式界 p，任意接受路径长度 ≤ p(输入长度)。
    接受路径 = 磁带语义可达路径且末端状态在接受态。 -/
def CBTM.isPolynomialTime (M : CBTM) : Prop :=
  ∃ p : ℕ → ℕ, IsPolynomialBound p ∧
    ∀ (x : List F4) (π : ComputationPath) (cfg : CBTMConfig M x),
      TapeReachablePath M x π cfg → cfg.state ∈ M.acceptStates →
      π.length ≤ p x.length

-- ======================================================================
-- 经典 Bool 语言复杂度类（旧模型：实部投影的接受关系）
-- ======================================================================

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
      have hempty : M.transition (cfg'.state, cfg'.tapeAt cfg'.headPos, cfg'.headPos) = ∅ :=
        M.h_transition_outside (cfg'.state) (cfg'.tapeAt cfg'.headPos) cfg'.headPos
          (by simpa [h_read] using hnot)
      rw [hempty] at h_trans
      simp at h_trans

/-- 磁带语义：受限机器的路径读符号虚部全假（读符号 ∈ 字母表 = 实部符号）。 -/
lemma tapeReachable_steps_im_false {M : CBTM} {x : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M x} (h_rest : CBTM.IsRestricted M)
    (h : TapeReachablePath M x π cfg) :
    ∀ step ∈ π, F4.im step.readSym = false := by
  intro step hstep
  exact isRestricted_im_false h_rest step.readSym (tapeReachablePath_read_in_alphabet h step hstep)

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
  by_cases h : ∃ π, ReachablePath M.machine M.input 0 π ∧ ReachablePath.isAccepting M.machine π = true
  · let P : ℕ → Prop := fun n =>
      ∃ π, ReachablePath M.machine M.input 0 π ∧ ReachablePath.isAccepting M.machine π = true ∧
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
  ∃ π : ComputationPath, ReachablePath M.machine M.input 0 π ∧
    ReachablePath.isAccepting M.machine π = true

-- ======================================================================
-- 单机 κ：所有接受路径中决策点（生成元）数目的最大值（路径最坏情形）
-- ======================================================================

/-- 单机 κ：所有接受路径中决策点（生成元）数目的最大值（路径最坏情形）。

    现有版本下（Finset 取代多重集，禁止无意义分支；每条接受路径消费整个输入）
    本机 κ 与单路径 κ 重合，但语义上仍取最大，以体现「路径最坏情形」。 -/
noncomputable def IVM.kappa (M : IVM) : ℕ :=
  sSup { n : ℕ | ∃ π : ComputationPath, ReachablePath M.machine M.input 0 π ∧
    ReachablePath.isAccepting M.machine π = true ∧ branchCount π = n }

end PvsNP
