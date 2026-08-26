/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

/-
真实子集和编码、F4 语言与维度下界（经典 CBTM 磁带语义版）。

本文件实现论文（measure.C.0.7.tex 第 5 节）所要求的「带固定虚部的 F4 编码」：
  - 语言输入 = encodeSubsetSumF4Real inst（直接 F4 编码：每元素 = α 分支标记
    + 原生二进制，后接 target 二进制；不经过 Sym 编译层，不依赖验证器机器）；
  - α = (false, true) 是独立于元素值位的分支标记符号，虚部 = 1 标记 NTM2 分叉位置；
  - 元素值与目标值的二进制数据虚部恒 false。

信息论下界的关键：编码中虚部 = 1 的符号数恰为元素个数（imTrueCount_encodeSubsetSumF4Real），
而每条接受路径必须读每个激活位（accepting_path_reads_all_activated，翻转未读位的实部
→ 编码失效 → 语言值改变 → 矛盾），故分支次数 ≥ 元素个数（kappa_M_ge_imTrueCount）。

所有论证直接基于经典 CBTM 的磁带语义（TapeReachablePath / tapeAccepts，IVM.lean），
与验证器机器（SubsetSumVerifierCore / SubsetSumVerifierCBTM）完全解耦。
-/

import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM
import PvsNP.EssentialDimension
import PvsNP.LowerBound
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
-- 真实编码（不依赖 Sym 编译层：α 标记 + 原生二进制）
-- ============================================================================

/-- 自然数的二进制编码（最低位在前，虚部 false）。 -/
def natToBinaryF4Real (n : ℕ) : List F4 :=
  (Nat.digits 2 n).map boolToF4

/-- 每个元素 = alpha 分支标记（虚部 true）+ 元素二进制；后接 target 二进制。 -/
def encodeSubsetSumF4Real (inst : SubsetSumInstance) : List F4 :=
  inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s) ++ natToBinaryF4Real inst.target

-- 二进制编码的虚部全 false
lemma natToBinaryF4Real_im_false (n : ℕ) :
    ∀ s ∈ natToBinaryF4Real n, F4.im s = false := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
  simp [boolToF4]

lemma imTrueCount_natToBinaryF4Real (n : ℕ) :
    imTrueCount (natToBinaryF4Real n) = 0 := by
  unfold imTrueCount
  have hfilter : (natToBinaryF4Real n).filter (fun s => F4.im s) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    have him : F4.im s = false := natToBinaryF4Real_im_false n s hs
    simp [him]
  rw [hfilter]
  rfl

lemma imTrueCount_cons_alpha_binary (s : ℕ) :
    imTrueCount (F4.alpha :: natToBinaryF4Real s) = 1 := by
  unfold imTrueCount
  rw [List.filter_cons_of_pos (by simp [F4.alpha])]
  have hfilter : (natToBinaryF4Real s).filter (fun x => F4.im x) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    have him : F4.im x = false := natToBinaryF4Real_im_false s x hx
    simp [him]
  rw [hfilter]
  rfl

lemma imTrueCount_flatMap_alpha_binary (l : List ℕ) :
    imTrueCount (l.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [show (x :: xs).flatMap (fun s => F4.alpha :: natToBinaryF4Real s) =
        (F4.alpha :: natToBinaryF4Real x) ++
        xs.flatMap (fun s => F4.alpha :: natToBinaryF4Real s) from rfl]
      rw [imTrueCount_append, imTrueCount_cons_alpha_binary, ih]
      simp only [List.length_cons]
      omega

-- 编码中虚部 true 的符号数 = 元素个数
lemma imTrueCount_encodeSubsetSumF4Real (inst : SubsetSumInstance) :
    imTrueCount (encodeSubsetSumF4Real inst) = inst.elements.length := by
  unfold encodeSubsetSumF4Real
  rw [imTrueCount_append, imTrueCount_natToBinaryF4Real]
  simp [imTrueCount_flatMap_alpha_binary]

-- ============================================================================
-- F4 语言（带固定虚部的输入）
-- ============================================================================

/-- 子集和语言（F4 版本，真实编码）：输入 = encodeSubsetSumF4Real inst，
    虚部标记 = NTM2 分叉位置（α 元素选择点），实部 = 元素与目标值数据。
    空实例（elements = []）定义为非法（验证器状态 24 直接拒绝）。 -/
def subsetSumLanguageF4Real : FLanguage := fun w =>
  ∃ inst, w = encodeSubsetSumF4Real inst ∧ inst.elements ≠ [] ∧ subsetSumHolds inst

-- ============================================================================
-- flipReAt：翻转第 i 格的实部
-- ============================================================================

/-- 翻转第 i 格（0-based）的实部为 true。 -/
def flipReAt (w : List F4) (i : ℕ) : List F4 :=
  match w with
  | [] => []
  | s :: rest => if i = 0 then (true, s.2) :: rest else s :: flipReAt rest (i - 1)

/-- flipReAt 保持长度。 -/
lemma flipReAt_length (w : List F4) (i : ℕ) : (flipReAt w i).length = w.length := by
  induction w generalizing i with
  | nil => simp [flipReAt]
  | cons s rest ih =>
      simp [flipReAt]
      by_cases h : i = 0 <;> simp [h, ih]

/-- 翻转后第 i 格的实部为 true、虚部保持（i < w.length）。 -/
lemma flipReAt_getD_self (w : List F4) (i : ℕ) (hi : i < w.length) :
    (flipReAt w i).getD i F4.zero = (true, (w.getD i F4.zero).2) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          have hk : k < rest.length := by simp at hi; exact hi
          simp [flipReAt, List.getD_cons_succ]
          exact ih k hk

/-- 翻转后其他格的符号不变（j < w.length）。 -/
lemma flipReAt_getD_ne (w : List F4) (i j : ℕ) (hij : j ≠ i) (hj : j < w.length) :
    (flipReAt w i).getD j F4.zero = w.getD j F4.zero := by
  induction w generalizing i j with
  | nil => simp at hj
  | cons s rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exfalso; exact hij rfl
          | succ j' => simp [flipReAt]
      | succ i' =>
          cases j with
          | zero => simp [flipReAt]
          | succ j' =>
              have hj' : j' < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              exact ih i' j' (by omega) hj'

-- ============================================================================
-- 磁带格局辅助（configAt 链）
-- ============================================================================

/-- stepConfig 后带头位置的格被写入。 -/
lemma stepConfig_tapeAt_head {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) :
    (stepConfig cfg r).tapeAt cfg.headPos = r.writeSym := by
  unfold stepConfig CBTMConfig.tapeAt
  simp [if_pos rfl]

/-- stepConfig 后其他格不变。 -/
lemma stepConfig_tapeAt_ne {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) {j : ℤ} (hj : j ≠ cfg.headPos) :
    (stepConfig cfg r).tapeAt j = cfg.tapeAt j := by
  unfold stepConfig CBTMConfig.tapeAt
  simp [hj]

/-- configAtGo 的一步归约方程。 -/
lemma configAtGo_succ (M : CBTM) (input : List F4) (step : TransitionStep)
    (rest : ComputationPath) (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) :
    configAtGo M input (step :: rest) state tape pos (t + 1) =
      configAtGo M input rest step.result.nextState
        (fun i => if i = pos then step.result.writeSym else tape i)
        (pos + step.result.moveDir.toInt) t := rfl

/-- configAtGo 的零步方程。 -/
lemma configAtGo_zero (M : CBTM) (input : List F4) (steps : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) :
    configAtGo M input steps state tape pos 0 =
      { state := state, tape := tape,
        headPos := pos } := by
  cases steps <;> rfl

/-- configAtGo 只看前 t 步：前缀相同的路径在 t 处格局相同（任意起点）。 -/
lemma configAtGo_eq_of_take_eq (M : CBTM) (input : List F4) (π₁ π₂ : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) (h : π₁.take t = π₂.take t) :
    configAtGo M input π₁ state tape pos t = configAtGo M input π₂ state tape pos t := by
  induction t generalizing π₁ π₂ state tape pos with
  | zero => cases π₁ <;> cases π₂ <;> rfl
  | succ t ih =>
      cases π₁ with
      | nil =>
          cases π₂ with
          | nil => rfl
          | cons s₂ r₂ => simp at h
      | cons s₁ r₁ =>
          cases π₂ with
          | nil => simp at h
          | cons s₂ r₂ =>
              have hs : s₁ = s₂ := by
                have := congrArg (fun l : ComputationPath => l.getD 0 s₁) h
                simpa [List.getD_cons_zero] using this
              subst s₂
              have ht : r₁.take t = r₂.take t := by
                simpa using congrArg List.tail h
              rw [configAtGo_succ, configAtGo_succ]
              exact ih r₁ r₂ (state := s₁.result.nextState)
                (tape := fun i => if i = pos then s₁.result.writeSym else tape i)
                (pos := pos + s₁.result.moveDir.toInt) ht

/-- configAt 只看前 t 步：前缀相同的路径在 t 处格局相同。 -/
lemma configAt_eq_of_take_eq {M : CBTM} {input : List F4} {π₁ π₂ : ComputationPath}
    {t : ℕ} (h : π₁.take t = π₂.take t) :
    CBTM.configAt M input π₁ t = CBTM.configAt M input π₂ t := by
  unfold CBTM.configAt
  exact configAtGo_eq_of_take_eq M input π₁ π₂ M.startState (initialTapeOf input M.blankSym) 0 t h

/-- configAt 的前缀闭合：t ≤ π₀.length 时追加一步不影响前 t 步格局。 -/
lemma configAt_append_left {M : CBTM} {input : List F4} (π₀ : ComputationPath)
    (step : TransitionStep) {t : ℕ} (ht : t ≤ π₀.length) :
    CBTM.configAt M input (π₀ ++ [step]) t = CBTM.configAt M input π₀ t := by
  apply configAt_eq_of_take_eq
  rw [List.take_append_of_le_length (by omega)]

/-- configAtGo 的步进：第 (t+1) 步格局 = 第 t 步格局应用第 t 步转移（任意起点）。 -/
lemma configAtGo_succ_stepConfig (M : CBTM) (input : List F4) (π : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) (ht : t < π.length) :
    configAtGo M input π state tape pos (t + 1) =
      stepConfig (configAtGo M input π state tape pos t) (π.get ⟨t, ht⟩).result := by
  induction t generalizing π state tape pos with
  | zero =>
      cases π with
      | nil => simp at ht
      | cons s rest =>
          rw [Nat.zero_add, configAtGo_succ]
          simp [stepConfig, configAtGo_zero]
  | succ t ih =>
      cases π with
      | nil => simp at ht
      | cons s rest =>
          have ht' : t < rest.length := by
            simp at ht
            exact ht
          have := ih (π := rest) (state := s.result.nextState)
            (tape := fun i => if i = pos then s.result.writeSym else tape i)
            (pos := pos + s.result.moveDir.toInt) ht'
          rw [configAtGo_succ, configAtGo_succ]
          simpa using this

/-- configAt 的步进：第 (t+1) 步格局 = 第 t 步格局应用第 t 步转移。 -/
lemma configAt_succ_stepConfig (M : CBTM) (input : List F4) (π : ComputationPath)
    (t : ℕ) (ht : t < π.length) :
    CBTM.configAt M input π (t + 1) =
      stepConfig (CBTM.configAt M input π t) (π.get ⟨t, ht⟩).result := by
  unfold CBTM.configAt
  exact configAtGo_succ_stepConfig M input π M.startState (initialTapeOf input M.blankSym) 0 t ht

-- ============================================================================
-- 下界核心（磁带语义）：TapeReachablePath 版
-- ============================================================================

/-- 磁带路径桥：TapeReachablePath 末端格局的头位置与状态 = configAt 链（headPos/state 与磁带无关）。 -/
lemma tapeReachable_state_head_eq_configAt {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeReachablePath M input π cfg) :
    cfg.state = (CBTM.configAt M input π π.length).state ∧
      cfg.headPos = (CBTM.configAt M input π π.length).headPos := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    cfg'.state = (CBTM.configAt M input π' π'.length).state ∧
    cfg'.headPos = (CBTM.configAt M input π' π'.length).headPos
  change P π cfg
  induction h with
  | nil => constructor <;> rfl
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
      have hget : ((π₀ ++ [step]).get ⟨π₀.length, by simp⟩) = step := by
        simp [List.getElem_append_right, List.getElem_cons_zero]
      rcases ih with ⟨hst₀, hhp₀⟩
      constructor
      · rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
        rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
        rw [configAt_append_left π₀ step (by omega)]
        rw [hget]
        rfl
      · rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
        rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
        rw [configAt_append_left π₀ step (by omega)]
        rw [hget]
        unfold stepConfig
        rw [hhp₀]

/-- 核心：未读格 i 的翻转不影响路径（磁带语义，任意机器）。 -/
lemma tapeReachable_sim_under_unread_update {M : CBTM} {w w' : List F4} {π : ComputationPath}
    {i : ℤ} {cfg : CBTMConfig M w}
    (h : TapeReachablePath M w π cfg)
    (hinit : ∀ j : ℤ, j ≠ i → (initialConfig M w).tapeAt j = (initialConfig M w').tapeAt j)
    (hskip : ∀ t, t < π.length → (CBTM.configAt M w π t).headPos ≠ i) :
    ∃ cfg' : CBTMConfig M w', TapeReachablePath M w' π cfg' ∧
      cfg.state = cfg'.state ∧ cfg.headPos = cfg'.headPos ∧
      ∀ j : ℤ, j ≠ i → cfg.tapeAt j = cfg'.tapeAt j := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M w)
      (hsk : ∀ t, t < π'.length → (CBTM.configAt M w π' t).headPos ≠ i) : Prop :=
    ∃ cfg'' : CBTMConfig M w', TapeReachablePath M w' π' cfg'' ∧
      cfg'.state = cfg''.state ∧ cfg'.headPos = cfg''.headPos ∧
      ∀ j : ℤ, j ≠ i → cfg'.tapeAt j = cfg''.tapeAt j
  have hP : P π cfg hskip := by
    induction h with
    | nil =>
        exact ⟨initialConfig M w', TapeReachablePath.nil, rfl, rfl, hinit⟩
    | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
        have hskip₀' : ∀ t, t < π₀.length → (CBTM.configAt M w π₀ t).headPos ≠ i := by
          intro t ht
          rw [← configAt_append_left (M := M) (input := w) π₀ step (by omega)]
          exact hskip t (by rw [List.length_append]; omega)
        rcases ih hskip₀' with ⟨cfg₀', hπ₀', hst₀, hhp₀, htp₀⟩
        have hcfg₀_head_ne : cfg₀.headPos ≠ i := by
          rcases tapeReachable_state_head_eq_configAt h_ind with ⟨_, hhp⟩
          have hhp' : (CBTM.configAt M w π₀ π₀.length).headPos ≠ i := by
            have hh : (CBTM.configAt M w (π₀ ++ [step]) π₀.length).headPos ≠ i :=
              hskip π₀.length (by simp [List.length_append])
            rwa [configAt_append_left π₀ step (by omega)] at hh
          rwa [← hhp] at hhp'
        have hread' : step.readSym = cfg₀'.tapeAt cfg₀'.headPos := by
          rw [h_read]
          rw [← hhp₀]
          rw [← htp₀ cfg₀.headPos hcfg₀_head_ne]
        have htrans' : step.result ∈ M.transition (cfg₀'.state, cfg₀'.tapeAt cfg₀'.headPos) := by
          have hst' : cfg₀'.state = step.fromState := by rw [← hst₀, ← h_from]
          rw [hst']
          rw [h_from]
          rw [← hhp₀]
          rw [← htp₀ cfg₀.headPos hcfg₀_head_ne]
          exact h_trans
        refine ⟨stepConfig cfg₀' step.result,
          TapeReachablePath.cons π₀ step cfg₀' hπ₀' (by rw [h_from, hst₀]) hread' htrans', ?_⟩
        constructor
        · rfl
        constructor
        · unfold stepConfig
          rw [hhp₀]
        · intro j hj
          by_cases hh : j = cfg₀.headPos
          · subst j
            rw [stepConfig_tapeAt_head (cfg := cfg₀) (r := step.result)]
            rw [hhp₀]
            rw [stepConfig_tapeAt_head (cfg := cfg₀') (r := step.result)]
          · rw [stepConfig_tapeAt_ne (cfg := cfg₀) (r := step.result) (by exact hh)]
            have hh' : j ≠ cfg₀'.headPos := by
              rw [← hhp₀]
              exact hh
            rw [stepConfig_tapeAt_ne (cfg := cfg₀') (r := step.result) hh']
            exact htp₀ j hj
  change P π cfg hskip at hP
  exact hP

/-- 未读格翻转不改变接受性。 -/
lemma tapeAccepts_insensitive_to_unread_update {M : CBTM} {w w' : List F4} {i : ℤ}
    {π : ComputationPath} {cfg : CBTMConfig M w}
    (hr : TapeReachablePath M w π cfg) (ha : cfg.state ∈ M.acceptStates)
    (hinit : ∀ j : ℤ, j ≠ i → (initialConfig M w).tapeAt j = (initialConfig M w').tapeAt j)
    (hskip : ∀ t, t < π.length → (CBTM.configAt M w π t).headPos ≠ i) :
    M.tapeAccepts w' := by
  rcases tapeReachable_sim_under_unread_update hr hinit hskip with
    ⟨cfg', hr', hst, hhp, _⟩
  refine ⟨π, cfg', hr', ?_⟩
  rwa [← hst]

-- ============================================================================
-- getD 辅助
-- ============================================================================

/-- getD 在界内恰为 get（core 环境无 get? 界内引理，归纳直证）。 -/
lemma getD_eq_get {α : Type} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d = l.get ⟨i, hi⟩ := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          rw [List.getD_cons_succ]
          have hk : k < rest.length := by simp at hi; exact hi
          rw [ih k hk]
          change (a :: rest)[k + 1]'hi = rest[k]'hk
          rw [List.getElem_cons (i := k + 1)]
          simp

/-- 翻转后其他格的符号不变（get 版，归纳直证）。 -/
lemma flipReAt_get_ne (w : List F4) (i j : ℕ) (hij : j ≠ i) (hj : j < w.length) :
    (flipReAt w i).get ⟨j, by simpa [flipReAt_length] using hj⟩ = w.get ⟨j, hj⟩ := by
  induction w generalizing i j with
  | nil => simp at hj
  | cons s rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exfalso; exact hij rfl
          | succ k =>
              have hk : k < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              first | done | exact ih 0 k (by omega) hk
      | succ i' =>
          cases j with
          | zero => simp [flipReAt]
          | succ k =>
              have hk : k < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              first | done | exact ih i' k (by omega) hk

/-- getD 越过前缀：l₁.length ≤ i 时 (l₁ ++ l₂).getD i = l₂.getD (i - l₁.length)。 -/
lemma getD_append_drop (l₁ l₂ : List F4) (i : ℕ) (d : F4)
    (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  induction l₁ generalizing i with
  | nil => simp
  | cons a rest ih =>
      cases i with
      | zero => simp at hi
      | succ k =>
          rw [List.cons_append]
          rw [List.getD_cons_succ]
          have hk : rest.length ≤ k := by simp at hi; exact hi
          rw [show (a :: rest).length = rest.length + 1 by rfl]
          rw [Nat.add_sub_add_right]
          exact ih k hk

-- ============================================================================
-- 真实编码结构引理
-- ============================================================================

/-- flatMap 块（α :: 二进制）中虚部 true 的格实部必为 false（激活位恒为 α = (false, true)）。 -/
lemma im_true_re_false_flatMap_alpha (l : List ℕ) :
    ∀ i, i < (l.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length →
      F4.im ((l.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD i F4.zero) = true →
      ((l.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD i F4.zero).1 = false := by
  intro i hi him
  induction l generalizing i with
  | nil => simp at hi
  | cons v rest ih =>
      rw [show (v :: rest).flatMap (fun s => F4.alpha :: natToBinaryF4Real s) =
        (F4.alpha :: natToBinaryF4Real v) ++
        rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s) from rfl] at hi him ⊢
      by_cases hi_b : i < (F4.alpha :: natToBinaryF4Real v).length
      · have hget : ((F4.alpha :: natToBinaryF4Real v) ++
            rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD i F4.zero =
            (F4.alpha :: natToBinaryF4Real v).getD i F4.zero :=
          List.getD_append (F4.alpha :: natToBinaryF4Real v)
            (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) F4.zero i hi_b
        rw [hget] at him ⊢
        cases i with
        | zero => rfl
        | succ k =>
            have hk : k < (natToBinaryF4Real v).length := by
              simp [Nat.succ_lt_succ_iff] at hi_b
              exact hi_b
            have hk' : k < (natToBinaryF4Real v).length := by
              simpa using hk
            have him_bits : F4.im ((natToBinaryF4Real v).getD k F4.zero) = false :=
              natToBinaryF4Real_im_false v ((natToBinaryF4Real v).getD k F4.zero)
                (by
                  rw [getD_eq_get (natToBinaryF4Real v) k F4.zero hk']
                  exact List.getElem_mem hk')
            rw [List.getD_cons_succ] at him
            rw [him_bits] at him
            simp at him
      · have hirest : i - (F4.alpha :: natToBinaryF4Real v).length <
            (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length := by
          rw [List.length_append] at hi
          have hge : (F4.alpha :: natToBinaryF4Real v).length ≤ i := by omega
          have h1 : i - (F4.alpha :: natToBinaryF4Real v).length <
              ((F4.alpha :: natToBinaryF4Real v).length +
                (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length) -
                (F4.alpha :: natToBinaryF4Real v).length :=
            Nat.sub_lt_sub_right hge hi
          have h2 : ((F4.alpha :: natToBinaryF4Real v).length +
              (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length) -
              (F4.alpha :: natToBinaryF4Real v).length =
              (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length :=
            Nat.add_sub_cancel_left (F4.alpha :: natToBinaryF4Real v).length
              (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length
          rwa [h2] at h1
        have hget : ((F4.alpha :: natToBinaryF4Real v) ++
            rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD i F4.zero =
            (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD
              (i - (F4.alpha :: natToBinaryF4Real v).length) F4.zero := by
          rw [getD_append_drop (F4.alpha :: natToBinaryF4Real v)
            (rest.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) i F4.zero
            (by exact Nat.le_of_not_gt hi_b)]
        rw [hget] at him ⊢
        exact ih (i - (F4.alpha :: natToBinaryF4Real v).length) hirest him

/-- 真实编码中虚部 true 的格实部必为 false（激活位恒为 α = (false, true)）。 -/
lemma encodeSubsetSumF4Real_im_true_re_false (inst : SubsetSumInstance) :
    ∀ i, i < (encodeSubsetSumF4Real inst).length →
      F4.im ((encodeSubsetSumF4Real inst).getD i F4.zero) = true →
      ((encodeSubsetSumF4Real inst).getD i F4.zero).1 = false := by
  intro i hi him
  unfold encodeSubsetSumF4Real at hi him ⊢
  by_cases hi_e : i < (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length
  · have hget : ((inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) ++
        natToBinaryF4Real inst.target).getD i F4.zero =
        (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).getD i F4.zero :=
      List.getD_append (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s))
        (natToBinaryF4Real inst.target) F4.zero i hi_e
    rw [hget] at him ⊢
    exact im_true_re_false_flatMap_alpha inst.elements i hi_e him
  · have htarget : F4.im ((natToBinaryF4Real inst.target).getD
        (i - (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length) F4.zero) = false :=
      natToBinaryF4Real_im_false inst.target
        ((natToBinaryF4Real inst.target).getD
          (i - (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length) F4.zero)
        (by
          have hlen : i - (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length <
              (natToBinaryF4Real inst.target).length := by
            rw [List.length_append] at hi
            omega
          rw [getD_eq_get (natToBinaryF4Real inst.target)
            (i - (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length)
            F4.zero hlen]
          exact List.getElem_mem hlen)
    have hget : ((inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) ++
        natToBinaryF4Real inst.target).getD i F4.zero =
        (natToBinaryF4Real inst.target).getD
          (i - (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)).length) F4.zero := by
      rw [getD_append_drop (inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s))
        (natToBinaryF4Real inst.target) i F4.zero
        (by exact Nat.le_of_not_gt hi_e)]
    rw [hget] at him
    rw [htarget] at him
    simp at him

/-- 翻转激活位（虚部 true 的格）实部后不再是合法编码：真实编码的激活位恒为 α，
    而 flipReAt 使该格实部变 true，与「虚部 true ⟹ 实部 false」矛盾。 -/
lemma flipReAt_activated_not_in_L (inst : SubsetSumInstance) (i : ℕ)
    (hi : i < (encodeSubsetSumF4Real inst).length)
    (him : F4.im ((encodeSubsetSumF4Real inst).getD i F4.zero) = true)
    (hL : subsetSumLanguageF4Real (flipReAt (encodeSubsetSumF4Real inst) i)) : False := by
  rcases hL with ⟨inst', henc, _hne', _hholds⟩
  have hself : (flipReAt (encodeSubsetSumF4Real inst) i).getD i F4.zero =
      (true, ((encodeSubsetSumF4Real inst).getD i F4.zero).2) :=
    flipReAt_getD_self (encodeSubsetSumF4Real inst) i hi
  have hre_true : ((flipReAt (encodeSubsetSumF4Real inst) i).getD i F4.zero).1 = true := by
    rw [hself]
  have hlen' : i < (encodeSubsetSumF4Real inst').length := by
    rw [← henc]
    rw [flipReAt_length]
    exact hi
  have him' : F4.im ((encodeSubsetSumF4Real inst').getD i F4.zero) = true := by
    rw [← henc]
    rw [hself]
    exact him
  have hre_false : ((encodeSubsetSumF4Real inst').getD i F4.zero).1 = false :=
    encodeSubsetSumF4Real_im_true_re_false inst' i hlen' him'
  rw [henc] at hre_true
  rw [hre_false] at hre_true
  exact Bool.noConfusion hre_true

-- ============================================================================
-- 下界核心（磁带语义）：正确机器必须读取每个虚部 true 的激活位。
-- 磁带语义下接受路径不必消费整个输入，故「读序列 = 输入」不再免费；
-- 必读性由「翻转未读激活位的实部 → 编码失效 → 语言值改变」推出。
-- ============================================================================

/-- TapeReachablePath 末端格局的 headPos 在 configAt 链中的位置（t₀ 内带头从不落在 i）。 -/
lemma tapeReachable_tapeAt_eq_of_head_ne {M : CBTM} {input : List F4} {π : ComputationPath}
    {i : ℤ} {t₀ : ℕ}
    (hne : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i) :
    (CBTM.configAt M input π (min t₀ π.length)).tapeAt i = (initialConfig M input).tapeAt i := by
  induction t₀ generalizing π with
  | zero => simp [CBTM.configAt, configAtGo_zero, CBTMConfig.tapeAt, initialConfig]
  | succ t₀ ih =>
      by_cases ht : t₀ < π.length
      · have hm : min (t₀ + 1) π.length = min t₀ π.length + 1 := by omega
        rw [hm]
        have hstepm : (CBTM.configAt M input π (min t₀ π.length + 1)) =
            stepConfig (CBTM.configAt M input π (min t₀ π.length))
              (π.get ⟨min t₀ π.length, by omega⟩).result :=
          configAt_succ_stepConfig M input π (min t₀ π.length) (by omega)
        rw [hstepm]
        have hpos_ne : (CBTM.configAt M input π (min t₀ π.length)).headPos ≠ i :=
          hne (min t₀ π.length) (by omega)
        rw [stepConfig_tapeAt_ne (cfg := (CBTM.configAt M input π (min t₀ π.length)))
          (r := (π.get ⟨min t₀ π.length, by omega⟩).result) hpos_ne.symm]
        have hne' : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i := by
          intro t ht'
          exact hne t (by omega)
        exact ih hne'
      · -- min (t₀+1) π.length = π.length = min t₀ π.length（t₀ ≥ π.length）
        have hm' : min (t₀ + 1) π.length = min t₀ π.length := by omega
        rw [hm']
        have hne' : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i := by
          intro t ht'
          exact hne t (by omega)
        exact ih hne'

/-- TapeReachablePath 的末端格局恰为 configAt 的末端格局。 -/
lemma tapeReachable_cfg_eq_configAt {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeReachablePath M input π cfg) :
    cfg = CBTM.configAt M input π π.length := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    cfg' = CBTM.configAt M input π' π'.length
  change P π cfg
  induction h with
  | nil => rfl
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      rw [ih]
      change stepConfig (CBTM.configAt M input π₀ π₀.length) step.result =
        CBTM.configAt M input (π₀ ++ [step]) (List.length (π₀ ++ [step]))
      rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
      rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
      rw [configAt_append_left π₀ step (by omega)]
      rw [show (π₀ ++ [step]).get ⟨π₀.length, by simp⟩ = step by
        simp [List.getElem_append_right, List.getElem_cons_zero]]

/-- 第 t 步读的符号 = 第 t 步格局带头处的符号。 -/
lemma tapeReachable_readSym_at {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeReachablePath M input π cfg)
    (t : ℕ) (ht : t < π.length) :
    (π.get ⟨t, ht⟩).readSym =
      (CBTM.configAt M input π t).tapeAt (CBTM.configAt M input π t).headPos := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    ∀ t (ht : t < π'.length), (π'.get ⟨t, ht⟩).readSym =
      (CBTM.configAt M input π' t).tapeAt (CBTM.configAt M input π' t).headPos
  revert t ht
  change P π cfg
  induction h with
  | nil => intro t ht; simp at ht
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      intro t ht
      by_cases hte : t = π₀.length
      · subst t
        have hget : ((π₀ ++ [step]).get ⟨π₀.length, by simp⟩) = step := by
          simp [List.getElem_append_right, List.getElem_cons_zero]
        rw [hget, h_read]
        have hcfg : cfg₀ = CBTM.configAt M input (π₀ ++ [step]) π₀.length := by
          have h1 : cfg₀ = CBTM.configAt M input π₀ π₀.length := tapeReachable_cfg_eq_configAt h_ind
          rw [h1]
          rw [configAt_append_left π₀ step (by omega)]
        rw [hcfg]
      · have ht₀ : t < π₀.length := by
          simp [List.length_append] at ht
          omega
        have hget : ((π₀ ++ [step]).get ⟨t, by simp; omega⟩) = π₀.get ⟨t, ht₀⟩ := by
          exact List.getElem_append_left (α := TransitionStep) (as := π₀) (bs := [step])
            (i := t) ht₀
        rw [hget]
        rw [ih t ht₀]
        have hpre : (π₀ ++ [step]).take t = π₀.take t := by
          rw [List.take_append_of_le_length (by exact Nat.le_of_lt ht₀)]
        simpa only [configAt_eq_of_take_eq (M := M) (input := input) (t := t) hpre]

/-- 激活索引列表的元素都 ≥ start（1-based 起点的单调性）。 -/
lemma not_mem_activatedGenIndicesOnPathAux_lt (π : ComputationPath) (start idx : ℕ)
    (hlt : idx < start) : idx ∉ activatedGenIndicesOnPathAux π start := by
  induction π generalizing start idx with
  | nil => simp [activatedGenIndicesOnPathAux]
  | cons step rest ih =>
      unfold activatedGenIndicesOnPathAux
      by_cases him : step.readSym.im = true
      · rw [if_pos him]
        rw [List.mem_cons]
        intro h
        rcases h with h | h
        · subst h
          omega
        · exact (ih (start + 1) idx (Nat.lt_trans hlt (Nat.lt_succ_self start))) h
      · rw [if_neg him]
        exact ih (start + 1) idx (Nat.lt_trans hlt (Nat.lt_succ_self start))

/-- 激活索引列表（1-based）的成员：start + idx ∈ 列表 ⟺ 第 idx 步读符号虚部为 true。 -/
lemma mem_activatedGenIndicesOnPathAux (π : ComputationPath) (start idx : ℕ)
    (hidx : idx < π.length) :
    start + idx ∈ activatedGenIndicesOnPathAux π start ↔
      F4.im ((π.getD idx Inhabited.default).readSym) = true := by
  induction π generalizing start idx with
  | nil => simp at hidx
  | cons step rest ih =>
      by_cases hidx0 : idx = 0
      · subst idx
        unfold activatedGenIndicesOnPathAux
        by_cases him : step.readSym.im = true
        · simp [him, List.getD_cons_zero]
        · rw [if_neg him, List.getD_cons_zero]
          have hnot : step.readSym.im = true ↔ False := by
            constructor
            · intro h; exact him h
            · intro h; cases h
          rw [hnot, iff_false]
          intro h
          apply (not_mem_activatedGenIndicesOnPathAux_lt rest (start + 1) start
            (Nat.lt_succ_self start))
          simpa using h
      · rcases idx with _ | k
        · contradiction
        · have hk : k < rest.length := by simp at hidx; exact hidx
          have := ih (start := start + 1) (idx := k) hk
          unfold activatedGenIndicesOnPathAux
          by_cases him : step.readSym.im = true
          · simp [him, hidx0, List.getD_cons_succ]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
          · simp [him, hidx0, List.getD_cons_succ]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

-- range 的 cons 分解（尾元素版 range_succ 与 w 的 cons 结构不对齐，需此形式）
lemma range_cons_succ (n : ℕ) : List.range (n + 1) = 0 :: (List.range n).map (fun i => i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ]
      conv_lhs => rw [ih]
      rw [List.cons_append]
      rw [List.range_succ, List.map_append, List.map_singleton]
      first | done | rfl

/-- range 索引 filter 计数 = 列表 filter 计数（core 无 List.enum 的替代）。 -/
lemma length_filter_map_add (l : List ℕ) (p : ℕ → Bool) :
    ((l.map (fun i => i + 1)).filter p).length = (l.filter (fun i => p (i + 1))).length := by
  rw [List.filter_map, List.length_map]
  rfl

lemma length_filter_range_getD (w : List F4) :
    ((List.range w.length).filter (fun i => F4.im (w.getD i F4.zero) = true)).length =
      (w.filter (fun s : F4 => F4.im s)).length := by
  induction w with
  | nil => simp
  | cons s rest ih =>
      rw [List.length_cons, range_cons_succ]
      rw [List.filter_cons, List.getD_cons_zero]
      by_cases him : F4.im s
      · rw [if_pos (by simpa using him)]
        simp only [him, List.filter_cons]
        simp only [List.length_cons]
        rw [length_filter_map_add]
        simp only [List.getD_cons_succ]
        rw [ih]
        first | done | rfl
      · rw [if_neg (by intro h; exact him (of_decide_eq_true h))]
        simp only [him, List.filter_cons]
        rw [length_filter_map_add]
        simp only [List.getD_cons_succ]
        rw [ih]
        first | done | rfl

/-- 正确机器的接受路径必读每个激活位：反证翻转未读位的实部 → 编码失效 → 语言改变 → 矛盾。 -/
lemma accepting_path_reads_all_activated (M : CBTM) (w : List F4)
    (hw : ∃ inst, w = encodeSubsetSumF4Real inst ∧ inst.elements ≠ [] ∧ subsetSumHolds inst)
    (hcorrect : ∀ w', M.tapeAccepts w' ↔ subsetSumLanguageF4Real w')
    {π : ComputationPath} {cfg : CBTMConfig M w}
    (hπ : TapeReachablePath M w π cfg) (hacc : cfg.state ∈ M.acceptStates) :
    ∀ i, i < w.length → F4.im (w.getD i F4.zero) = true →
      ∃ t, t < π.length ∧ (CBTM.configAt M w π t).headPos = (i : ℤ) := by
  intro i hi him
  rcases hw with ⟨inst, hw', _hne, hholds⟩
  subst w
  by_contra hnot
  have hskip : ∀ t, t < π.length →
      (CBTM.configAt M (encodeSubsetSumF4Real inst) π t).headPos ≠ (i : ℤ) := by
    intro t ht hpos
    exact hnot ⟨t, ht, hpos⟩
  let w' : List F4 := flipReAt (encodeSubsetSumF4Real inst) i
  have hinit : ∀ j : ℤ, j ≠ (i : ℤ) →
      (initialConfig M (encodeSubsetSumF4Real inst)).tapeAt j = (initialConfig M w').tapeAt j := by
    intro j hj
    have hF4 : initialTapeOf (encodeSubsetSumF4Real inst) M.blankSym j =
        initialTapeOf w' M.blankSym j := by
      unfold initialTapeOf
      by_cases hj' : 0 ≤ j ∧ j.toNat < (encodeSubsetSumF4Real inst).length
      · rw [dif_pos hj']
        have hj'' : 0 ≤ j ∧ j.toNat < w'.length := by
          rcases hj' with ⟨h0, hlt⟩
          exact ⟨h0, by rw [flipReAt_length]; exact hlt⟩
        rw [dif_pos hj'']
        have hne : j.toNat ≠ i := by
          intro h
          exact hj (by
            cases j with
            | ofNat n => subst h; rfl
            | negSucc n => omega)
        rw [flipReAt_get_ne (encodeSubsetSumF4Real inst) i j.toNat hne hj'.2]
      · rw [dif_neg hj']
        rw [dif_neg (by
          intro h
          apply hj'
          exact ⟨h.1, by rw [← flipReAt_length]; exact h.2⟩)]
    simpa [CBTMConfig.tapeAt, initialConfig] using hF4
  have hacc'' : M.tapeAccepts w' := by
    exact tapeAccepts_insensitive_to_unread_update hπ hacc hinit hskip
  have hL' : subsetSumLanguageF4Real w' := (hcorrect w').1 hacc''
  exact flipReAt_activated_not_in_L inst i hi him hL'

/-- 激活步数 ≥ 虚部 true 格数（必读 + 写=读绑定：首个读格 i 的步读到的恰是 w[i]，im=true，必激活）。 -/
lemma activated_ge_imTrueCount_of_reads_all {M : CBTM} {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M w}
    (hreach : TapeReachablePath M w π cfg)
    (hreads : ∀ i, i < w.length → F4.im (w.getD i F4.zero) = true →
      ∃ t, t < π.length ∧ (CBTM.configAt M w π t).headPos = (i : ℤ)) :
    (activatedGenSetOnPath π).card ≥ imTrueCount w := by
  classical
  -- 激活位索引列表（i < w.length 且 im=true），按 range 排列（core 无 List.enum）
  let wf : List (ℕ × F4) := ((List.range w.length).filter
    (fun i => F4.im (w.getD i F4.zero) = true)).map (fun i => (i, w.getD i F4.zero))
  have hmain : ∀ p, p ∈ wf → p.1 < w.length ∧ p.2 = w.getD p.1 F4.zero ∧
      F4.im (w.getD p.1 F4.zero) = true := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, hif, hpi⟩
    rw [← hpi]
    exact ⟨List.mem_range.mp (List.mem_filter.mp hif).1, rfl,
      of_decide_eq_true (List.mem_filter.mp hif).2⟩
  let ts : List ℕ := wf.attach.map (fun ⟨p, hp⟩ => Nat.find
    (hreads p.1 (hmain p hp).1 (hmain p hp).2.2))
  have hlen : ts.length = imTrueCount w := by
    unfold ts wf imTrueCount
    rw [List.length_map, List.length_attach, List.length_map]
    exact length_filter_range_getD w
  -- 每个 t_i 是激活步（0-based t < π.length 且 readSym.im = true）
  have ht_active : ∀ t ∈ ts, t < π.length ∧
      F4.im ((π.getD t Inhabited.default).readSym) = true := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨⟨p, hp⟩, _hpe, rfl⟩
    let P : ℕ → Prop := fun t => t < π.length ∧ (CBTM.configAt M w π t).headPos = (p.1 : ℤ)
    let t₀ : ℕ := Nat.find (p := P) (hreads p.1 (hmain p hp).1 (hmain p hp).2.2)
    have hP : P t₀ := by
      exact Nat.find_spec _
    have htlt : t₀ < π.length := hP.1
    have hpos : (CBTM.configAt M w π t₀).headPos = (p.1 : ℤ) := hP.2
    constructor
    · exact htlt
    · have hfirst : ∀ t, t < t₀ → (CBTM.configAt M w π t).headPos ≠ (p.1 : ℤ) := by
        intro u hu hpos'
        exact (Nat.find_min (H := hreads p.1 (hmain p hp).1 (hmain p hp).2.2) (m := u) hu)
          (And.intro (by omega) hpos')
      have htape : (CBTM.configAt M w π (min t₀ π.length)).tapeAt (p.1 : ℤ) =
          (initialConfig M w).tapeAt (p.1 : ℤ) :=
        tapeReachable_tapeAt_eq_of_head_ne (i := (p.1 : ℤ)) (t₀ := t₀) hfirst
      have hm : min t₀ π.length = t₀ := by omega
      have hread : ((π.getD t₀ Inhabited.default).readSym) =
          (CBTM.configAt M w π t₀).tapeAt (p.1 : ℤ) := by
        have hread' := tapeReachable_readSym_at (M := M) (input := w) (h := hreach) (t := t₀) htlt
        rw [hpos] at hread'
        rw [getD_eq_get π t₀ Inhabited.default htlt]
        exact hread'
      have htape' : (CBTM.configAt M w π t₀).tapeAt (p.1 : ℤ) =
          w.getD p.1 F4.zero := by
        rw [hm] at htape
        rw [htape]
        have htapeInit : (initialConfig M w).tapeAt (p.1 : ℤ) = w.get ⟨p.1, (hmain p hp).1⟩ := by
          change (initialConfig M w).tape (p.1 : ℤ) = w.get ⟨p.1, (hmain p hp).1⟩
          have hget : initialTapeOf w M.blankSym (p.1 : ℤ) = w.get ⟨p.1, (hmain p hp).1⟩ := by
            unfold initialTapeOf
            have hpp : 0 ≤ (p.1 : ℤ) ∧ ((p.1 : ℤ).toNat) < w.length := ⟨by omega, (hmain p hp).1⟩
            rw [dif_pos hpp]
            simpa
          simpa [CBTMConfig.tapeAt, initialConfig] using hget
        rw [htapeInit]
        simpa using (getD_eq_get w p.1 F4.zero (hmain p hp).1).symm
      rw [hread, htape']
      simpa [F4.im] using (hmain p hp).2.2
  -- ts 无重复（t_p 两两不同：一步只读一格）
  have hwfNodup : wf.Nodup := by
    unfold wf
    exact List.Nodup.map (l := (List.range w.length).filter
        (fun i => F4.im (w.getD i F4.zero) = true)) (f := fun i => (i, w.getD i F4.zero))
      (by intro a b heq; exact congrArg Prod.fst heq)
      (List.Nodup.filter (fun i => F4.im (w.getD i F4.zero) = true) (by
        have hrange : (List.range w.length).Nodup := by
          induction w.length with
          | zero => simp
          | succ n ih =>
              rw [List.range_succ, List.nodup_append]
              constructor
              · exact ih
              constructor
              · exact (List.nodup_singleton n)
              · intro a ha b hb
                rw [List.mem_singleton] at hb
                have : a < n := List.mem_range.mp ha
                omega
        exact hrange))
  have hinj : Function.Injective (fun x : {x : ℕ × F4 // x ∈ wf} =>
      (Nat.find (hreads x.1.1 (hmain x.1 x.2).1 (hmain x.1 x.2).2.2) : ℕ)) := by
    intro a₁ a₂ heq
    apply Subtype.ext
    have hposP : (CBTM.configAt M w π (Nat.find _)).headPos = (a₁.1.1 : ℤ) :=
      (Nat.find_spec (hreads a₁.1.1 (hmain a₁.1 a₁.2).1 (hmain a₁.1 a₁.2).2.2)).2
    have hposQ : (CBTM.configAt M w π
        (Nat.find (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2))).headPos =
        (a₂.1.1 : ℤ) :=
      (Nat.find_spec (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2)).2
    have hp1 : a₁.1.1 = a₂.1.1 := by
      have hhp : (CBTM.configAt M w π
          (Nat.find (hreads a₁.1.1 (hmain a₁.1 a₁.2).1 (hmain a₁.1 a₁.2).2.2))).headPos =
        (CBTM.configAt M w π
          (Nat.find (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2))).headPos :=
        congrArg (fun t => (CBTM.configAt M w π t).headPos) heq
      apply Int.ofNat_inj.mp
      rw [← hposP, ← hposQ]
      exact hhp
    apply Prod.ext
    · exact hp1
    · have hp2 := (hmain a₁.1 a₁.2).2.1
      have hq2 := (hmain a₂.1 a₂.2).2.1
      rw [hp2, hq2, hp1]
  have hnodup : ts.Nodup := by
    unfold ts
    exact List.Nodup.map (l := wf.attach)
      (f := fun ⟨p, hp⟩ => (Nat.find (hreads p.1 (hmain p hp).1 (hmain p hp).2.2) : ℕ))
      hinj ((List.nodup_attach).2 hwfNodup)
  -- 每个激活步 t（0-based）→ 1-based t+1 ∈ 激活索引列表
  have hto : ∀ t ∈ ts, t + 1 ∈ activatedGenIndicesOnPath π := by
    intro t ht
    rcases ht_active t ht with ⟨htlt, him⟩
    rw [activatedGenIndicesOnPath]
    simpa [Nat.add_comm] using (mem_activatedGenIndicesOnPathAux π 1 t htlt).2 him
  have hcard_ts : ts.length ≤ (activatedGenSetOnPath π).card := by
    have hnd : (ts.map (fun t => t + 1)).Nodup := by
      rw [List.nodup_map_iff_inj_on (l := ts) (f := fun t => t + 1)]
      · intro a _ha b _hb heq
        omega
      · exact hnodup
    have htof : (ts.map (fun t => t + 1)).toFinset ⊆ (activatedGenIndicesOnPath π).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
      exact hto t ht
    have hcardle : (ts.map (fun t => t + 1)).toFinset.card ≤
        (activatedGenIndicesOnPath π).toFinset.card :=
      Finset.card_le_card htof
    have hcard1 : (ts.map (fun t => t + 1)).toFinset.card =
        (ts.map (fun t => t + 1)).length := by
      rw [List.toFinset_card_of_nodup hnd]
    rw [activatedGenSetOnPath]
    rw [hcard1, List.length_map] at hcardle
    exact hcardle
  rw [← hlen]
  exact hcard_ts

/-- kappa_M 下界（磁带语义）：正确机器的 κ ≥ 虚部 true 符号数。 -/
lemma kappa_M_ge_imTrueCount (M : CBTM) (w : List F4)
    (hw : ∃ inst, w = encodeSubsetSumF4Real inst ∧ inst.elements ≠ [] ∧ subsetSumHolds inst)
    (hcorrect : ∀ w', M.tapeAccepts w' ↔ subsetSumLanguageF4Real w') :
    kappa_M M w ≥ imTrueCount w := by
  by_cases h_exists : ∃ π, ∃ cfg : CBTMConfig M w,
      TapeReachablePath M w π cfg ∧ cfg.state ∈ M.acceptStates
  · rcases kappa_M_spec M w h_exists with ⟨π, cfg, hr, ha, hcard⟩
    rw [← hcard]
    exact activated_ge_imTrueCount_of_reads_all hr
      (accepting_path_reads_all_activated M w hw hcorrect hr ha)
  · rcases hw with ⟨inst', henc', hne', hholds⟩
    have hacc : M.tapeAccepts w := (hcorrect w).2 (by rw [henc']; exact ⟨inst', rfl, hne', hholds⟩)
    exfalso
    rcases hacc with ⟨π, cfg, hr, ha⟩
    exact h_exists ⟨π, cfg, hr, ha⟩

-- ============================================================================
-- 点态下界（论文 thm:subset-sum-lower 的核心）：对任意正确验证器 M 与任意
-- YES 实例 inst，kappa_M M (encode inst) ≥ 元素个数。
-- ============================================================================

theorem subsetSum_kappa_lower_bound (M : CBTM) (inst : SubsetSumInstance)
    (hM : ∀ w, M.tapeAccepts w ↔ subsetSumLanguageF4Real w)
    (hYES : subsetSumLanguageF4Real (encodeSubsetSumF4Real inst)) :
    kappa_M M (encodeSubsetSumF4Real inst) ≥ inst.elements.length := by
  rcases hYES with ⟨inst', henc, hne, hholds⟩
  have hge := kappa_M_ge_imTrueCount M (encodeSubsetSumF4Real inst)
    ⟨inst', by rw [henc], hne, hholds⟩ hM
  rw [imTrueCount_encodeSubsetSumF4Real inst] at hge
  exact hge

-- ============================================================================
-- 子集和 ∉ P（F4 版本）：restricted 验证器 κ 恒 0，但点态下界 κ ≥ 1。
-- ============================================================================

theorem subsetSum_not_in_P_F :
    ¬ (∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTime M ∧
      (∀ w : List F4, M.tapeAccepts w ↔ subsetSumLanguageF4Real w)) := by
  intro h
  rcases h with ⟨M, hrest, _hpoly, hcorrect⟩
  let inst : SubsetSumInstance := { elements := [1], target := 1 }
  have hYES : subsetSumLanguageF4Real (encodeSubsetSumF4Real inst) := by
    refine ⟨inst, rfl, ?_⟩
    exact ⟨by simp [inst], ⟨[true], by simp [inst], by simp [inst, selectedSum]⟩⟩
  have h_lower : kappa_M M (encodeSubsetSumF4Real inst) ≥ 1 := by
    have hk := subsetSum_kappa_lower_bound M inst (fun w => hcorrect w) hYES
    simpa [inst] using hk
  have h_zero : kappa_M M (encodeSubsetSumF4Real inst) = 0 :=
    kappa_zero_of_restricted_total M (encodeSubsetSumF4Real inst) hrest
  rw [h_zero] at h_lower
  omega

-- 子集和 ∉ P_F
theorem subsetSum_not_in_P_F' : ¬ IsP_F subsetSumLanguageF4Real :=
  subsetSum_not_in_P_F

-- 注：subsetSum_in_NP_F 由 PvsNP.SubsetSumInNP 定理化（公理 A1 + 同构桥定理）；
-- P_F_neq_NP_F 相应组装于 PvsNP.FinalProof。

end PvsNP
