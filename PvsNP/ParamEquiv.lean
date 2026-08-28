/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM
import PvsNP.ClassicalFramework
import PvsNP.ClassicalComplexity

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
# PvsNP.ParamEquiv —— 参数化等价定理（论文 models.C.0.6.tex 定理 thm:equivalence）

论文声明：CBTM|₀ ≡ₚₒₗy DTM（P_cb = P）、CBTM ≡ₚₒₗy NTM（NP_cb = NP）——
经典计算模型与 CBTM 在**语言识别能力**上的外延等价（CBTM 不引入超计算能力）。

本文件形式化其语言层面的严格形态：

1. **经典 DTM 磁带语义**（ClassicDTM，Basic.lean）：`DTMTapeReachablePath`、
   `ClassicDTM.acceptsTape`。
2. **经典复杂度类**：
   - `IsP_classic K := ∃ D : ClassicDTM, ∀ x, D.acceptsTape x ↔ K x`；
   - `IsNP_classic K := ∃ A : NTM2, NTM2.Canonical A ∧ ∀ x, A.acceptsTape x ↔ K x`
     （用户裁定：ClassicNTM := NTM2，不重建经典 NTM 模型）。
3. **CBTM|₀ 类**（论文 P_cb 的语言形态）：`IsP_cb0 K := ∃ N, IsCBTM0 N ∧
   投影接受语义（∃ w, realProject w = x ∧ N.tapeAccepts w）↔ K x`。
4. **P 方向等价定理**：`P_cb0_eq_P_classic`（CBTM|₀ 与经典 DTM 外延等价）。
   证明骨架：
   （a）重放引理：受限机器接受 w ⟺ 接受 embed(Re w)（未读位置不敏感；
   受限路径读的符号虚部全 false）；
   （b）`ClassicDTM.toCBTM` 与 `CBTM.toClassicDTM` 的直接路径对应（接受保持）。
5. **NP 方向的框架形态**：语言级双向等价不可证——每台 NTM2 的 vbAt 模式
   （分叉位置集合）固定，而 FULL CBTM 的接受串可有任意虚部模式（一台机器
   无法覆盖所有模式）；且 FULL CBTM 对非复合串的行为无约束。机器级等价
   （规范 NTM2 ↔ toCBTM A，路径逐步对应）已在 A2Bridge 证明
   （`StructIso_preserves_accepts`）——论文「CBTM ≡ NTM」的框架形态即此桥。
-/

namespace PvsNP

open CBTM
open IVM

-- ======================================================================
-- 1. ClassicDTM 磁带语义
-- ======================================================================

/-- 经典 DTM 转移步。 -/
structure DTMStep where
  fromState : ℕ
  readSym : Bool
  pos : ℤ
  result : ClassicDTMTransitionResult

abbrev DTMPath := List DTMStep

/-- 经典 DTM 格局：状态、Bool 磁带、磁头位置。 -/
structure DTMCfg (M : ClassicDTM) (input : List Bool) where
  state : ℕ
  tape : ℤ → Bool
  headPos : ℤ

/-- 经典 DTM 初始磁带：输入区 [0, n)，空白 = blankSym。 -/
def DTMInitialTape (M : ClassicDTM) (input : List Bool) : ℤ → Bool :=
  fun i => if h : 0 ≤ i ∧ i.toNat < input.length then
      input.get ⟨i.toNat, h.2⟩
    else M.blankSym

/-- 经典 DTM 初始配置。 -/
def DTMInitialCfg (M : ClassicDTM) (input : List Bool) : DTMCfg M input :=
  { state := M.startState, tape := DTMInitialTape M input, headPos := 0 }

/-- 一步格局：写 writeSym 到带头位置，移动带头，更新状态。 -/
def DTMStepCfg {M : ClassicDTM} {input : List Bool} (cfg : DTMCfg M input)
    (r : ClassicDTMTransitionResult) : DTMCfg M input :=
  { state := r.nextState,
    tape := fun i => if i = cfg.headPos then r.writeSym else cfg.tape i,
    headPos := cfg.headPos + r.move.toInt }

/-- 带头位置的磁带符号。 -/
def DTMCfg.tapeAt {M : ClassicDTM} {input : List Bool} (cfg : DTMCfg M input) (i : ℤ) : Bool :=
  cfg.tape i

/-- 经典 DTM 磁带语义的可达路径：每步读带头位置的格子，写 writeSym，移动 move。 -/
inductive DTMTapeReachablePath (M : ClassicDTM) (input : List Bool) :
    DTMPath → DTMCfg M input → Prop
  | nil : DTMTapeReachablePath M input [] (DTMInitialCfg M input)
  | cons : ∀ (π₀ : DTMPath) (step : DTMStep) (cfg : DTMCfg M input),
      DTMTapeReachablePath M input π₀ cfg →
      step.fromState = cfg.state →
      step.readSym = cfg.tapeAt cfg.headPos →
      step.result = M.transition (cfg.state, cfg.tapeAt cfg.headPos) →
      step.pos = cfg.headPos →
      DTMTapeReachablePath M input (π₀ ++ [step]) (DTMStepCfg cfg step.result)

/-- 经典 DTM 磁带语义的接受：存在一条磁带可达路径，末端状态在接受态。 -/
def ClassicDTM.acceptsTape (M : ClassicDTM) (x : List Bool) : Prop :=
  ∃ π : DTMPath, ∃ cfg : DTMCfg M x,
    DTMTapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates

-- ======================================================================
-- 2. 经典复杂度类（语言等价版；ClassicNTM := NTM2，用户裁定）
-- ======================================================================

/-- 经典 P：存在经典 DTM 判定 Bool 语言（语言等价；时间保持为后续阶段）。 -/
def IsP_classic (K : BoolLanguage) : Prop :=
  ∃ D : ClassicDTM, ∀ x : List Bool, D.acceptsTape x ↔ K x

/-- 经典 NP：ClassicNTM := NTM2（用户裁定 —— 不重建经典 NTM 模型）。
    规范条款（Canonical）保留：与框架内 NTM2 的机器级等价（A2Bridge 桥）兼容。 -/
def IsNP_classic (K : BoolLanguage) : Prop :=
  ∃ A : NTM2, NTM2.Canonical A ∧ ∀ x : List Bool, A.acceptsTape x ↔ K x

-- ======================================================================
-- 3. CBTM|₀ 类（论文 P_cb 的语言形态：投影接受语义）
-- ======================================================================

/-- CBTM|₀ 判定的 Bool 语言：存在 IsCBTM0 机器，投影接受语义（∃ w 实部 = x 且接受）。
    「CBTM|₀ ≡ₚₒₗy DTM」的语言层形态：CBTM|₀ 与经典 DTM 判定同一 Bool 语言类。 -/
def IsP_cb0 (K : BoolLanguage) : Prop :=
  ∃ N : CBTM, IsCBTM0 N ∧
    ∀ x : List Bool, (∃ w : List F4, realProject w = x ∧ N.tapeAccepts w) ↔ K x

-- ======================================================================
-- 4. 受限机器的重放引理：接受 w ⟺ 接受 embed(Re w)（未读位置不敏感）
-- ======================================================================

/-- 受限机器路径的每步读符号在字母表内（转移非空 ⟹ 读符号 ∈ 字母表）。 -/
lemma restricted_step_read_in_alphabet (M : CBTM) (hrest : IsRestricted M) (w : List F4)
    (π : ComputationPath) (cfg : CBTMConfig M w) (hr : TapeReachablePath M w π cfg) :
    ∀ step ∈ π, step.readSym ∈ M.alphabet := by
  induction hr with
  | nil => simp
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      intro s hs
      simp at hs
      rcases hs with hs | hs
      · exact ih s hs
      · subst s
        by_contra hnot
        have hempty : M.transition (cfg₀.state, step.readSym, cfg₀.headPos) = ∅ :=
          M.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hnot
        have hmem' : step.result ∈ M.transition (cfg₀.state, step.readSym, cfg₀.headPos) := by
          simpa [hfrom, hread] using htrans
        rw [hempty] at hmem'
        simpa using hmem'

/-- 受限机器路径的每步读符号虚部全 false。 -/
lemma restricted_step_read_im_false (M : CBTM) (hrest : IsRestricted M) (w : List F4)
    (π : ComputationPath) (cfg : CBTMConfig M w) (hr : TapeReachablePath M w π cfg) :
    ∀ step ∈ π, F4.im step.readSym = false := by
  intro step hstep
  exact hrest.h_alphabet_im_false step.readSym
    (restricted_step_read_in_alphabet M hrest w π cfg hr step hstep)

/-- 初始磁带对应：若 w 在位置 i 的初始值虚部 false，则 embed(Re w) 与 w 的初始值相同。 -/
lemma initial_tapeAt_embed_eq (M : CBTM) (w : List F4) (i : ℤ)
    (hw : ((initialConfig M w).tape i).2 = false) :
    (initialConfig M (embedBool (realProject w))).tape i = (initialConfig M w).tape i := by
  unfold initialConfig initialTapeOf embedBool realProject
  by_cases h : 0 ≤ i ∧ i.toNat < w.length
  · apply Prod.ext
    · simp [h]
    · have hwi : (w.get ⟨i.toNat, h.2⟩).2 = false := by
        simpa [initialConfig, initialTapeOf, h] using hw
      simp [h, ← hwi]
  · simp [h]

/-- 重放：受限机器在 w 上的可达路径，同一路径在 embed(Re w) 上同样可达
    （每步读符号虚部 false —— 已读位置在 w 与 embed(Re w) 相同；
    未读位置不影响路径合法性）。 -/
lemma restricted_path_replay_embed (M : CBTM) (hrest : IsRestricted M) (w : List F4) :
    ∀ (π : ComputationPath) (cfg : CBTMConfig M w),
      TapeReachablePath M w π cfg →
      ∃ cfg' : CBTMConfig M (embedBool (realProject w)),
        TapeReachablePath M (embedBool (realProject w)) π cfg' ∧
        cfg'.state = cfg.state ∧ cfg'.headPos = cfg.headPos ∧
        ∀ p : ℤ, cfg'.tape p = cfg.tape p ∨
          (cfg'.tape p = (initialConfig M (embedBool (realProject w))).tape p ∧
           cfg.tape p = (initialConfig M w).tape p) := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨initialConfig M (embedBool (realProject w)), TapeReachablePath.nil, rfl, rfl, ?_⟩
      intro p
      right
      constructor <;> rfl
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      rcases ih with ⟨cfg₀', hrc', hst', hhp', htape'⟩
      have hread_im : F4.im step.readSym = false :=
        restricted_step_read_im_false M hrest w (π₀ ++ [step]) (stepConfig cfg₀ step.result)
          (TapeReachablePath.cons π₀ step cfg₀ hrc hfrom hread htrans) step (by simp)
      have htapeAt_eq : cfg₀'.tapeAt cfg₀'.headPos = step.readSym := by
        rw [hhp']
        change cfg₀'.tape cfg₀.headPos = step.readSym
        have htapeAt₀ : cfg₀.tapeAt cfg₀.headPos = step.readSym := hread.symm
        cases htape' cfg₀.headPos with
        | inl h =>
            rw [h]
            change cfg₀.tape cfg₀.headPos = step.readSym
            exact htapeAt₀
        | inr hpair =>
            rcases hpair with ⟨hcfg', hcfg⟩
            have hinit_w : (initialConfig M w).tape cfg₀.headPos = step.readSym := by
              rw [← hcfg]
              exact htapeAt₀
            have him_w : ((initialConfig M w).tape cfg₀.headPos).2 = false := by
              rw [hinit_w]
              exact hread_im
            have hinit_eq := initial_tapeAt_embed_eq M w cfg₀.headPos him_w
            rw [hcfg']
            rw [hinit_eq]
            exact hinit_w
      let cfg' := stepConfig cfg₀' step.result
      refine ⟨cfg', TapeReachablePath.cons π₀ step cfg₀' hrc' ?_ ?_ ?_, ?_, ?_, ?_⟩
      · rw [hfrom]
        exact hst'.symm
      · rw [htapeAt_eq]
      · have htrans' : step.result ∈ M.transition (cfg₀'.state, cfg₀'.tapeAt cfg₀'.headPos, cfg₀'.headPos) := by
          rw [htapeAt_eq]
          rw [hst', hhp']
          simpa [hfrom, hread] using htrans
        exact htrans'
      · rfl
      · dsimp [cfg', stepConfig]
        rw [hhp']
      · intro p
        dsimp [cfg', stepConfig]
        by_cases hp : p = cfg₀.headPos
        · subst p
          left
          simp [stepConfig, hhp']
        · cases htape' p with
          | inl h =>
              left
              simp [stepConfig, hp, hhp', h]
          | inr hpair =>
              right
              constructor
              · simp [stepConfig, hp, hhp', hpair.1]
              · simp [stepConfig, hp, hhp', hpair.2]

/-- 受限机器：接受 w ⟹ 接受 embed(Re w)（重放引理的接受形式；单向已够用）。 -/
lemma restricted_tapeAccepts_of_embed (M : CBTM) (hrest : IsRestricted M) (w : List F4) :
    M.tapeAccepts w → M.tapeAccepts (embedBool (realProject w)) := by
  intro ⟨π, cfg, hr, hacc⟩
  rcases restricted_path_replay_embed M hrest w π cfg hr with ⟨cfg', hr', hst', _hhp, _htape⟩
  refine ⟨π, cfg', hr', ?_⟩
  rwa [hst']

-- ======================================================================
-- 5. ClassicDTM ↔ CBTM0 的接受保持（直接构造）
-- ======================================================================

/-- 单元素集的两个 choose 相等（唯一性 + proof irrelevance）。 -/
lemma choose_eq_of_card_one {α : Type*} (s : Finset α) (h1 h2 : s.card = 1) :
    (card_eq_one_unique_mem s h1).choose = (card_eq_one_unique_mem s h2).choose := by
  exact (card_eq_one_unique_mem s h1).choose_spec.2 (card_eq_one_unique_mem s h2).choose
    (card_eq_one_unique_mem s h2).choose_spec.1

/-- DTM 配置 → toCBTM 配置：磁带逐格提升为 (b, false)。 -/
def dtmCfgToCBTM (M : ClassicDTM) {x : List Bool} (cfg : DTMCfg M x) :
    CBTMConfig (M.toCBTM) (embedBool x) :=
  { state := cfg.state, tape := fun i => boolToF4 (cfg.tape i), headPos := cfg.headPos }

/-- DTM 路径 → toCBTM 路径（逐步骤提升；接受保持）。 -/
lemma dtm_path_to_cbtm (M : ClassicDTM) :
    ∀ (x : List Bool) (π : DTMPath) (cfg : DTMCfg M x),
      DTMTapeReachablePath M x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig (M.toCBTM) (embedBool x),
        TapeReachablePath (M.toCBTM) (embedBool x) π' cfg' ∧
        cfg' = dtmCfgToCBTM M cfg := by
  intro x π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig (M.toCBTM) (embedBool x), TapeReachablePath.nil, ?_⟩
      unfold dtmCfgToCBTM DTMInitialCfg initialConfig DTMInitialTape embedBool
      congr
      · funext i
        by_cases h : 0 ≤ i ∧ i.toNat < x.length
        · simp [initialTapeOf, h, embedBool, List.getElem_map, boolToF4]
        · rw [ClassicDTM.toCBTM]
          simp [initialTapeOf, h, boolToF4]
  | cons π₀ step cfg₀ hrc hfrom hread htrans hpos ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      let step' : TransitionStep := {
        fromState := step.fromState,
        readSym := boolToF4 step.readSym,
        result := CBTMTransResult.mk step.result.nextState (boolToF4 step.result.writeSym) step.result.move }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_⟩
      · dsimp [step']
        rw [hcfg']
        dsimp [dtmCfgToCBTM]
        exact hfrom
      · dsimp [step']
        rw [hcfg']
        change boolToF4 step.readSym = boolToF4 (cfg₀.tapeAt cfg₀.headPos)
        rw [hread]
      · dsimp [step']
        rw [hcfg']
        change CBTMTransResult.mk step.result.nextState (boolToF4 step.result.writeSym) step.result.move ∈
          (M.toCBTM).transition (cfg₀.state, boolToF4 (cfg₀.tapeAt cfg₀.headPos), cfg₀.headPos)
        rw [← hread] at htrans ⊢
        cases h : step.readSym <;>
          (rw [h] at htrans;
           simp [ClassicDTM.toCBTM, ClassicDTM.toCBTMTrans, h, ← htrans, boolToF4, f4ToBool, F4.zero, F4.one])
      · rw [hcfg']
        dsimp [dtmCfgToCBTM, step', DTMStepCfg, stepConfig]
        congr
        · funext i
          by_cases hi : i = cfg₀.headPos
          · simp [hi]
          · simp [hi]

/-- DTM 接受 ⟹ toCBTM 接受（embed 输入）。 -/
lemma dtm_accepts_to_cbtm (M : ClassicDTM) (x : List Bool) :
    M.acceptsTape x → (M.toCBTM).tapeAccepts (embedBool x) := by
  intro ⟨π, cfg, hr, hacc⟩
  rcases dtm_path_to_cbtm M x π cfg hr with ⟨π', cfg', hrc', hcfg'⟩
  refine ⟨π', cfg', hrc', ?_⟩
  rw [hcfg']
  dsimp [dtmCfgToCBTM]
  exact hacc

/-- CBTM0 配置 → toClassicDTM 配置：磁带逐格投影实部。 -/
def cbtm0CfgToDTM (N : CBTM) (h0 : IsCBTM0 N) {x : List Bool}
    (cfg : CBTMConfig N (embedBool x)) : DTMCfg (N.toClassicDTM h0) x :=
  { state := cfg.state, tape := fun i => (cfg.tape i).1, headPos := cfg.headPos }

/-- CBTM0 路径（embed 输入）→ toClassicDTM 路径（接受保持）。
    关键：CBTM0 读的符号 ∈ {zero, one}（虚部 false），实部投影即 Bool 符号。 -/
lemma cbtm0_path_to_dtm (N : CBTM) (h0 : IsCBTM0 N) :
    ∀ (x : List Bool) (π : ComputationPath) (cfg : CBTMConfig N (embedBool x)),
      TapeReachablePath N (embedBool x) π cfg →
      ∃ π' : DTMPath, ∃ cfg' : DTMCfg (N.toClassicDTM h0) x,
        DTMTapeReachablePath (N.toClassicDTM h0) x π' cfg' ∧
        cfg' = cbtm0CfgToDTM N h0 cfg := by
  intro x π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], DTMInitialCfg (N.toClassicDTM h0) x, DTMTapeReachablePath.nil, ?_⟩
      unfold cbtm0CfgToDTM DTMInitialCfg initialConfig DTMInitialTape embedBool
      congr
      · funext i
        by_cases h : 0 ≤ i ∧ i.toNat < x.length
        · simp [initialTapeOf, h, embedBool, List.getElem_map, boolToF4]
        · rw [CBTM.toClassicDTM]
          simp [initialTapeOf, h, boolToF4]
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      have hmem : step.readSym ∈ N.alphabet := by
        by_contra hnot
        have hempty : N.transition (cfg₀.state, step.readSym, cfg₀.headPos) = ∅ :=
          N.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hnot
        have hmem' : step.result ∈ N.transition (cfg₀.state, step.readSym, cfg₀.headPos) := by
          simpa [hfrom, ← hread] using htrans
        rw [hempty] at hmem'
        simpa using hmem'
      have him : F4.im step.readSym = false := by
        rw [h0.alphabet_eq] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hz | ho
        · rw [hz]
          rfl
        · rw [ho]
          rfl
      let step' : DTMStep := {
        fromState := step.fromState,
        readSym := step.readSym.1,
        pos := cfg₀.headPos,
        result := ClassicDTMTransitionResult.mk step.result.nextState
          step.result.writeSym.1 step.result.moveDir }
      refine ⟨π' ++ [step'], DTMStepCfg cfg' step'.result,
        DTMTapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_ ?_, ?_⟩
      · dsimp [step']
        rw [hfrom]
        rw [hcfg']
        rfl
      · dsimp [step']
        rw [hcfg']
        dsimp [cbtm0CfgToDTM]
        change step.readSym.1 = (cfg₀.tapeAt cfg₀.headPos).1
        rw [hread]
      · -- 转移：toClassicDTM 转移 = 单元素 choose = step.result
        dsimp [step']
        rw [hcfg']
        have hmem0 : step.result ∈ N.transition (cfg₀.state, step.readSym, cfg₀.headPos) := by
          simpa [hfrom, ← hread] using htrans
        have hcard : (N.transition (cfg₀.state, step.readSym, cfg₀.headPos)).card = 1 :=
          h0.card_one cfg₀.state step.readSym cfg₀.headPos hmem
        have hpos0 : N.transition (cfg₀.state, step.readSym, 0) =
            N.transition (cfg₀.state, step.readSym, cfg₀.headPos) :=
          h0.pos_indep cfg₀.state step.readSym 0 cfg₀.headPos hmem
        have hres : step.result =
            (card_eq_one_unique_mem (N.transition (cfg₀.state, step.readSym, cfg₀.headPos)) hcard).choose :=
          (card_eq_one_unique_mem (N.transition (cfg₀.state, step.readSym, cfg₀.headPos)) hcard).choose_spec.2
            step.result hmem0
        change ClassicDTMTransitionResult.mk step.result.nextState step.result.writeSym.1 step.result.moveDir =
          (N.toClassicDTM h0).transition (cfg₀.state, (cfg₀.tapeAt cfg₀.headPos).1)
        rw [← hread]
        change ClassicDTMTransitionResult.mk step.result.nextState step.result.writeSym.1 step.result.moveDir =
          (N.toClassicDTM h0).transition (cfg₀.state, step.readSym.1)
        unfold CBTM.toClassicDTM
        change ClassicDTMTransitionResult.mk step.result.nextState step.result.writeSym.1 step.result.moveDir =
          ClassicDTMTransitionResult.mk
            (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym.1, 0))
              (h0.card_one cfg₀.state (boolToF4 step.readSym.1) 0
                (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym.1))).choose.nextState
            (f4ToBool (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym.1, 0))
              (h0.card_one cfg₀.state (boolToF4 step.readSym.1) 0
                (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym.1))).choose.writeSym)
            (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym.1, 0))
              (h0.card_one cfg₀.state (boolToF4 step.readSym.1) 0
                (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym.1))).choose.moveDir
        have hb2 : boolToF4 step.readSym.1 = step.readSym := by
          rw [← boolToF4_f4ToBool_of_im_false step.readSym him]
          rfl
        have hres2 : step.result =
            (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym.1, 0))
              (h0.card_one cfg₀.state (boolToF4 step.readSym.1) 0
                (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym.1))).choose := by
          -- choose 唯一性：step.result 是成员且集单元素
          apply (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym.1, 0))
            (h0.card_one cfg₀.state (boolToF4 step.readSym.1) 0
              (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym.1))).choose_spec.2
          rw [hb2]
          rw [hpos0]
          exact hmem0
        simp [← hres2, f4ToBool]
      · rw [hcfg']
        dsimp [cbtm0CfgToDTM, step', DTMStepCfg, stepConfig]

/-- CBTM0 接受（embed 输入）⟹ toClassicDTM 接受。 -/
lemma cbtm0_accepts_to_dtm (N : CBTM) (h0 : IsCBTM0 N) (x : List Bool) :
    N.tapeAccepts (embedBool x) → (N.toClassicDTM h0).acceptsTape x := by
  intro ⟨π, cfg, hr, hacc⟩
  rcases cbtm0_path_to_dtm N h0 x π cfg hr with ⟨π', cfg', hrc', hcfg'⟩
  refine ⟨π', cfg', hrc', ?_⟩
  rw [hcfg']
  dsimp [cbtm0CfgToDTM]
  exact hacc

/-- M.toCBTM 是 CBTM0。 -/
lemma toCBTM_isCBTM0 (M : ClassicDTM) : IsCBTM0 (M.toCBTM) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro q s i hs
    have hcases : s = F4.zero ∨ s = F4.one := by
      simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
    rcases hcases with rfl | rfl <;> simp [ClassicDTM.toCBTM]
  · intro q s i j hs
    rfl

/-- 转移相等：(M.toCBTM.toClassicDTM) 的转移 = M 的转移（choose 唯一成员 + 提升恒等）。 -/
lemma toClassicDTM_of_toCBTM_trans (M : ClassicDTM) (q : ℕ) (b : Bool) :
    (M.toCBTM.toClassicDTM (toCBTM_isCBTM0 M)).transition (q, b) = M.transition (q, b) := by
  have hcard : (M.toCBTM.transition (q, boolToF4 b, 0)).card = 1 :=
    (toCBTM_isCBTM0 M).card_one q (boolToF4 b) 0
      (boolToF4_mem_alphabet_of_isCBTM0 (toCBTM_isCBTM0 M) b)
  have hch : (card_eq_one_unique_mem (M.toCBTM.transition (q, boolToF4 b, 0)) hcard).choose =
      { nextState := (M.transition (q, b)).nextState,
        writeSym := boolToF4 (M.transition (q, b)).writeSym,
        moveDir := (M.transition (q, b)).move } := by
    exact ((card_eq_one_unique_mem (M.toCBTM.transition (q, boolToF4 b, 0)) hcard).choose_spec.2
      { nextState := (M.transition (q, b)).nextState,
        writeSym := boolToF4 (M.transition (q, b)).writeSym,
        moveDir := (M.transition (q, b)).move } (by
          cases b <;> simp [ClassicDTM.toCBTM, ClassicDTM.toCBTMTrans_zero, ClassicDTM.toCBTMTrans_one])).symm
  unfold CBTM.toClassicDTM
  dsimp [CBTM.toClassicDTMTrans]
  rw [choose_eq_of_card_one (M.toCBTM.transition (q, boolToF4 b, 0))
    ((toCBTM_isCBTM0 M).card_one q (boolToF4 b) 0 (boolToF4_mem_alphabet_of_isCBTM0 (toCBTM_isCBTM0 M) b)) hcard]
  rw [hch]
  cases b <;> simp [f4ToBool, boolToF4]

/-- 转移相同的两台 DTM：路径重放（同一路径在 M2 上可达，配置逐字段保持）。 -/
lemma dtm_replay_of_trans_eq {M1 M2 : ClassicDTM}
    (hstart : M1.startState = M2.startState)
    (hblank : M1.blankSym = M2.blankSym)
    (h : ∀ q b, M1.transition (q, b) = M2.transition (q, b)) :
    ∀ (x : List Bool) (π : DTMPath) (cfg : DTMCfg M1 x),
      DTMTapeReachablePath M1 x π cfg →
      ∃ cfg' : DTMCfg M2 x,
        DTMTapeReachablePath M2 x π cfg' ∧ cfg'.state = cfg.state ∧
        cfg'.headPos = cfg.headPos ∧ ∀ i, cfg'.tape i = cfg.tape i := by
  intro x π cfg hr
  induction hr with
  | nil =>
      refine ⟨DTMInitialCfg M2 x, DTMTapeReachablePath.nil, ?_, rfl, ?_⟩
      · dsimp [DTMInitialCfg]
        exact hstart.symm
      · intro i
        dsimp [DTMInitialCfg, DTMInitialTape]
        by_cases h : 0 ≤ i ∧ i.toNat < x.length
        · simp [h]
        · simp [h, hblank]
  | cons π₀ step cfg₀ hrc hfrom hread htrans hpos ih =>
      rcases ih with ⟨cfg₀', hrc', hst', hhp', htape'⟩
      have hta : cfg₀'.tapeAt cfg₀.headPos = cfg₀.tapeAt cfg₀.headPos := by
        change cfg₀'.tape cfg₀.headPos = cfg₀.tape cfg₀.headPos
        exact htape' cfg₀.headPos
      refine ⟨DTMStepCfg cfg₀' step.result,
        DTMTapeReachablePath.cons π₀ step cfg₀' hrc' ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
      · rw [hfrom]
        exact hst'.symm
      · rw [hhp', hta]
        exact hread
      · rw [hst']
        rw [hhp']
        rw [hta]
        exact htrans.trans (h (cfg₀.state) (cfg₀.tapeAt cfg₀.headPos))
      · rw [hhp']
        exact hpos
      · dsimp [DTMStepCfg]
      · dsimp [DTMStepCfg]
        rw [hhp']
      · intro i
        dsimp [DTMStepCfg]
        rw [hhp']
        by_cases hi : i = cfg₀.headPos
        · subst i
          simp [hhp']
        · rw [htape' i]

/-- 转移相同、起始状态与接受状态集相同的两台 DTM：接受保持。 -/
lemma dtm_accepts_of_trans_eq {M1 M2 : ClassicDTM}
    (hstart : M1.startState = M2.startState)
    (hblank : M1.blankSym = M2.blankSym)
    (haccs : M1.acceptStates = M2.acceptStates)
    (h : ∀ q b, M1.transition (q, b) = M2.transition (q, b)) (x : List Bool) :
    M1.acceptsTape x → M2.acceptsTape x := by
  intro ⟨π, cfg, hr, hacc⟩
  rcases dtm_replay_of_trans_eq hstart hblank h x π cfg hr with ⟨cfg', hr', hst', _hhp, _htape⟩
  refine ⟨π, cfg', hr', ?_⟩
  rw [hst']
  rw [← haccs]
  exact hacc

/-- toCBTM 接受（embed 输入）⟹ DTM 接受（反向：toCBTM 是 CBTM0）。 -/
lemma cbtm_accepts_embed_to_dtm (M : ClassicDTM) (x : List Bool) :
    (M.toCBTM).tapeAccepts (embedBool x) → M.acceptsTape x := by
  intro h
  have h1 := cbtm0_accepts_to_dtm (M.toCBTM) (toCBTM_isCBTM0 M) x h
  exact @dtm_accepts_of_trans_eq (M.toCBTM.toClassicDTM (toCBTM_isCBTM0 M)) M
    (by simp [CBTM.toClassicDTM, ClassicDTM.toCBTM])
    (by simp [CBTM.toClassicDTM, ClassicDTM.toCBTM, boolToF4])
    (by simp [CBTM.toClassicDTM, ClassicDTM.toCBTM])
    (fun q b => toClassicDTM_of_toCBTM_trans M q b) x h1

-- ======================================================================
-- 6. 参数化等价定理（P 方向）：IsP_cb0 = IsP_classic
-- ======================================================================

/-- DTM 配置 → N 配置：磁带逐格提升为 boolToF4（与 dtmCfgToCBTM 同构，目标为 N）。 -/
def dtmCfgToCBTM0 (N : CBTM) (h0 : IsCBTM0 N) {x : List Bool}
    (cfg : DTMCfg (N.toClassicDTM h0) x) : CBTMConfig N (embedBool x) :=
  { state := cfg.state, tape := fun i => boolToF4 (cfg.tape i), headPos := cfg.headPos }

/-- DTM 路径（toClassicDTM）→ N 路径（embed 输入；接受保持的反向方向）。 -/
lemma dtm_path_to_cbtm0 (N : CBTM) (h0 : IsCBTM0 N) :
    ∀ (x : List Bool) (π : DTMPath) (cfg : DTMCfg (N.toClassicDTM h0) x),
      DTMTapeReachablePath (N.toClassicDTM h0) x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig N (embedBool x),
        TapeReachablePath N (embedBool x) π' cfg' ∧ cfg' = dtmCfgToCBTM0 N h0 cfg := by
  intro x π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig N (embedBool x), TapeReachablePath.nil, ?_⟩
      unfold dtmCfgToCBTM0 DTMInitialCfg initialConfig DTMInitialTape embedBool
      congr
      · funext i
        by_cases h : 0 ≤ i ∧ i.toNat < x.length
        · simp [initialTapeOf, h, embedBool, List.getElem_map, boolToF4]
        · rw [CBTM.toClassicDTM]
          simp [initialTapeOf, h]
          -- 空白区：N.blankSym 虚部 false（alphabet = {zero, one}）
          have hbim : F4.im N.blankSym = false := by
            have hb : N.blankSym ∈ N.alphabet := N.h_blank_in_alphabet
            rw [h0.alphabet_eq] at hb
            simp at hb
            rcases hb with hb1 | hb2
            · rw [hb1]
              rfl
            · rw [hb2]
              rfl
          rw [← boolToF4_f4ToBool_of_im_false N.blankSym hbim]
          rfl
  | cons π₀ step cfg₀ hrc hfrom hread htrans hpos ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      let step' : TransitionStep := {
        fromState := step.fromState,
        readSym := boolToF4 step.readSym,
        result := CBTMTransResult.mk step.result.nextState (boolToF4 step.result.writeSym) step.result.move }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_⟩
      · dsimp [step']
        rw [hfrom]
        rw [hcfg']
        dsimp [dtmCfgToCBTM0]
      · dsimp [step']
        rw [hcfg']
        change boolToF4 step.readSym = boolToF4 (cfg₀.tapeAt cfg₀.headPos)
        rw [hread]
      · -- 转移：htrans（toClassicDTM 转移的等式）+ choose 成员 + 位置无关
        dsimp [step']
        rw [hcfg']
        change CBTMTransResult.mk step.result.nextState (boolToF4 step.result.writeSym) step.result.move ∈
          N.transition (cfg₀.state, boolToF4 (cfg₀.tapeAt cfg₀.headPos), cfg₀.headPos)
        rw [← hread]
        -- 展开 toClassicDTM 转移（htrans）
        rw [← hread] at htrans
        unfold CBTM.toClassicDTM at htrans
        dsimp [CBTM.toClassicDTMTrans] at htrans
        let ch := (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym, 0))
          (h0.card_one cfg₀.state (boolToF4 step.readSym) 0
            (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym))).choose
        -- 写符号虚部 false（投影约束：读符号虚部 false）
        have hproj := N.h_projection_constraint cfg₀.state (boolToF4 step.readSym) 0
          (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym) (by simp [boolToF4])
        have hch_mem : ch ∈ N.transition (cfg₀.state, boolToF4 step.readSym, 0) := by
          dsimp [ch]
          exact (card_eq_one_unique_mem (N.transition (cfg₀.state, boolToF4 step.readSym, 0))
            (h0.card_one cfg₀.state (boolToF4 step.readSym) 0
              (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym))).choose_spec.1
        have hch_im : F4.im ch.writeSym = false := hproj.2 ch hch_mem
        have hpos1 : N.transition (cfg₀.state, boolToF4 step.readSym, 0) =
            N.transition (cfg₀.state, boolToF4 step.readSym, cfg₀.headPos) :=
          h0.pos_indep cfg₀.state (boolToF4 step.readSym) 0 cfg₀.headPos
            (boolToF4_mem_alphabet_of_isCBTM0 h0 step.readSym)
        -- 目标：mk step.result.nextState (boolToF4 step.result.writeSym) step.result.move ∈
        --   transition (q, boolToF4 step.readSym, headPos)
        -- 用 htrans（step.result = mk ch.nextState (f4ToBool ch.writeSym) ch.moveDir）替换：
        rw [htrans]
        -- 目标：mk ch.nextState (boolToF4 (f4ToBool ch.writeSym)) ch.moveDir ∈ transition (q, boolToF4 step.readSym, headPos)
        -- boolToF4 (f4ToBool ch.writeSym) = ch.writeSym（虚部 false）
        have hbw : boolToF4 (f4ToBool ch.writeSym) = ch.writeSym :=
          boolToF4_f4ToBool_of_im_false ch.writeSym hch_im
        rw [hbw]
        rw [← hpos1]
        -- 目标：ch ∈ transition (q, boolToF4 step.readSym, 0)
        exact hch_mem
      · rw [hcfg']
        dsimp [dtmCfgToCBTM0, step', DTMStepCfg, stepConfig]
        congr
        · funext i
          by_cases hi : i = cfg₀.headPos
          · simp [hi]
          · simp [hi]

/-- toClassicDTM 接受 ⟹ N 接受（embed 输入；反向接受保持）。 -/
lemma dtm_accepts_to_cbtm0 (N : CBTM) (h0 : IsCBTM0 N) (x : List Bool) :
    (N.toClassicDTM h0).acceptsTape x → N.tapeAccepts (embedBool x) := by
  intro ⟨π, cfg, hr, hacc⟩
  rcases dtm_path_to_cbtm0 N h0 x π cfg hr with ⟨π', cfg', hrc', hcfg'⟩
  refine ⟨π', cfg', hrc', ?_⟩
  rw [hcfg']
  dsimp [dtmCfgToCBTM0]
  exact hacc

/-- 经典 DTM 判定 ⟹ CBTM|₀ 判定（投影接受语义）。
    投影接受 x ⟺ ∃ w, Re w = x ∧ toCBTM 接受 w ⟺ toCBTM 接受 embed x（重放）
    ⟺ D 接受 x（接受保持）。 -/
theorem IsP_classic_subset_IsP_cb0 (K : BoolLanguage) (hP : IsP_classic K) : IsP_cb0 K := by
  rcases hP with ⟨D, hD⟩
  refine ⟨D.toCBTM, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · intro q s i hs
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl <;> simp [ClassicDTM.toCBTM]
    · intro q s i j hs
      simp [ClassicDTM.toCBTM]
  · intro x
    constructor
    · intro hproj
      rcases hproj with ⟨w, hw, hacc⟩
      have hrest : IsRestricted (D.toCBTM) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro s hs
          have hcases : s = F4.zero ∨ s = F4.one := by
            simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
          rcases hcases with rfl | rfl <;> simp [ClassicDTM.toCBTM]
        · intro s hs
          have hcases : s = F4.zero ∨ s = F4.one := by
            simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
          rcases hcases with rfl | rfl <;> simp [ClassicDTM.toCBTM]
        · intro q s i hs
          have hcases : s = F4.zero ∨ s = F4.one := by
            simpa [ClassicDTM.toCBTM, Finset.mem_insert, Finset.mem_singleton] using hs
          rcases hcases with rfl | rfl <;> simp [ClassicDTM.toCBTM]
        · cases D.blankSym <;> simp [ClassicDTM.toCBTM]
      have hembed : (D.toCBTM).tapeAccepts (embedBool (realProject w)) :=
        restricted_tapeAccepts_of_embed (D.toCBTM) hrest w hacc
      have hwx : embedBool (realProject w) = embedBool x := by rw [hw]
      rw [hwx] at hembed
      exact (hD x).1 (cbtm_accepts_embed_to_dtm D x hembed)
    · intro hx
      have haccD : D.acceptsTape x := (hD x).2 hx
      refine ⟨embedBool x, ?_, dtm_accepts_to_cbtm D x haccD⟩
      simp [embedBool, realProject]

/-- CBTM|₀ 判定 ⟹ 经典 DTM 判定。
    投影接受 x ⟺ N 接受 embed x（重放：受限 N 的接受串投影 = 嵌入接受）
    ⟺ (N.toClassicDTM) 接受 x（接受保持）。 -/
theorem IsP_cb0_subset_IsP_classic (K : BoolLanguage) (hP : IsP_cb0 K) : IsP_classic K := by
  rcases hP with ⟨N, h0, hN⟩
  refine ⟨N.toClassicDTM h0, ?_⟩
  intro x
  constructor
  · intro hacc
    -- D 接受 x → N 接受 embed x（反向接受保持）→ 投影接受（w = embed x）→ x ∈ K
    have hNacc : N.tapeAccepts (embedBool x) := dtm_accepts_to_cbtm0 N h0 x hacc
    exact (hN x).1 ⟨embedBool x, by simp [embedBool, realProject], hNacc⟩
  · intro hx
    have hproj := (hN x).2 hx
    rcases hproj with ⟨w, hw, hacc⟩
    have hrest : IsRestricted N := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [h0.alphabet_eq] at hs
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      · intro s hs
        rw [h0.alphabet_eq] at hs
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      · intro q s i hs
        exact h0.card_one q s i hs
      · rw [h0.alphabet_eq]
        exact N.h_blank_in_alphabet
    have hembed : N.tapeAccepts (embedBool (realProject w)) :=
      restricted_tapeAccepts_of_embed N hrest w hacc
    have hwx : embedBool (realProject w) = embedBool x := by rw [hw]
    rw [hwx] at hembed
    exact cbtm0_accepts_to_dtm N h0 x hembed

/-- 参数化等价定理（P 方向，论文 thm:equivalence(1) 的语言层形态）：
    P_cb0 = P_classic —— CBTM|₀ 与经典 DTM 的外延等价（CBTM 不引入超计算能力）。 -/
theorem P_cb0_eq_P_classic :
    {K : BoolLanguage | IsP_cb0 K} = {K : BoolLanguage | IsP_classic K} := by
  apply Set.ext
  intro K
  constructor
  · intro h
    exact IsP_cb0_subset_IsP_classic K h
  · intro h
    exact IsP_classic_subset_IsP_cb0 K h

end PvsNP
