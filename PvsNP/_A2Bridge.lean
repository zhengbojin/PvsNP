/- A2 桥(A2 公理消去的核心定理):位置模型 + 复合磁带 + Bool 输入版。
   输入 = Bool 串(与经典 P/NP 语言相同);虚部 = 机器内部 vb 带(由转移派生,
   只与输入的模式对应);格局 = (state, tape × vb, headPos) 与 CBTM 逐格相同。 -/
import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM

namespace PvsNP

open CBTM
open IVM

-- ======================================================================
-- 结构同构保持接受语言（A2 公理消去的核心定理）
-- ======================================================================

/-- 空白一致性：输入区之外 vb 带为常数（与 CBTM 常数空白符号对齐，含负位置）。 -/
def BlankVbConsistent (A : NTM2) (x : List Bool) : Prop :=
  (∀ i : ℤ, 0 ≤ i → x.length ≤ i.toNat → A.vbAt i = A.vbAt 0) ∧
  (∀ i : ℤ, i < 0 → A.vbAt i = A.vbAt 0)

/-- NTM2 输入（Bool 串）→ CBTM 输入（F4 复合串）：实部 = 输入，虚部 = vb 带。 -/
def ntm2InputToCBTM (A : NTM2) (x : List Bool) : List F4 :=
  x.mapIdx (fun i b => (b, A.vbAt i))

/-- NTM2 配置 → CBTM 配置：恒等（格局同型：state, tape × vb, headPos）。 -/
def ntm2CfgToCBTM (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    {x : List Bool} (cfg : NTM2Config A x) : CBTMConfig M (ntm2InputToCBTM A x) :=
  { state := cfg.state, tape := cfg.tape, headPos := cfg.headPos }

/-- 初始配置的对应（恒等；输入区虚部 = vb 带，空白区 = 常数 (blankSym, vbAt 0)）。 -/
lemma iso_initial_corresp (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List Bool) :
    ntm2CfgToCBTM A M iso (NTM2InitialConfig A x) = initialConfig M (ntm2InputToCBTM A x) := by
  unfold ntm2CfgToCBTM NTM2InitialConfig initialConfig NTM2InitialTape ntm2InputToCBTM
  rw [iso.h_start]
  congr
  · funext i
    dsimp
    by_cases h : 0 ≤ i ∧ i.toNat < x.length
    · unfold initialTapeOf
      simp [h, ntm2InputToCBTM, List.length_mapIdx]
    · unfold initialTapeOf
      simp [h, iso.h_blank, ntm2InputToCBTM, List.length_mapIdx]

/-- 可达路径上磁带虚部恒 = vb 带（格局复合语义：虚部是机器内部信息，由转移关系派生）。
    输入区由初始带定义，空白区为常数（空白一致性）。 -/
lemma ntm2Path_tape_im_vb (A : NTM2) (x : List Bool) (hblank : BlankVbConsistent A x) :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∀ i, (cfg.tape i).2 = A.vbAt i := by
  intro π cfg hr
  induction hr with
  | nil =>
      intro i
      unfold NTM2InitialConfig NTM2InitialTape
      by_cases h : 0 ≤ i ∧ i.toNat < x.length
      · simp [h]
      · simp [h]
        by_cases h0 : 0 ≤ i
        · have hlt : x.length ≤ i.toNat := by
            have : ¬ i.toNat < x.length := by
              intro h2
              exact h ⟨h0, h2⟩
            exact Nat.le_of_not_gt this
          exact (hblank.1 i h0 hlt).symm
        · have hneg : i < 0 := lt_of_not_ge h0
          exact (hblank.2 i hneg).symm
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro i
      unfold NTM2StepConfig
      by_cases h : i = cfg₀.headPos
      · simp [h]
        exact ih cfg₀.headPos
      · simp [h]
        exact ih i

/-- 单步转移对应（NTM2 → CBTM，位置 i 处虚部一致时）。 -/
lemma iso_step_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (q : ℕ) (b : Bool) (i : ℤ) (r : ℕ × Bool × Dir) :
    r ∈ A.transition (q, b, i) →
    CBTMTransResult.mk r.1 (r.2.1, A.vbAt i) r.2.2 ∈ M.transition (q, (b, A.vbAt i), i) := by
  intro hr
  rw [← iso.h_φ_id (b, A.vbAt i)]
  rw [iso.h_transition q (b, A.vbAt i) i rfl]
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- 单步配置步进的对应（恒等）。 -/
lemma iso_step_config (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    {x : List Bool} (cfg : NTM2Config A x) (r : ℕ × Bool × Dir) :
    ntm2CfgToCBTM A M iso (NTM2StepConfig cfg r) =
      stepConfig (ntm2CfgToCBTM A M iso cfg)
        (CBTMTransResult.mk r.1 (r.2.1, (cfg.tape cfg.headPos).2) r.2.2) := by
  dsimp [ntm2CfgToCBTM, NTM2StepConfig, stepConfig]
/-- 可达路径的对应（NTM2 → CBTM，路径与配置逐步保持；空白一致性时）。 -/
lemma iso_path_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List Bool)
    (hblank : BlankVbConsistent A x) :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig M (ntm2InputToCBTM A x),
        TapeReachablePath M (ntm2InputToCBTM A x) π' cfg' ∧
        cfg' = ntm2CfgToCBTM A M iso cfg := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig M (ntm2InputToCBTM A x), TapeReachablePath.nil, ?_⟩
      exact (iso_initial_corresp A M iso x).symm
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      have hvb : A.vbAt step.pos = (cfg₀.tape cfg₀.headPos).2 := by
        rw [hpos]
        exact (ntm2Path_tape_im_vb A x hblank π₀ cfg₀ hrc cfg₀.headPos).symm
      let step' : TransitionStep :=
        { fromState := step.fromState,
          readSym := (step.readSym, A.vbAt step.pos),
          result := CBTMTransResult.mk step.result.1 (step.result.2.1, A.vbAt step.pos) step.result.2.2 }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_⟩
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [← hfrom]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [hread]
        rw [hpos] at hvb ⊢
        rw [hvb]
        rfl
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        unfold CBTMConfig.tapeAt
        dsimp [step']
        rw [hpos] at hvb ⊢
        simpa [hvb] using iso_step_forward A M iso cfg₀.state (cfg₀.tape cfg₀.headPos).1
          cfg₀.headPos step.result htrans
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [hpos] at hvb ⊢
        rw [hvb]
        exact (iso_step_config A M iso cfg₀ step.result).symm

/-- 可达路径的对应（CBTM → NTM2；空白一致性时）。 -/
lemma iso_path_backward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List Bool)
    (hblank : BlankVbConsistent A x) :
    ∀ π, ∀ cfg : CBTMConfig M (ntm2InputToCBTM A x),
      TapeReachablePath M (ntm2InputToCBTM A x) π cfg →
      ∃ π' : NTM2ComputationPath, ∃ cfg' : NTM2Config A x,
        TapeReachablePathNTM2 A x π' cfg' ∧ cfg = ntm2CfgToCBTM A M iso cfg' := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], NTM2InitialConfig A x, TapeReachablePathNTM2.nil, ?_⟩
      exact (iso_initial_corresp A M iso x).symm
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      let s₀ : F4 := cfg₀.tapeAt cfg₀.headPos
      have him_s0 : F4.im s₀ = A.vbAt cfg₀.headPos := by
        dsimp [s₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        exact ntm2Path_tape_im_vb A x hblank π' cfg' hrc' cfg'.headPos
      have himage : step.result ∈ (A.transition (cfg₀.state, s₀.1, cfg₀.headPos)).image
          (fun r : ℕ × Bool × Dir =>
            CBTMTransResult.mk r.1 (r.2.1, A.vbAt cfg₀.headPos) r.2.2) := by
        rw [← iso.h_transition cfg₀.state s₀ cfg₀.headPos him_s0]
        rw [iso.h_φ_id s₀]
        exact htrans
      rcases Finset.mem_image.mp himage with ⟨r₀, hr₀, hres⟩
      let step₀ : NTM2TransitionStep :=
        { fromState := cfg₀.state, readSym := s₀.1, pos := cfg₀.headPos, result := r₀ }
      refine ⟨π' ++ [step₀], NTM2StepConfig cfg' r₀,
        TapeReachablePathNTM2.cons π' step₀ cfg' hrc' ?_ ?_ ?_ ?_, ?_⟩
      · dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      · dsimp [step₀, s₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        rfl
      · dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      · dsimp [step₀, s₀]
        have hr₀' : r₀ ∈ A.transition (cfg'.state, (cfg'.tape cfg'.headPos).1, cfg'.headPos) := by
          dsimp [s₀] at hr₀
          rw [hcfg'] at hr₀
          dsimp [ntm2CfgToCBTM] at hr₀
          exact hr₀
        exact hr₀'
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        rw [← hres]
        have hvb' : A.vbAt cfg₀.headPos = (cfg'.tape cfg'.headPos).2 := by
          rw [hcfg']
          dsimp [ntm2CfgToCBTM]
          dsimp [s₀] at him_s0
          rw [hcfg'] at him_s0
          dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt] at him_s0
          exact him_s0.symm
        rw [hvb']
        exact (iso_step_config A M iso cfg' r₀).symm

/-- 结构同构保持接受语言（NTM2 磁带语义 ↔ CBTM 磁带语义；空白一致性时）。
    输入 = Bool 串，CBTM 输入 = 复合串（实部 + vb 带）。消去同构桥公理的关键定理。 -/
theorem StructIso_preserves_accepts (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) :
    ∀ x : List Bool, (BlankVbConsistent A x → (A.acceptsTape x ↔ M.tapeAccepts (ntm2InputToCBTM A x))) := by
  intro x hblank
  constructor
  · intro ⟨π, cfg, hr, hacc⟩
    rcases (iso_path_forward A M iso x hblank π cfg hr) with ⟨π', cfg', hrc', hcfg'⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [hcfg']
    rw [iso.h_accept]
    exact hacc
  · intro ⟨π, cfg, hr, hacc⟩
    rcases (iso_path_backward A M iso x hblank π cfg hr) with ⟨π', cfg', hrc', hcfg'⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [iso.h_accept] at hacc
    rw [hcfg'] at hacc
    exact hacc

end PvsNP
