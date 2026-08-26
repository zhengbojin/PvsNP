/- A2 桥(A2 公理消去的核心定理):位置模型 + 复合磁带 + Bool 输入版。
   输入 = Bool 串(与经典 P/NP 语言相同);虚部 = 机器内部 vb 带(由转移派生,
   只与输入的模式对应);格局 = (state, tape × vb, headPos) 与 CBTM 逐格相同。
   v3:空白一致性(BlankVbConsistent)前提改为规范 NTM2(NTM2.Canonical):
   任意可达路径的磁头只在输入区内活动 + 每格至多读一次。
   因此空白区 vbAt 的取值不再影响桥;前提是纯机器性质,与输入无关。 -/
import PvsNP.Basic
import PvsNP.CBTM
import PvsNP.IVM

namespace PvsNP

open CBTM
open IVM

-- ======================================================================
-- 结构同构保持接受语言（A2 公理消去的核心定理；规范 NTM2 版）
-- ======================================================================

/-- 空白一致性：输入区之外 vb 带为常数（与 CBTM 常数空白符号对齐，含负位置）。
    v3 起不再作为桥的前提（规范 NTM2 不读空白区）；保留定义供文档与旧语句引用。 -/
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

/-- 非负整数：ℤ 界 < ↑n 蕴含 toNat 界 < n。 -/
lemma int_toNat_lt_of_lt (i : ℤ) (n : ℕ) (h0 : 0 ≤ i) (hlt : i < (n : ℤ)) :
    i.toNat < n := by
  exact (Int.toNat_lt (n := n) h0).mpr hlt

/-- 空路径的可达配置唯一：nil 路径的终配置 = 初始配置。 -/
lemma reach_cfg_of_len_zero (A : NTM2) (x : List Bool) :
    ∀ (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg → π = [] → cfg = NTM2InitialConfig A x := by
  intro π cfg h
  induction h with
  | nil =>
      intro hπ
      rfl
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro hπ
      exfalso
      have hlen : (π₀ ++ [step]).length ≠ 0 := by simp
      exact hlen (by rw [hπ]; rfl)

lemma reach_nil_cfg (A : NTM2) (x : List Bool) (cfg : NTM2Config A x) :
    TapeReachablePathNTM2 A x [] cfg → cfg = NTM2InitialConfig A x := by
  intro h
  exact reach_cfg_of_len_zero A x [] cfg h rfl

/-- 可达路径上输入区磁带虚部恒 = vb 带（虚部永不改变：初始带定义 + 步进写回保持）。
    无任何前提 —— 输入区虚部由初始磁带定义直接给出。 -/
lemma ntm2Path_tape_im_vb_input (A : NTM2) (x : List Bool) :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∀ i, 0 ≤ i → i < (x.length : ℤ) → (cfg.tape i).2 = A.vbAt i := by
  intro π cfg hr
  induction hr with
  | nil =>
      intro i hi0 hilt
      unfold NTM2InitialConfig NTM2InitialTape
      simp [hi0, int_toNat_lt_of_lt i x.length hi0 hilt]
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro i hi0 hilt
      unfold NTM2StepConfig
      by_cases h : i = cfg₀.headPos
      · simp [h]
        exact ih cfg₀.headPos (by rw [← h]; exact hi0) (by rw [← h]; exact hilt)
      · simp [h]
        exact ih i hi0 hilt

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

/-- 可达路径的对应（NTM2 → CBTM，路径与配置逐步保持；规范 NTM2 时）。
    每步的读位置由规范（步前在输入区）保证在输入区内，虚部对齐无需空白一致性。 -/
lemma iso_path_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List Bool)
    (hcan : NTM2.Canonical A) :
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
      have hstep_mem : step ∈ π₀ ++ [step] := by simp
      have hcan_full := hcan x (π₀ ++ [step]) (NTM2StepConfig cfg₀ step.result)
        (TapeReachablePathNTM2.cons π₀ step cfg₀ hrc hfrom hread hpos htrans)
      have hpos0 : 0 ≤ step.pos := (hcan_full.1 step hstep_mem).1
      have hposlt : step.pos < (x.length : ℤ) := (hcan_full.1 step hstep_mem).2.1
      have hvb : A.vbAt step.pos = (cfg₀.tape cfg₀.headPos).2 := by
        rw [hpos]
        symm
        exact ntm2Path_tape_im_vb_input A x π₀ cfg₀ hrc cfg₀.headPos
          (by rw [← hpos]; exact hpos0) (by rw [← hpos]; exact hposlt)
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

/-- 可达路径的对应（CBTM → NTM2；规范 NTM2 时）。
    归纳加强：镜像路径与 CBTM 路径同长，且终配置在输入区内（或路径为空）且非负。 -/
lemma iso_path_backward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List Bool)
    (hcan : NTM2.Canonical A) :
    ∀ π, ∀ cfg : CBTMConfig M (ntm2InputToCBTM A x),
      TapeReachablePath M (ntm2InputToCBTM A x) π cfg →
      ∃ π' : NTM2ComputationPath, ∃ cfg' : NTM2Config A x,
        TapeReachablePathNTM2 A x π' cfg' ∧ cfg = ntm2CfgToCBTM A M iso cfg' ∧
        (cfg'.headPos < (x.length : ℤ) ∨ π'.length = 0) ∧ 0 ≤ cfg'.headPos := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], NTM2InitialConfig A x, TapeReachablePathNTM2.nil, ?_, ?_, ?_⟩
      · exact (iso_initial_corresp A M iso x).symm
      · exact Or.inr rfl
      · dsimp [NTM2InitialConfig]
        omega
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg', hlt, hnonneg⟩
      let s₀ : F4 := cfg₀.tapeAt cfg₀.headPos
      have hhead_eq : cfg₀.headPos = cfg'.headPos := by
        rw [hcfg']
        rfl
      have him_s0 : F4.im s₀ = A.vbAt cfg₀.headPos := by
        dsimp [s₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        by_cases hπ' : π'.length = 0
        · have hπ'eq : π' = [] := by
            cases π' with
            | nil => rfl
            | cons a rest => simp at hπ'
          subst hπ'eq
          have hcfg'init : cfg' = NTM2InitialConfig A x := reach_nil_cfg A x cfg' hrc'
          rw [hcfg'init]
          unfold NTM2InitialConfig NTM2InitialTape
          by_cases hlen0 : x.length = 0
          · simp [hlen0]
          · have hlenpos : 0 < x.length := Nat.pos_of_ne_zero hlen0
            simp [hlenpos]
        · cases hlt with
          | inl hlt' =>
              exact ntm2Path_tape_im_vb_input A x π' cfg' hrc' cfg'.headPos hnonneg hlt'
          | inr hlen0 => exact False.elim (hπ' hlen0)
      have himage : step.result ∈ (A.transition (cfg₀.state, s₀.1, cfg₀.headPos)).image
          (fun r : ℕ × Bool × Dir =>
            CBTMTransResult.mk r.1 (r.2.1, A.vbAt cfg₀.headPos) r.2.2) := by
        rw [← iso.h_transition cfg₀.state s₀ cfg₀.headPos him_s0]
        rw [iso.h_φ_id s₀]
        exact htrans
      rcases Finset.mem_image.mp himage with ⟨r₀, hr₀, hres⟩
      let step₀ : NTM2TransitionStep :=
        { fromState := cfg₀.state, readSym := s₀.1, pos := cfg₀.headPos, result := r₀ }
      have hfrom₀ : step₀.fromState = cfg'.state := by
        dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      have hread₀ : step₀.readSym = (cfg'.tape cfg'.headPos).1 := by
        dsimp [step₀, s₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        rfl
      have hpos₀ : step₀.pos = cfg'.headPos := by
        dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      have htrans₀ : step₀.result ∈ A.transition (cfg'.state, (cfg'.tape cfg'.headPos).1, cfg'.headPos) := by
        dsimp [step₀, s₀]
        have hr₀' : r₀ ∈ A.transition (cfg'.state, (cfg'.tape cfg'.headPos).1, cfg'.headPos) := by
          dsimp [s₀] at hr₀
          rw [hcfg'] at hr₀
          dsimp [ntm2CfgToCBTM] at hr₀
          exact hr₀
        exact hr₀'
      have hcan_new := hcan x (π' ++ [step₀]) (NTM2StepConfig cfg' r₀)
        (TapeReachablePathNTM2.cons π' step₀ cfg' hrc' hfrom₀ hread₀ hpos₀ htrans₀)
      have hstep₀_mem : step₀ ∈ π' ++ [step₀] := by simp
      have hstep0_after : 0 ≤ step₀.pos + step₀.result.2.2.toInt :=
        (hcan_new.1 step₀ hstep₀_mem).2.2.1
      have hstep0_after_lt : step₀.pos + step₀.result.2.2.toInt < (x.length : ℤ) :=
        (hcan_new.1 step₀ hstep₀_mem).2.2.2
      have hcfg''head : (NTM2StepConfig cfg' r₀).headPos = step₀.pos + step₀.result.2.2.toInt := by
        dsimp [NTM2StepConfig, step₀]
        rw [hhead_eq]
      have hnew_lt : (NTM2StepConfig cfg' r₀).headPos < (x.length : ℤ) := by
        rw [hcfg''head]
        exact hstep0_after_lt
      have hnew_ge : 0 ≤ (NTM2StepConfig cfg' r₀).headPos := by
        rw [hcfg''head]
        exact hstep0_after
      refine ⟨π' ++ [step₀], NTM2StepConfig cfg' r₀,
        TapeReachablePathNTM2.cons π' step₀ cfg' hrc' hfrom₀ hread₀ hpos₀ htrans₀, ?_, ?_, ?_⟩
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
      · exact Or.inl hnew_lt
      · exact hnew_ge

/-- 结构同构保持接受语言（NTM2 磁带语义 ↔ CBTM 磁带语义；规范 NTM2 时）。
    输入 = Bool 串，CBTM 输入 = 复合串（实部 + vb 带）。
    前提是纯机器性质（与输入无关），消去同构桥公理的关键定理。 -/
theorem StructIso_preserves_accepts (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (hcan : NTM2.Canonical A) :
    ∀ x : List Bool, (A.acceptsTape x ↔ M.tapeAccepts (ntm2InputToCBTM A x)) := by
  intro x
  constructor
  · intro ⟨π, cfg, hr, hacc⟩
    rcases (iso_path_forward A M iso x hcan π cfg hr) with ⟨π', cfg', hrc', hcfg'⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [hcfg']
    rw [iso.h_accept]
    exact hacc
  · intro ⟨π, cfg, hr, hacc⟩
    rcases (iso_path_backward A M iso x hcan π cfg hr) with ⟨π', cfg', hrc', hcfg', _hlt, _hnonneg⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [iso.h_accept] at hacc
    rw [hcfg'] at hacc
    exact hacc

end PvsNP
