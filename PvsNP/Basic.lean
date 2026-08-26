/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mathlib

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
# PvsNP.Basic

底层定义：四元符号 F₄、素数平方根、方向、磁带、经典 DTM、语言占位。
-/

namespace PvsNP

open Set
open Finset

abbrev F4 : Type := Bool × Bool
-- ======================================================================
-- §1. F₄ 四元符号系统
-- ======================================================================


namespace F4

def zero : F4 := (false, false)
def one : F4 := (true, false)
def alpha : F4 := (false, true)
def beta : F4 := (true, true)

def re (s : F4) : Bool := s.1
def im (s : F4) : Bool := s.2
attribute [reducible] re im

@[simp] lemma im_zero : im zero = false := rfl
@[simp] lemma im_one : im one  = false := rfl
@[simp] lemma im_alpha : im alpha = true := rfl
@[simp] lemma im_beta : im beta  = true := rfl

-- ======================================================================
-- §3. Galois
-- ======================================================================
def galoisAction (s : F4) : F4 := (F4.re s, !F4.im s)


-- theorem galois_involution (s : F4) : galoisAction (galoisAction s) = s := by
--  ext <;> simp [galoisAction, F4.re, F4.im]

theorem galois_involution (s : F4) : galoisAction (galoisAction s) = s := by
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> rfl

@[simp] theorem F4_zero_re : F4.zero.re = false := rfl
@[simp] theorem F4_zero_im : F4.zero.im = false := rfl
@[simp] theorem F4_one_re : F4.one.re  = true  := rfl
@[simp] theorem F4_one_im : F4.one.im  = false := rfl
@[simp] theorem F4_alpha_re : F4.alpha.re = false := rfl
@[simp] theorem F4_alpha_im : F4.alpha.im = true  := rfl
@[simp] theorem F4_beta_re : F4.beta.re  = true  := rfl
@[simp] theorem F4_beta_im : F4.beta.im  = true  := rfl

end F4

-- ======================================================================
-- §4. 方向
-- ======================================================================

inductive Dir : Type
  | L : Dir
  | R : Dir
  | S : Dir
  deriving DecidableEq, Repr

namespace Dir

instance : Fintype Dir :=
  Fintype.ofList [Dir.L, Dir.R, Dir.S] <| by
    intro x
    cases x <;> decide

def toInt : Dir → ℤ
  | L => -1
  | R => 1
  | S => 0

theorem toInt_inj (d₁ d₂ : Dir) (h : toInt d₁ = toInt d₂) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp [toInt] at h <;> decide

end Dir

-- ======================================================================
-- §5. 素数平方根线性无关定理
--
-- 「互异素数的平方根在 ℚ 上线性无关」这一代数数论结果已形式化于
-- PvsNP.PrimeSqrtLinearIndep（定理 `primeSqrt_Q_linearIndependent`），此处不再
-- 以公理占位。
-- ======================================================================

-- ======================================================================
-- §6. 双向无限磁带
-- ======================================================================

structure Tape (α : Type) : Type where
  tape : ℤ → α
  default : α

namespace Tape

def read (t : Tape α) (i : ℤ) : α := t.tape i

def write (t : Tape α) (i : ℤ) (a : α) : Tape α := {
  tape := fun j => if j = i then a else t.tape j
  default := t.default
}

def blank (d : α) : Tape α := { tape := fun _ => d, default := d }

def realTape (t : Tape F4) : Tape Bool := {
  tape := fun i => F4.re (t.tape i)
  default := F4.re t.default
}

def imagTape (t : Tape F4) : Tape Bool := {
  tape := fun i => F4.im (t.tape i)
  default := F4.im t.default
}

def combineTapes (rt it : Tape Bool) : Tape F4 := {
  tape := fun i => match rt.tape i, it.tape i with
    | false, false => F4.zero
    | true, false  => F4.one
    | false, true  => F4.alpha
    | true, true   => F4.beta
  default := match rt.default, it.default with
    | false, false => F4.zero
    | true, false  => F4.one
    | false, true  => F4.alpha
    | true, true   => F4.beta
}

theorem realTape_read (t : Tape F4) (i : ℤ) : (realTape t).read i = F4.re (t.read i) :=
  rfl

theorem imagTape_read (t : Tape F4) (i : ℤ) : (imagTape t).read i = F4.im (t.read i) :=
  rfl

theorem combineTapes_real (rt : Tape Bool) (it : Tape Bool) (i : ℤ) :
    (realTape (combineTapes rt it)).read i = rt.read i := by
  unfold combineTapes realTape Tape.read
  cases h : rt.tape i
  · cases h' : it.tape i <;> simp [h, h']
  · cases h' : it.tape i <;> simp [h, h']

theorem combineTapes_imag (rt : Tape Bool) (it : Tape Bool) (i : ℤ) :
    (imagTape (combineTapes rt it)).read i = it.read i := by
  unfold combineTapes imagTape Tape.read
  cases h : rt.tape i
  · cases h' : it.tape i <;> simp [h, h']
  · cases h' : it.tape i <;> simp [h, h']

end Tape

-- ======================================================================
-- §7. 经典 DTM
-- ======================================================================

structure ClassicDTMTransitionResult where
  nextState : ℕ
  writeSym  : Bool
  move      : Dir



structure ClassicDTM where
  states : Finset ℕ
  startState : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  alphabet : Finset Bool := [false, true].toFinset
  transition : ℕ × Bool → ClassicDTMTransitionResult
  blankSym : Bool := false
  h_start_in_states : startState ∈ states
  h_accept_subset : acceptStates ⊆ states
  h_reject_subset : rejectStates ⊆ states
  h_accept_reject_disjoint : acceptStates ∩ rejectStates = ∅
  isValid : ∀ q s, (transition (q, s)).nextState ∈ states
  h_alphabet_all : alphabet = {false, true}


-- ===========================================================================
-- 配置（状态 + 纸带 + 读写头位置）
-- ===========================================================================

structure DTMConfig (M : ClassicDTM) where
  state : ℕ
  tape  : Tape Bool
  headPos : ℤ


-- ======================================================================
-- §8. 分支触发与对偶翻转
-- ======================================================================



def dualFlip : F4 → F4 := F4.galoisAction

theorem dualFlip_involutive (s : F4) : dualFlip (dualFlip s) = s := F4.galois_involution s

-- ======================================================================
-- 维度引理（修正）
-- ======================================================================

/-- 有限维向量空间的维数上界：若 V 的基大小 ≤ n，则任何线性无关集合大小 ≤ n。 -/
theorem dimension_upperBound (V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (h_dim : Module.rank K V ≤ (n : Cardinal)) :
    ∀ (s : Finset V), LinearIndependent K (fun v : s => (v : V)) → s.card ≤ n := by
  intro s h_indep
  have h_card_le_rank : Cardinal.mk (s : Set V) ≤ Module.rank K V := by
    simpa using h_indep.cardinal_le_rank
  have h_card_le_n : Cardinal.mk (s : Set V) ≤ (n : Cardinal) :=
    le_trans h_card_le_rank h_dim
  have h_mk_eq : Cardinal.mk (s : Set V) = (s.card : Cardinal) := by simp
  rw [h_mk_eq] at h_card_le_n
  exact_mod_cast h_card_le_n

-- ===========================================================================
-- §9. 二分支 NTM（在 Bool 上工作）
-- ===========================================================================


-- 使用 ℕ 作为状态类型，无需额外缩写
-- 如果希望保留 State 名称，可以改为 abbrev State := ℕ，但需注意与结构体同名的影响

structure NTM2 where
  states : Finset ℕ
  startState : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  alphabet : Finset Bool
  /-- 转移依赖磁头位置：(q, 读符号, 磁头位置) → 结果集（写符号、方向）。
      分支是存在性定义：转移关系先行，vb[i] 由此派生。 -/
  transition : ℕ × Bool × ℤ → Finset (ℕ × Bool × Dir)
  blankSym : Bool
  h_blank_in_alphabet : blankSym ∈ alphabet
  h_start_in_states : startState ∈ states
  h_accept_subset : acceptStates ⊆ states
  h_reject_subset : rejectStates ⊆ states
  h_accept_reject_disjoint : acceptStates ∩ rejectStates = ∅
  /-- 分支存在性：每步 1 或 2 个结果（card = vb[i] + 1，vb 由此派生）。 -/
  h_branch_axiom : ∀ q b i, b ∈ alphabet → (transition (q, b, i)).card = 1 ∨ (transition (q, b, i)).card = 2
  /-- 位置分支一致性：同一磁头位置的分支数不依赖状态与读符号（vb[i] 良定义）。 -/
  h_card_pos_indep : ∀ q b q' b' i, b ∈ alphabet → b' ∈ alphabet →
    (transition (q, b, i)).card = (transition (q', b', i)).card
  h_accept_singleton : acceptStates.card = 1
  h_reject_singleton : rejectStates.card = 1
  h_alphabet_all : alphabet = {false, true}
  h_transition_state_mem : ∀ q b i, b ∈ alphabet → ∀ r ∈ (transition (q, b, i)), r.1 ∈ states

/-- 派生虚拟虚部带：vb[i] = 位置 i 的分支标志（card = 2 ⟺ 分叉）。
    先有转移关系，再有 vb；vb 与读符号（实部）完全无关（h_card_pos_indep）。 -/
def NTM2.vbAt (A : NTM2) (i : ℤ) : Bool :=
  (A.transition (A.startState, A.blankSym, i)).card = 2

/-- 位置 i 处是否分叉（vb = 1）。 -/
def IsVb (A : NTM2) (i : ℤ) : Prop := NTM2.vbAt A i = true


structure NTM2TransitionStep where
  fromState : ℕ
  readSym : Bool
  pos : ℤ
  result : ℕ × Bool × Dir

abbrev NTM2ComputationPath := List NTM2TransitionStep

def NTM2ComputationPath.endState (A : NTM2) (π : NTM2ComputationPath) : ℕ :=
  π.foldl (fun _ step => step.result.1) A.startState

/-- foldl 在 map 下的交换：累加函数忽略累加器、只取元素「结果状态」。 -/
lemma foldl_map_endState {α β : Type} (f : α → β) (g : β → ℕ) (h : α → ℕ)
    (init : ℕ) (l : List α) (hcompat : ∀ a, g (f a) = h a) :
    (l.map f).foldl (fun _ b => g b) init = l.foldl (fun _ a => h a) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih =>
    simp [List.foldl, hcompat a, ih]

inductive ReachablePathNTM2 (A : NTM2) : List Bool → NTM2ComputationPath → Prop
  | nil : ReachablePathNTM2 A [] []
  | cons : ∀ (xs : List Bool) (a : Bool) (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep),
      ReachablePathNTM2 A xs π₀ →
      step.fromState = NTM2ComputationPath.endState A π₀ →
      step.readSym = a →
      step.result ∈ A.transition (NTM2ComputationPath.endState A π₀, a, step.pos) →
      ReachablePathNTM2 A (xs ++ [a]) (π₀ ++ [step])

/-- NTM2 接受一个 Bool 串。 -/
def NTM2.accepts (A : NTM2) (x : List Bool) : Prop :=
  ∃ π, ReachablePathNTM2 A x π ∧ NTM2ComputationPath.endState A π ∈ A.acceptStates

-- ============================================================================
-- NTM2 磁带语义（与 CBTM/DTM 对齐：带头 + 初始配置 + 步进）
-- ============================================================================

/-- NTM2 的格局：状态、复合磁带（tape × vb，每格 = 实部 × 虚部，与 CBTM 对齐）、磁头位置。
    输入是 Bool 串（与虚部无关）；虚部 = vb 带（由转移关系派生的机器内部信息，
    只与输入的模式对应）。 -/
structure NTM2Config (A : NTM2) (input : List Bool) where
  state : ℕ
  tape : ℤ → F4
  headPos : ℤ

/-- NTM2 初始磁带：输入（Bool 串）写在 [0, n)（实部 = 输入，虚部 = vb 带），
    空白区 = (blankSym, vbAt 0) 常数（与 CBTM 的常数空白符号对齐）。 -/
def NTM2InitialTape (A : NTM2) (input : List Bool) : ℤ → F4 :=
  fun i => if h : 0 ≤ i ∧ i.toNat < input.length then
      (input.get ⟨i.toNat, h.2⟩, A.vbAt i)
    else (A.blankSym, A.vbAt 0)

/-- NTM2 初始配置。 -/
def NTM2InitialConfig (A : NTM2) (input : List Bool) : NTM2Config A input :=
  { state := A.startState, tape := NTM2InitialTape A input, headPos := 0 }

/-- NTM2 一步格局：写 result.2.1（实部）到带头位置（虚部保持 vb 带），移动带头，更新状态。 -/
def NTM2StepConfig {A : NTM2} {input : List Bool} (cfg : NTM2Config A input)
    (r : ℕ × Bool × Dir) : NTM2Config A input :=
  { state := r.1,
    tape := fun i => if i = cfg.headPos then (r.2.1, (cfg.tape cfg.headPos).2) else cfg.tape i,
    headPos := cfg.headPos + r.2.2.toInt }

/-- NTM2 磁带语义的可达路径：每步读 headPos 处的格子（实部），写 r.2.1，移动 r.2.2。
    转移依赖磁头位置；虚部（分支性）由派生带 vb 在磁头位置的值决定。 -/
inductive TapeReachablePathNTM2 (A : NTM2) (input : List Bool) :
    NTM2ComputationPath → NTM2Config A input → Prop
  | nil : TapeReachablePathNTM2 A input [] (NTM2InitialConfig A input)
  | cons : ∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (cfg : NTM2Config A input),
      TapeReachablePathNTM2 A input π₀ cfg →
      step.fromState = cfg.state →
      step.readSym = (cfg.tape cfg.headPos).1 →
      step.pos = cfg.headPos →
      step.result ∈ A.transition (cfg.state, (cfg.tape cfg.headPos).1, cfg.headPos) →
      TapeReachablePathNTM2 A input (π₀ ++ [step]) (NTM2StepConfig cfg step.result)

/-- NTM2 磁带语义的接受：存在一条磁带可达路径，其末端状态在接受态。 -/
def NTM2.acceptsTape (A : NTM2) (x : List Bool) : Prop :=
  ∃ π, ∃ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg ∧ cfg.state ∈ A.acceptStates

/-- 规范 NTM2：任意可达路径的磁头只在输入区内活动（每步的步前与步后位置均在 [0, len)），
    且每个输入格至多被读一次（「只能读一遍输入」）。
    vb 带只在输入区内有意义；空白区 vbAt 的取值不影响规范机器的行为，
    因此空白一致性（BlankVbConsistent）不再是同构桥的前提。 -/
def NTM2.Canonical (A : NTM2) : Prop :=
  ∀ (x : List Bool) (π : NTM2ComputationPath) (cfg : NTM2Config A x),
    TapeReachablePathNTM2 A x π cfg →
      (∀ step ∈ π,
        0 ≤ step.pos ∧ step.pos < x.length ∧
        0 ≤ step.pos + step.result.2.2.toInt ∧
        step.pos + step.result.2.2.toInt < x.length) ∧
      (π.map (fun step => step.pos)).Nodup


end PvsNP
