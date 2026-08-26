/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



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


/-!
# NTM2 层 padding（暂缓主线，保仓库绿的最小骨架）

padding 规格：1 → 0001，0 → 0000（每个二进制位扩展为 4 位）。
待回填：pad_get4 / pad_injective（getD-append 支撑引理）、NTM2 翻译机器。 -/

namespace PvsNP
open CBTM

-- ============================================================================
-- §1 padding：每个二进制位 → 4 个二进制位（1 → 0001，0 → 0000）
-- ============================================================================

/-- 单位的 padding：1 → [0,0,0,1]，0 → [0,0,0,0]。 -/
def padBit (b : Bool) : List Bool := [false, false, false, b]

/-- 串的 padding：逐位扩展为 4 位块。 -/
def pad (bs : List Bool) : List Bool := bs.flatMap padBit

@[simp] lemma padBit_false : padBit false = [false, false, false, false] := rfl
@[simp] lemma padBit_true : padBit true = [false, false, false, true] := rfl

@[simp] lemma pad_nil : pad [] = [] := rfl
@[simp] lemma pad_cons (b : Bool) (bs : List Bool) :
    pad (b :: bs) = [false, false, false, b] ++ pad bs := by
  simp [pad, padBit]

/-- padding 保持长度：4 倍。 -/
theorem pad_length (bs : List Bool) : (pad bs).length = 4 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      simp [pad, padBit, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega

end PvsNP
