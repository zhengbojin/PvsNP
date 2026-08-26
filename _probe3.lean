import PvsNP.CBTM
import PvsNP.IVM

open PvsNP

example (A : NTM2) : ∃ M : CBTM, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M) := by
  rcases exists_CBTM_iso_NTM2 A with ⟨M, ⟨iso⟩⟩
  refine ⟨M, ?_, ⟨iso⟩⟩
  rfl

example (A : NTM2) : True := by
  rcases exists_CBTM_iso_NTM2 A with ⟨M, ⟨iso⟩⟩
  have hM : M = NTM2.toCBTM A := rfl
  trivial
