import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19092_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or,[3,7]⟩, ⟨.not,[8]⟩], 9⟩
end PEqualNP.Outside.L_meta_19092_aux

open PEqualNP.Outside.L_meta_19092_aux PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19092 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1911 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [FanInTwo,witness]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
