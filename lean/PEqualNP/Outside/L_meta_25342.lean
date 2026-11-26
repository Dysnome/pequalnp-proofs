import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25342_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and,[1,5]⟩, ⟨.or,[2,3]⟩, ⟨.or,[2,4]⟩, ⟨.and,[3,8]⟩, ⟨.or,[5,9]⟩, ⟨.not,[10]⟩, ⟨.and,[7,11]⟩, ⟨.or,[6,12]⟩, ⟨.or,[0,13]⟩],14⟩
end PEqualNP.Outside.L_meta_25342_aux

open PEqualNP.Outside.L_meta_25342_aux PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_25342 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [FanInTwo,witness]
  · decide +kernel
