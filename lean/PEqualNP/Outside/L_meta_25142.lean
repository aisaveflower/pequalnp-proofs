import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25142

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.not, [12]⟩], 13⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem rep : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34630322097 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

theorem small : witness.size ≤ 9 := by decide

end PEqualNP.Outside.L_meta_25142

open PEqualNP.Outside.L_meta_25142 in
theorem PEqualNP.Outside.L_meta_25142 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322097 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, witnessFit, small, rep⟩
