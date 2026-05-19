import «upper_bound».«main»
import «finite_check».«main»
import Definitions
theorem root : {n : ℕ | n = digitFactorialSum n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    by_cases hn : 10 ^ 7 ≤ n
    · exact absurd h (ne_of_gt (upper_bound n hn))
    · push_neg at hn
      exact (finite_check n hn).mp h
  · intro h
    have hlt : n < 10 ^ 7 := by
      rcases h with rfl | rfl | rfl | rfl <;> norm_num
    exact (finite_check n hlt).mpr h
