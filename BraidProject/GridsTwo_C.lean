import BraidProject.Grids_C
import BraidProject.GridsTwo'

open FreeMonoid

namespace Braid

namespace GridData

namespace DeterminativeSpine

theorem one_one : GridData a b c d → a = 1 → b = 1 → (c = 1 ∧ d = 1) := by
  intro h one two
  have H := to_grid h
  rw [one, two] at H
  apply Grid.DeterminativeSpine.one_one H

--theorem one_one (h1 : GridData 1 1 c d) : c = 1 ∧ d = 1 := one_one_helper h1 rfl rfl

theorem one_generator (h : GridData a b c d) : ∀ {i}, a = 1 → b = FreeMonoid.of i → c = of i ∧ d = 1 := by
  intro i ha hb
  have H := to_grid h
  rw [ha, hb] at H
  apply Grid.DeterminativeSpine.one_generator H

theorem generator_one (h : GridData a b c d) : ∀ {i}, a = FreeMonoid.of i → b = 1 → c = 1 ∧ d = of i := by
  intro i ha hb
  have H := to_grid h
  rw [ha, hb] at H
  apply Grid.DeterminativeSpine.generator_one H

theorem generator_generator_same : GridData a b c d → ∀ {i}, a = FreeMonoid.of i → b = FreeMonoid.of i → c = 1 ∧ d = 1 := by
  intro h
  have H := to_grid h
  intro i ha hb
  rw [ha, hb] at H
  apply Grid.DeterminativeSpine.generator_generator_same H

theorem one_word : ∀ {a b c}, GridData a b c d → a = 1 → c = b ∧ d = 1 := by
  intro a b c h ha
  have H := to_grid h
  rw [ha] at H
  apply Grid.DeterminativeSpine.one_word H

theorem word_one : ∀ {a b c}, GridData a b c d → b = 1 → c = 1 ∧ d = a := by
  intro a b c h hb
  have H := to_grid h
  rw [hb] at H
  apply Grid.DeterminativeSpine.word_one H

theorem word_word_same (h : GridData a b c d) : a = b → c = 1 ∧ d = 1 := by
  intro hab
  have H := to_grid h
  rw [hab] at H
  exact Grid.DeterminativeSpine.word_word_same H

theorem generator_generator_close : GridData a b c d → ∀ {i j}, a = FreeMonoid.of i → b = FreeMonoid.of j → (Nat.dist i j = 1) →
  c = FreeMonoid.of j * FreeMonoid.of i ∧ d = FreeMonoid.of i * FreeMonoid.of j := by
  intro h i j ha hb hd
  have H := to_grid h
  rw [ha, hb] at H
  apply Grid.DeterminativeSpine.generator_generator_close H hd

theorem generator_generator_apart {a b c d : FreeMonoid ℕ} (h : GridData a b c d) : ∀ {i j}, (i.dist j ≥ 2) → a = of i → b = of j →
    (c = of j ∧ d = of i):= by
  intro i j hij ha hb
  have H := to_grid h
  rw [ha, hb] at H
  apply Grid.DeterminativeSpine.generator_generator_apart H hij

theorem braid_eq_of_GridData_empty_sink : GridData a b 1 1 → PresentedMonoid.rel braid_monoid_rels_inf a b := by
  intro h
  apply PresentedMonoid.exact
  rw [← mul_one a, ← mul_one b]
  exact braid_eq h

end DeterminativeSpine
end GridData
end Braid
