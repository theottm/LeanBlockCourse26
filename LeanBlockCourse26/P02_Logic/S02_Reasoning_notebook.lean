
/-
## Exercise Block B01: Graph of Implications

This exercise demonstrates how forward and backward reasoning can lead to very
different-looking proofs of the same fact. Consider the following graph of
implications:

A - f -> B <- g - C
|        |        |
h        i        j
|        |        |
v        v        v
D <- k - E - l -> F
^        ^        |
|        |        p
m        n        |
|        |        v
G <- q - H - r -> I

Find a path from `A` to `I` using different reasoning styles. Have at least
one purely forward arguing path and one purely backward arguing path.
-/

-- Term proof 1
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I :=
  p $ l $ i $ f a


-- Term proof 2
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I :=
  (p ∘ l ∘ i ∘ f) a

-- Backward tactic proof
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  apply p
  apply l
  apply i
  apply f
  exact a

-- With one apply
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  apply (p ∘ l ∘ i ∘ f) a

-- Forward tactic proof
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  have hb : B := f a
  have he : E := i hb
  have hf : F := l he
  have hi : I := p hf
  exact hi
