# Gyárfás's theorem for paths, in Lean 4

A machine-checked proof that **graphs with no induced path on t vertices are χ-bounded**
(Gyárfás, 1987). For every t there is a function f such that every finite graph G with no
induced Pₜ satisfies χ(G) ≤ f(ω(G)). Here χ is the chromatic number and ω is the clique number.

This is the case of paths in the **Gyárfás–Sumner conjecture**, which says the same for every
tree in place of the path. That conjecture is still open.

## The proof (Gyárfás's path argument)

Induction on the clique number. The neighbours of any vertex have smaller clique number, so they
can be coloured with c = f(k) colours. Suppose some vertex set S cannot be coloured with
t·c + 1 colours.

1. Take a connected piece of S that cannot, a vertex x in it, and a connected piece C of the rest
   that cannot be coloured with t·c colours. C contains a neighbour of x.
2. Grow an induced path x = p₀, p₁, … At each step, split C into the neighbours of the last path
   vertex, which need at most c colours, and the rest. Some connected piece Q of the rest needs c
   fewer colours than C. Walking inside C from Q towards the neighbours gives a neighbour u that
   is adjacent to Q. Then u extends the induced path, and Q replaces C.
3. After t − 1 steps the induced path has t vertices, a contradiction.

This gives f(0) = 0 and f(k + 1) = t·f(k) + 1. Gyárfás's own count gives (t − 1)^(ω − 1); the
formal statement only asks for some f.

## Lean

- `GyarfasPathLean/Basic.lean`: the whole proof, about 330 lines. It uses only the standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
- `Gyarfas.chiBounded_pathGraph`: the main theorem. It has exactly the type of
  `GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.path` in Google DeepMind's
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (`FormalConjectures/Wikipedia/GyarfasSumnerConjecture.lean`).

```bash
lake exe cache get
lake build
```

## Reference

A. Gyárfás, *Problems from the world surrounding perfect graphs*, Zastos. Mat. 19 (1987), 413–441.
