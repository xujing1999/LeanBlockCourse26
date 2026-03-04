---
title: "Measuring proof length with #golf"
parent: Addendum
nav_order: 9996
---

# Measuring proof length with `#golf`
{: .no_toc }

*2026-03-04 · P02/S03 Exercise Block B02*

---

In the exercise blocks we asked you to minimize the number of non-whitespace characters in your proof. The course repo contains a custom `#golf` command that measures this automatically.

## Using `#golf` in your own project

1. Copy [`LeanBlockCourse26/CodeGolf.lean`](https://github.com/FordUniver/LeanBlockCourse26/blob/main/LeanBlockCourse26/CodeGolf.lean) into the corresponding location in your project (i.e., `YourProject/CodeGolf.lean`)
2. Add `import YourProject.CodeGolf` to any file where you want to use it
3. Wrap your proof with `#golf`:

```lean
#golf example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨p, q⟩
  exact ⟨q, p⟩
-- Golf: 20 chars
```

## Scoring rules

- Whitespace is free (indentation and newlines don't count)
- `;` (tactic separator) is free — it is equivalent to a newline, so formatting choices don't affect your score
- `<;>` (the tactic combinator that applies to all remaining goals) **does** count

## How it works

`#golf` is a custom Lean 4 elaboration command. It wraps any declaration (`example`, `theorem`, `def`), elaborates it normally, then extracts the proof body from the syntax tree using source positions. This avoids the need to manually paste your proof into a string.
