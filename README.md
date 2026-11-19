# A counterexample to the El-Zahar–Erdős conjecture

Manuscript and Lean 4 formalization of *A counterexample to the El-Zahar–Erdős conjecture*.
Chenghua Liu and Boning Meng (Renormalization Group) are the manuscript authors.
The Lean formalization was developed with OpenAI Codex.

From this directory, run:

```sh
lake exe cache get
lake build
lake env lean --stdin <<'LEAN'
import Erdos1111

#print axioms Erdos1111.counterexample_large_girth
#print axioms Erdos1111.erdos_1111_false
LEAN
```

The Lean toolchain and all dependency revisions are pinned in the project files.

On macOS, if the default developer directory points to an Xcode installation
that blocks Git, select the installed Command Line Tools before running the
commands above:

```sh
export DEVELOPER_DIR=/Library/Developer/CommandLineTools
```

## Main theorems

- `Erdos1111.counterexample_large_girth` gives, for every chromatic threshold
  and every prescribed girth at least four, a finite simple graph in which the
  smaller chromatic number of any anticomplete pair is at most six. It uses
  Mathlib's extended girth, which is infinite for forests.
- `Erdos1111.erdos_1111_false` refutes the general statement of
  [Erdős Problem #1111](https://www.erdosproblems.com/1111)
  ([JSP-000922](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000922)).
  It takes the clique threshold to be three and the two target chromatic
  numbers to be seven. The negation is universe-polymorphic.

The block construction uses integer parameters whose cubes give the paper's
edge-density parameters. Explicit finite probability bounds suffice to
choose the graph. The short-cycle estimate then allows deletion of at most
one block's worth of vertices while preserving the needed chromatic lower
bound.
