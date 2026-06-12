# Lean graph theory tutorial

This is a small Lean 4 + mathlib project for learning graph theory formalization
with `SimpleGraph`.

## Requirements

`elan` manages the Lean toolchain.  This project pins Lean in `lean-toolchain`,
so normal commands are:

```bash
cd /home/hirata/lean/tutorial
lake build
```

For editing, open this directory in VS Code with the Lean 4 extension, then read:

```text
Tutorial/Basic.lean
```

## Contents

`Tutorial/Basic.lean` introduces:

* a finite vertex type;
* a hand-defined path graph `a -- b -- c`;
* adjacency proofs with `G.Adj`;
* neighbor sets with `G.neighborSet`;
* standard graphs such as `completeGraph` and `emptyGraph`;
* walks with `G.Walk`;
* finite degrees with `G.degree`;
* a reusable theorem over an arbitrary `SimpleGraph`.

The examples are intentionally small.  The next step is to replace `path3` with
one of your own graph definitions, then state your usual lemmas as Lean theorems.
